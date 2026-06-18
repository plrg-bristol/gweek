//! # The search schedulers
//!
//! Owns the **search**: creates the runtime arena, builds the initial machine, imports the
//! top-level function values, and runs one of four scheduling strategies that drive the
//! machine's `run_to_branch` over the search tree, recording solutions.
//!
//! Four entry points share the machinery — [`eval`] (CLI, prints solutions),
//! [`eval_collect`] (WASM batch, returns one `String`), [`eval_streaming`] (WASM, callback per
//! solution), and [`run`] (tests, returns a count) — all dispatching on [`Strategy`]:
//!
//! - **BFS** — level frontier; complete and fair, but the frontier (and arena) can blow up.
//!   Default.
//! - **DFS** — a stack; fast and lean, incomplete on infinite branches.
//! - **IDDFS** — repeated depth-limited DFS, doubling the limit; counts each solution in exactly
//!   one round via a frontier window, so no cross-round dedup is needed.
//! - **Fair** — round-robin over work-stacks, each given a step quota; complete with DFS-like
//!   speed, the recommended general default.
//!
//! Deadline polling rides on a shared `Clock` (defined in `step`) that reads the wall clock only
//! once every 1024 ticks. `record_solution` closes the answer value to a ground term; a residual
//! free logic variable is reported as a `_<id>` placeholder rather than dropped, and a cyclic
//! term renders as an error rather than overflowing.

use std::collections::VecDeque;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use bumpalo::Bump;

use super::config::Config;
use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::SuspEnv;
use super::step::{Clock, Machine, RunResult, Stack};
use super::vclosure::VClosure;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    Bfs,
    Dfs,
    Iddfs,
    Fair,
}

/// Absolute deadline for a run, computed once from the configured timeout.
fn deadline_from(cfg: &Config) -> Instant {
    Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs)
}

/// Run with output, using config for strategy/timeout. Creates its own runtime arena.
pub fn eval<'a>(cfg: &Config, comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>]) {
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = deadline_from(cfg);
    let mut on_solution = |s: &str| println!("> {}", s);
    let (solns, timed_out) = run_internal(cfg, &arena, comp, env, deadline, &mut on_solution);
    if timed_out {
        println!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns);
    } else {
        println!(">>> {} solutions", solns);
    }
}

/// Collect all solutions into a String (for WASM).
pub fn eval_collect<'a>(cfg: &Config, comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>]) -> String {
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = deadline_from(cfg);
    let mut solutions = Vec::new();
    let (solns, timed_out) = {
        let mut on_solution = |s: &str| solutions.push(format!("> {}", s));
        run_internal(cfg, &arena, comp, env, deadline, &mut on_solution)
    };
    if timed_out {
        solutions.push(format!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns));
    } else {
        solutions.push(format!(">>> {} solutions", solns));
    }
    solutions.join("\n")
}

/// Stream solutions one at a time via a callback, then return the summary line.
pub fn eval_streaming<'a>(
    cfg: &Config,
    comp: &'a MComputation<'a>,
    vals: &[&'a MValue<'a>],
    mut on_solution: impl FnMut(&str),
) -> String {
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = deadline_from(cfg);
    let mut cb = |s: &str| on_solution(&format!("> {}", s));
    let (solns, timed_out) = run_internal(cfg, &arena, comp, env, deadline, &mut cb);
    if timed_out {
        format!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns)
    } else {
        format!(">>> {} solutions", solns)
    }
}

/// Run without output (for tests). Creates its own runtime arena.
pub fn run<'a>(cfg: &Config, comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>], print: bool) -> usize {
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = deadline_from(cfg);
    if print {
        let mut on_solution = |s: &str| println!("> {}", s);
        run_internal(cfg, &arena, comp, env, deadline, &mut on_solution).0
    } else {
        let mut on_solution = |_: &str| {};
        run_internal(cfg, &arena, comp, env, deadline, &mut on_solution).0
    }
}

/// Build an Env from the compile-time list of top-level values.
fn import_env<'a>(arena: &'a Bump, vals: &[&'a MValue<'a>]) -> Env<'a> {
    let mut env = Env::empty(arena);
    for val in vals {
        env = env.extend_val(arena, val, env);
    }
    env
}

fn run_internal<'a>(
    cfg: &Config,
    arena: &'a Bump,
    comp: &'a MComputation<'a>,
    env: Env<'a>,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    match cfg.strategy {
        Strategy::Bfs => eval_bfs(cfg, arena, comp, env, deadline, on_solution),
        Strategy::Dfs => eval_dfs(cfg, arena, comp, env, deadline, on_solution),
        Strategy::Iddfs => eval_iddfs(cfg, arena, comp, env, deadline, on_solution),
        Strategy::Fair => eval_fair(cfg, arena, comp, env, deadline, on_solution),
    }
}

fn fresh_machine<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>) -> Machine<'a> {
    Machine {
        arena,
        cclos: (comp, env),
        stack: Stack::empty(arena),
        lenv: LogicEnv::new(),
        senv: SuspEnv::new(),
        done: false,
    }
}

/// Record a solution; returns true if we should stop (--first mode).
fn record_solution(cfg: &Config, m: &Machine, solns: &mut usize, on_solution: &mut dyn FnMut(&str)) -> bool {
    if let MComputation::Return(v) = m.cclos.0 {
        on_solution(&output(v, m.cclos.1, &m.lenv, &m.senv));
        *solns += 1;
        if cfg.first_only {
            return true;
        }
    }
    false
}

fn eval_bfs<'a>(cfg: &Config, arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut machines = vec![fresh_machine(arena, comp, env)];
    let mut next = Vec::new();
    let mut solns = 0;
    let mut clock = Clock::new(deadline);
    while !machines.is_empty() {
        for m in machines.drain(..) {
            if clock.expired() {
                return (solns, true);
            }
            let results = match m.run_to_branch(cfg, deadline) {
                RunResult::Yield(ms) => ms,
                RunResult::TimedOut => return (solns, true),
            };
            for m in results {
                if m.done {
                    if record_solution(cfg, &m, &mut solns, on_solution) {
                        return (solns, false);
                    }
                } else {
                    next.push(m);
                }
            }
        }
        std::mem::swap(&mut machines, &mut next);
    }
    (solns, false)
}

fn eval_dfs<'a>(cfg: &Config, arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut stack = vec![fresh_machine(arena, comp, env)];
    let mut solns = 0;
    let mut clock = Clock::new(deadline);
    while let Some(m) = stack.pop() {
        if clock.expired() {
            return (solns, true);
        }
        let results = match m.run_to_branch(cfg, deadline) {
            RunResult::Yield(ms) => ms,
            RunResult::TimedOut => return (solns, true),
        };
        for m in results.into_iter().rev() {
            if m.done {
                if record_solution(cfg, &m, &mut solns, on_solution) {
                    return (solns, false);
                }
            } else {
                stack.push(m);
            }
        }
    }
    (solns, false)
}

fn eval_iddfs<'a>(cfg: &Config, arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut solns = 0;
    let mut depth_limit: usize = 1;
    let mut clock = Clock::new(deadline);
    loop {
        let mut stack = vec![(fresh_machine(arena, comp, env), 0)];
        let mut cutoff = false;
        while let Some((m, depth)) = stack.pop() {
            if clock.expired() {
                return (solns, true);
            }
            if depth >= depth_limit {
                cutoff = true;
                continue;
            }
            let results = match m.run_to_branch(cfg, deadline) {
                RunResult::Yield(ms) => ms,
                RunResult::TimedOut => return (solns, true),
            };
            let is_branch = results.len() > 1;
            for m in results.into_iter().rev() {
                let next_depth = if is_branch { depth + 1 } else { depth };
                if m.done {
                    // Count a solution only in the round that first reaches its
                    // depth (the frontier (depth_limit/2, depth_limit]): every
                    // round with a larger limit re-derives it, but the window
                    // selects exactly one, so distinct derivations that happen
                    // to print identically are no longer collapsed.
                    if next_depth >= depth_limit / 2
                        && next_depth < depth_limit
                        && record_solution(cfg, &m, &mut solns, on_solution)
                    {
                        return (solns, false);
                    }
                } else {
                    stack.push((m, next_depth));
                }
            }
        }
        if !cutoff {
            break;
        }
        depth_limit *= 2;
    }
    (solns, false)
}

fn eval_fair<'a>(cfg: &Config, arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    const QUOTA: usize = 10000;
    const MAX_THREADS: usize = 10000;
    let mut queue: VecDeque<Vec<Machine<'a>>> = VecDeque::new();
    queue.push_back(vec![fresh_machine(arena, comp, env)]);
    let mut solns = 0;
    let mut clock = Clock::new(deadline);
    while let Some(mut local) = queue.pop_front() {
        let mut steps = 0;
        while let Some(m) = local.pop() {
            if clock.expired() {
                return (solns, true);
            }
            if steps >= QUOTA {
                local.push(m);
                break;
            }
            steps += 1;
            let results = match m.run_to_branch(cfg, deadline) {
                RunResult::Yield(ms) => ms,
                RunResult::TimedOut => return (solns, true),
            };
            if results.len() > 1 && queue.len() < MAX_THREADS {
                // Spread branch alternatives across the queue for fairness.
                // First alternative continues in the current thread (DFS);
                // remaining alternatives become new threads.
                let mut first = true;
                for m in results {
                    if m.done {
                        if record_solution(cfg, &m, &mut solns, on_solution) {
                            return (solns, false);
                        }
                    } else if first {
                        local.push(m);
                        first = false;
                    } else {
                        queue.push_back(vec![m]);
                    }
                }
            } else {
                for m in results.into_iter().rev() {
                    if m.done {
                        if record_solution(cfg, &m, &mut solns, on_solution) {
                            return (solns, false);
                        }
                    } else {
                        local.push(m);
                    }
                }
            }
        }
        if !local.is_empty() {
            queue.push_back(local);
        }
    }
    (solns, false)
}

fn output<'a>(val: &'a MValue<'a>, env: Env<'a>, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> String {
    match VClosure::mk_clos(val, env).close(lenv, senv) {
        Ok(closed) => closed.to_string(),
        Err(_) => "<cyclic term: cannot print (occurs check disabled)>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;
    use crate::machine::translate::translate;

    /// Parse, translate and run `src`, collecting the rendered solutions.
    fn solutions(src: &str, strategy: Strategy) -> Vec<String> {
        let arena = Bump::new();
        let ast = parser::parse(src).unwrap();
        let (comp, env_vals) = translate(&arena, ast);
        let run_arena = Bump::new();
        let env = import_env(&run_arena, &env_vals);
        let cfg = Config {
            strategy,
            optimize: false,
            timeout_secs: 60,
            occurs_check: true,
            strict: false,
            first_only: false,
        };
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        let mut out = Vec::new();
        let (_, timed_out) = {
            let mut on_solution = |s: &str| out.push(s.to_string());
            run_internal(&cfg, &run_arena, comp, env, deadline, &mut on_solution)
        };
        assert!(!timed_out, "test program timed out");
        out
    }

    /// B7: a solution whose answer still mentions an unresolved logic variable
    /// must be reported and counted, not silently dropped. `inert.gwk` is
    /// `exists x :: Nat. x.`, whose answer is a residual free variable.
    #[test]
    fn inert_reports_free_variable() {
        let src = std::fs::read_to_string("examples/inert.gwk").unwrap();
        let solns = solutions(&src, Strategy::Bfs);
        assert_eq!(solns.len(), 1);
        assert!(
            solns[0].starts_with('_'),
            "expected a free-variable placeholder, got {:?}",
            solns[0]
        );
    }

    /// B8: IDDFS must count distinct derivations that print identically once
    /// each, exactly like the other complete strategies, rather than collapsing
    /// them via a rendered-output set. Here both arms of the choice render `1`.
    #[test]
    fn iddfs_counts_indistinguishable_derivations() {
        let src = "f :: Nat\nf = 1 <> 1.\n\nf.";
        let bfs = solutions(src, Strategy::Bfs).len();
        let fair = solutions(src, Strategy::Fair).len();
        let iddfs = solutions(src, Strategy::Iddfs).len();
        assert_eq!(bfs, 2);
        assert_eq!(fair, 2);
        assert_eq!(iddfs, bfs);
        assert_eq!(iddfs, fair);
    }
}
