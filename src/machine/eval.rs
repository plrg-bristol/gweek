//! # The search schedulers
//!
//! This module owns the search. It takes the heap and an initial machine, then drives the
//! machine's `run_to_branch` under one of four strategies, recording each solution. Four entry
//! points share the apparatus — [`eval()`] for the CLI, [`eval_collect`] and [`eval_streaming`]
//! for the web, [`run`] for tests — all dispatching on [`Strategy`]:
//!
//! - *BFS* — complete and fair, but its frontier may blow up (the default);
//! - *DFS* — lean and fast, yet incomplete on an infinite branch;
//! - *IDDFS* — depth-limited DFS, doubled until a round prunes nothing: complete, low memory;
//! - *Fair* — round-robin work-stacks, complete with DFS-like speed (the one to reach for).
//!
//! Each strategy keeps its whole frontier in an explicit container, so the gaps between
//! `run_to_branch` calls are natural safe points: when the heap asks to be collected, the scheduler
//! hands every live machine to [`collect`], which forwards their roots and reclaims the rest.

use std::collections::{HashMap, VecDeque};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use super::config::Config;
use super::env::Env;
use super::heap::{CompId, Heap};
use super::lvar::LogicEnv;
use super::mterms::MComputation;
use super::senv::SuspEnv;
use super::step::{Clock, Machine, RunResult, Stack};
use super::vclosure::VClosure;
use super::NodeId;

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

/// Run with output, using config for strategy/timeout.
pub fn eval(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId]) {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut on_solution = |s: &str| println!("> {}", s);
    let (solns, timed_out) = run_internal(cfg, heap, comp, env, deadline, &mut on_solution);
    if timed_out {
        println!(
            ">>> timed out after {}s, {} solutions found",
            cfg.timeout_secs, solns
        );
    } else {
        println!(">>> {} solutions", solns);
    }
}

/// Collect all solutions into a String (for WASM).
pub fn eval_collect(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId]) -> String {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut solutions = Vec::new();
    let (solns, timed_out) = {
        let mut on_solution = |s: &str| solutions.push(format!("> {}", s));
        run_internal(cfg, heap, comp, env, deadline, &mut on_solution)
    };
    if timed_out {
        solutions.push(format!(
            ">>> timed out after {}s, {} solutions found",
            cfg.timeout_secs, solns
        ));
    } else {
        solutions.push(format!(">>> {} solutions", solns));
    }
    solutions.join("\n")
}

/// Stream solutions one at a time via a callback, then return the summary line.
pub fn eval_streaming(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    vals: &[NodeId],
    mut on_solution: impl FnMut(&str),
) -> String {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut cb = |s: &str| on_solution(&format!("> {}", s));
    let (solns, timed_out) = run_internal(cfg, heap, comp, env, deadline, &mut cb);
    if timed_out {
        format!(
            ">>> timed out after {}s, {} solutions found",
            cfg.timeout_secs, solns
        )
    } else {
        format!(">>> {} solutions", solns)
    }
}

/// Run without output (for tests).
pub fn run(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId], print: bool) -> usize {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    if print {
        let mut on_solution = |s: &str| println!("> {}", s);
        run_internal(cfg, heap, comp, env, deadline, &mut on_solution).0
    } else {
        let mut on_solution = |_: &str| {};
        run_internal(cfg, heap, comp, env, deadline, &mut on_solution).0
    }
}

/// Build an Env from the compile-time list of top-level values.
fn import_env(heap: &mut Heap, vals: &[NodeId]) -> Env {
    let mut env = Env::empty(heap);
    for val in vals {
        env = env.extend_val(heap, *val, env);
    }
    env
}

fn run_internal(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    env: Env,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    match cfg.strategy {
        Strategy::Bfs => eval_bfs(cfg, heap, comp, env, deadline, on_solution),
        Strategy::Dfs => eval_dfs(cfg, heap, comp, env, deadline, on_solution),
        Strategy::Iddfs => eval_iddfs(cfg, heap, comp, env, deadline, on_solution),
        Strategy::Fair => eval_fair(cfg, heap, comp, env, deadline, on_solution),
    }
}

fn fresh_machine(heap: &mut Heap, comp: CompId, env: Env) -> Machine {
    Machine {
        cclos: (comp, env),
        stack: Stack::empty(heap),
        lenv: LogicEnv::new(),
        senv: SuspEnv::new(),
        done: false,
    }
}

/// Collect at a safe point, forwarding the roots of every live machine.
///
/// The plan's invariant — no intra-heap old→young pointers, with the mutable
/// logic/suspension environments scanned wholesale as roots — means a complete
/// root walk suffices and no write barrier is needed. Distinct machines often
/// share a `LogicEnv`/`SuspEnv` `Rc`; the dedup maps rebuild each shared store
/// exactly once so the sharing survives the collection.
fn collect<'m>(heap: &mut Heap, machines: impl Iterator<Item = &'m mut Machine>) {
    heap.begin_collection();
    let mut lenv_map: HashMap<usize, LogicEnv> = HashMap::new();
    let mut senv_map: HashMap<usize, SuspEnv> = HashMap::new();
    for m in machines {
        m.cclos.1 = heap.forward_env(m.cclos.1);
        m.stack = Stack(heap.forward(m.stack.0));
        let lkey = m.lenv.store_ptr();
        if let Some(c) = lenv_map.get(&lkey) {
            m.lenv = c.clone();
        } else {
            let n = m.lenv.forwarded(heap);
            lenv_map.insert(lkey, n.clone());
            m.lenv = n;
        }
        let skey = m.senv.store_ptr();
        if let Some(c) = senv_map.get(&skey) {
            m.senv = c.clone();
        } else {
            let n = m.senv.forwarded(heap);
            senv_map.insert(skey, n.clone());
            m.senv = n;
        }
    }
    heap.scan();
    heap.end_collection();
}

/// Record a solution; returns true if we should stop (--first mode).
fn record_solution(
    cfg: &Config,
    heap: &Heap,
    m: &Machine,
    solns: &mut usize,
    on_solution: &mut dyn FnMut(&str),
) -> bool {
    if let MComputation::Return(v) = heap.comp(m.cclos.0) {
        let v = *v;
        on_solution(&output(heap, v, m.cclos.1, &m.lenv, &m.senv));
        *solns += 1;
        if cfg.first_only {
            return true;
        }
    }
    false
}

fn eval_bfs(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    env: Env,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    let mut machines = vec![fresh_machine(heap, comp, env)];
    let mut next = Vec::new();
    let mut solns = 0;
    let mut clock = Clock::new(deadline);
    while !machines.is_empty() {
        while let Some(m) = machines.pop() {
            if clock.expired() {
                return (solns, true);
            }
            match m.run_to_branch(cfg, heap, deadline) {
                RunResult::Yield(results) => {
                    for m in results {
                        if m.done {
                            if record_solution(cfg, heap, &m, &mut solns, on_solution) {
                                return (solns, false);
                            }
                        } else {
                            next.push(m);
                        }
                    }
                }
                RunResult::TimedOut => return (solns, true),
                RunResult::NeedGc(m) => {
                    machines.push(m);
                    collect(heap, machines.iter_mut().chain(next.iter_mut()));
                }
            }
        }
        std::mem::swap(&mut machines, &mut next);
    }
    (solns, false)
}

fn eval_dfs(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    env: Env,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    let mut stack = vec![fresh_machine(heap, comp, env)];
    let mut solns = 0;
    let mut clock = Clock::new(deadline);
    while let Some(m) = stack.pop() {
        if clock.expired() {
            return (solns, true);
        }
        match m.run_to_branch(cfg, heap, deadline) {
            RunResult::Yield(results) => {
                for m in results.into_iter().rev() {
                    if m.done {
                        if record_solution(cfg, heap, &m, &mut solns, on_solution) {
                            return (solns, false);
                        }
                    } else {
                        stack.push(m);
                    }
                }
            }
            RunResult::TimedOut => return (solns, true),
            RunResult::NeedGc(m) => {
                stack.push(m);
                collect(heap, stack.iter_mut());
            }
        }
    }
    (solns, false)
}

fn eval_iddfs(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    env: Env,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    let mut solns = 0;
    let mut depth_limit: usize = 1;
    let mut clock = Clock::new(deadline);
    loop {
        let mut stack = vec![(fresh_machine(heap, comp, env), 0)];
        let mut cutoff = false;
        while let Some((m, depth)) = stack.pop() {
            if clock.expired() {
                return (solns, true);
            }
            if depth >= depth_limit {
                cutoff = true;
                continue;
            }
            match m.run_to_branch(cfg, heap, deadline) {
                RunResult::Yield(results) => {
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
                                && record_solution(cfg, heap, &m, &mut solns, on_solution)
                            {
                                return (solns, false);
                            }
                        } else {
                            stack.push((m, next_depth));
                        }
                    }
                }
                RunResult::TimedOut => return (solns, true),
                RunResult::NeedGc(m) => {
                    stack.push((m, depth));
                    collect(heap, stack.iter_mut().map(|(m, _)| m));
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

fn eval_fair(
    cfg: &Config,
    heap: &mut Heap,
    comp: CompId,
    env: Env,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    const QUOTA: usize = 10000;
    const MAX_THREADS: usize = 10000;
    let mut queue: VecDeque<Vec<Machine>> = VecDeque::new();
    queue.push_back(vec![fresh_machine(heap, comp, env)]);
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
            let results = match m.run_to_branch(cfg, heap, deadline) {
                RunResult::Yield(ms) => ms,
                RunResult::TimedOut => return (solns, true),
                RunResult::NeedGc(m) => {
                    local.push(m);
                    collect(heap, queue.iter_mut().flatten().chain(local.iter_mut()));
                    continue;
                }
            };
            if results.len() > 1 && queue.len() < MAX_THREADS {
                // Spread branch alternatives across the queue for fairness.
                // First alternative continues in the current thread (DFS);
                // remaining alternatives become new threads.
                let mut first = true;
                for m in results {
                    if m.done {
                        if record_solution(cfg, heap, &m, &mut solns, on_solution) {
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
                        if record_solution(cfg, heap, &m, &mut solns, on_solution) {
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

fn output(heap: &Heap, val: NodeId, env: Env, lenv: &LogicEnv, senv: &SuspEnv) -> String {
    match VClosure::mk_clos(val, env).close(heap, lenv, senv) {
        Ok(closed) => closed.to_string(),
        Err(_) => "<cyclic term: cannot print (occurs check disabled)>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::elaborate::elaborate;
    use crate::parser;

    fn test_config(strategy: Strategy) -> Config {
        Config {
            strategy,
            optimize: false,
            timeout_secs: 60,
            occurs_check: true,
            strict: false,
            first_only: false,
        }
    }

    /// Parse, elaborate and run `src`, collecting the rendered solutions.
    fn solutions(src: &str, strategy: Strategy) -> Vec<String> {
        let mut heap = Heap::new();
        let ast = parser::parse(src).unwrap();
        let (comp, env_vals) = elaborate(&mut heap, ast);
        let env = import_env(&mut heap, &env_vals);
        let cfg = test_config(strategy);
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        let mut out = Vec::new();
        let (_, timed_out) = {
            let mut on_solution = |s: &str| out.push(s.to_string());
            run_internal(&cfg, &mut heap, comp, env, deadline, &mut on_solution)
        };
        assert!(!timed_out, "test program timed out");
        out
    }

    /// Count solutions for `src` under `strategy`, with a heap whose watermark
    /// is set to `watermark` (small forces aggressive collection).
    fn count_with_watermark(src: &str, strategy: Strategy, watermark: usize) -> Vec<String> {
        let mut heap = Heap::with_watermark(watermark);
        let ast = parser::parse(src).unwrap();
        let (comp, env_vals) = elaborate(&mut heap, ast);
        let env = import_env(&mut heap, &env_vals);
        let cfg = test_config(strategy);
        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let mut out = Vec::new();
        let (_, timed_out) = {
            let mut on_solution = |s: &str| out.push(s.to_string());
            run_internal(&cfg, &mut heap, comp, env, deadline, &mut on_solution)
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

    /// The core GC safety test: under aggressive collection every strategy must
    /// reproduce, identically, the solutions it finds with collection all but
    /// disabled. A missed root would drop or corrupt a solution.
    #[test]
    fn collection_preserves_solutions() {
        let cases: &[&str] = &["examples/perm.gwk", "examples/coins.gwk"];
        let strategies = [
            Strategy::Bfs,
            Strategy::Dfs,
            Strategy::Iddfs,
            Strategy::Fair,
        ];
        for path in cases {
            let src = std::fs::read_to_string(path).unwrap();
            for &strategy in &strategies {
                let mut aggressive = count_with_watermark(&src, strategy, 256);
                let mut relaxed = count_with_watermark(&src, strategy, usize::MAX);
                aggressive.sort();
                relaxed.sort();
                assert_eq!(
                    aggressive, relaxed,
                    "GC changed solutions for {path} under {strategy:?}"
                );
            }
        }
    }
}
