use std::collections::{HashSet, VecDeque};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use bumpalo::Bump;

use super::config::config;
use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::SuspEnv;
use super::step::{Machine, Stack};
use super::vclosure::VClosure;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    Bfs,
    Dfs,
    Iddfs,
    Fair,
}

/// Run with output, using config for strategy/timeout. Creates its own runtime arena.
pub fn eval<'a>(comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>]) {
    let cfg = config();
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs);
    let mut on_solution = |s: &str| println!("> {}", s);
    let (solns, timed_out) = run_internal(&arena, comp, env, cfg.strategy, deadline, &mut on_solution);
    if timed_out {
        println!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns);
    } else {
        println!(">>> {} solutions", solns);
    }
}

/// Collect all solutions into a String (for WASM).
pub fn eval_collect<'a>(comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>]) -> String {
    let cfg = config();
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs);
    let mut solutions = Vec::new();
    let (solns, timed_out) = {
        let mut on_solution = |s: &str| solutions.push(format!("> {}", s));
        run_internal(&arena, comp, env, cfg.strategy, deadline, &mut on_solution)
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
    comp: &'a MComputation<'a>,
    vals: &[&'a MValue<'a>],
    mut on_solution: impl FnMut(&str),
) -> String {
    let cfg = config();
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs);
    let mut cb = |s: &str| on_solution(&format!("> {}", s));
    let (solns, timed_out) = run_internal(&arena, comp, env, cfg.strategy, deadline, &mut cb);
    if timed_out {
        format!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns)
    } else {
        format!(">>> {} solutions", solns)
    }
}

/// Run without output (for tests). Creates its own runtime arena.
pub fn run<'a>(comp: &'a MComputation<'a>, vals: &[&'a MValue<'a>], strategy: Strategy, print: bool) -> usize {
    let arena = Bump::new();
    let env = import_env(&arena, vals);
    let deadline = Instant::now() + std::time::Duration::from_secs(3600);
    if print {
        let mut on_solution = |s: &str| println!("> {}", s);
        run_internal(&arena, comp, env, strategy, deadline, &mut on_solution).0
    } else {
        let mut on_solution = |_: &str| {};
        run_internal(&arena, comp, env, strategy, deadline, &mut on_solution).0
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
    arena: &'a Bump,
    comp: &'a MComputation<'a>,
    env: Env<'a>,
    strategy: Strategy,
    deadline: Instant,
    on_solution: &mut dyn FnMut(&str),
) -> (usize, bool) {
    match strategy {
        Strategy::Bfs => eval_bfs(arena, comp, env, deadline, on_solution),
        Strategy::Dfs => eval_dfs(arena, comp, env, deadline, on_solution),
        Strategy::Iddfs => eval_iddfs(arena, comp, env, deadline, on_solution),
        Strategy::Fair => eval_fair(arena, comp, env, deadline, on_solution),
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
fn record_solution(m: &Machine, solns: &mut usize, on_solution: &mut dyn FnMut(&str)) -> bool {
    if let MComputation::Return(v) = m.cclos.0 {
        if let Some(s) = output(m.arena, v, m.cclos.1, &m.lenv, &m.senv) {
            on_solution(&s);
            *solns += 1;
            if config().first_only {
                return true;
            }
        }
    }
    false
}

fn eval_bfs<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut machines = vec![fresh_machine(arena, comp, env)];
    let mut next = Vec::new();
    let mut solns = 0;
    let mut iters = 0u32;
    while !machines.is_empty() {
        for m in machines.drain(..) {
            iters += 1;
            if iters & 1023 == 0 && Instant::now() >= deadline {
                return (solns, true);
            }
            for m in m.run_to_branch() {
                if m.done {
                    if record_solution(&m, &mut solns, on_solution) {
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

fn eval_dfs<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut stack = vec![fresh_machine(arena, comp, env)];
    let mut solns = 0;
    let mut iters = 0u32;
    while let Some(m) = stack.pop() {
        iters += 1;
        if iters & 1023 == 0 && Instant::now() >= deadline {
            return (solns, true);
        }
        for m in m.run_to_branch().into_iter().rev() {
            if m.done {
                if record_solution(&m, &mut solns, on_solution) {
                    return (solns, false);
                }
            } else {
                stack.push(m);
            }
        }
    }
    (solns, false)
}

fn eval_iddfs<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    let mut solns = 0;
    let mut depth_limit: usize = 1;
    let mut seen = HashSet::new();
    let mut iters = 0u32;
    loop {
        let mut stack = vec![(fresh_machine(arena, comp, env), 0)];
        let mut cutoff = false;
        while let Some((m, depth)) = stack.pop() {
            iters += 1;
            if iters & 1023 == 0 && Instant::now() >= deadline {
                return (solns, true);
            }
            if depth >= depth_limit {
                cutoff = true;
                continue;
            }
            let results = m.run_to_branch();
            let is_branch = results.len() > 1;
            for m in results.into_iter().rev() {
                if m.done {
                    if let MComputation::Return(v) = m.cclos.0 {
                        if let Some(s) = output(m.arena, v, m.cclos.1, &m.lenv, &m.senv) {
                            if seen.insert(s.clone()) {
                                on_solution(&s);
                                solns += 1;
                                if config().first_only {
                                    return (solns, false);
                                }
                            }
                        }
                    }
                } else {
                    let next_depth = if is_branch { depth + 1 } else { depth };
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

fn eval_fair<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: Env<'a>, deadline: Instant, on_solution: &mut dyn FnMut(&str)) -> (usize, bool) {
    const QUOTA: usize = 10000;
    let mut queue = VecDeque::new();
    queue.push_back(fresh_machine(arena, comp, env));
    let mut solns = 0;
    let mut iters = 0u32;
    while let Some(m) = queue.pop_front() {
        let mut local = vec![m];
        let mut steps = 0;
        while let Some(m) = local.pop() {
            iters += 1;
            if iters & 1023 == 0 && Instant::now() >= deadline {
                return (solns, true);
            }
            if steps >= QUOTA {
                queue.push_back(m);
                queue.extend(local.drain(..));
                break;
            }
            steps += 1;
            for m in m.run_to_branch().into_iter().rev() {
                if m.done {
                    if record_solution(&m, &mut solns, on_solution) {
                        return (solns, false);
                    }
                } else {
                    local.push(m);
                }
            }
        }
    }
    (solns, false)
}

fn output<'a>(arena: &'a Bump, val: &'a MValue<'a>, env: Env<'a>, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Option<String> {
    Some(VClosure::Clos { val, env }.close(arena, lenv, senv)?.to_string())
}
