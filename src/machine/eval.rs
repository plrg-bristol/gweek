use std::collections::{HashSet, VecDeque};
use std::rc::Rc;

use bumpalo::Bump;

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

pub fn eval(comp: MComputation, vals: Vec<Rc<MValue>>, strategy: Strategy) {
    let arena = Bump::new();
    let env = import_env(&arena, &vals);
    let solns = run_internal(&arena, comp, env, strategy, true);
    println!(">>> {} solutions", solns);
}

pub fn run(comp: MComputation, vals: Vec<Rc<MValue>>, strategy: Strategy, print: bool) -> usize {
    let arena = Bump::new();
    let env = import_env(&arena, &vals);
    run_internal(&arena, comp, env, strategy, print)
}

/// Build a bump-allocated Env from the compile-time list of top-level values.
/// Each function's closure env is the env built so far (its predecessors).
fn import_env<'a>(arena: &'a Bump, vals: &[Rc<MValue>]) -> Env<'a> {
    let mut env = Env::empty(arena);
    for val in vals {
        env = env.extend_val(arena, val.clone(), env);
    }
    env
}

fn run_internal<'a>(
    arena: &'a Bump,
    comp: MComputation,
    env: Env<'a>,
    strategy: Strategy,
    print: bool,
) -> usize {
    match strategy {
        Strategy::Bfs => eval_bfs(arena, comp, env, print),
        Strategy::Dfs => eval_dfs(arena, comp, env, print),
        Strategy::Iddfs => eval_iddfs(arena, comp, env, print),
        Strategy::Fair => eval_fair(arena, comp, env, print),
    }
}

fn fresh_machine<'a>(arena: &'a Bump, comp: MComputation, env: Env<'a>) -> Machine<'a> {
    Machine {
        arena,
        comp: comp.into(),
        env,
        stack: Stack::empty_stack(),
        lenv: LogicEnv::new(),
        senv: SuspEnv::new(),
        done: false,
    }
}

fn record_solution(m: &Machine, solns: &mut usize, print: bool) {
    if let MComputation::Return(v) = &*m.comp {
        if let Some(s) = output(v.clone(), m.env, &m.lenv, &m.senv) {
            if print {
                println!("> {}", s);
            }
            *solns += 1;
        }
    }
}

fn eval_bfs<'a>(arena: &'a Bump, comp: MComputation, env: Env<'a>, print: bool) -> usize {
    let mut machines = vec![fresh_machine(arena, comp, env)];
    let mut next = Vec::new();
    let mut solns = 0;
    while !machines.is_empty() {
        for m in machines.drain(..) {
            for m in m.run_to_branch() {
                if m.done {
                    record_solution(&m, &mut solns, print);
                } else {
                    next.push(m);
                }
            }
        }
        std::mem::swap(&mut machines, &mut next);
    }
    solns
}

fn eval_dfs<'a>(arena: &'a Bump, comp: MComputation, env: Env<'a>, print: bool) -> usize {
    let mut stack = vec![fresh_machine(arena, comp, env)];
    let mut solns = 0;
    while let Some(m) = stack.pop() {
        for m in m.run_to_branch().into_iter().rev() {
            if m.done {
                record_solution(&m, &mut solns, print);
            } else {
                stack.push(m);
            }
        }
    }
    solns
}

fn eval_iddfs<'a>(arena: &'a Bump, comp: MComputation, env: Env<'a>, print: bool) -> usize {
    let mut solns = 0;
    let mut depth_limit: usize = 1;
    let mut seen = HashSet::new();
    loop {
        let mut stack = vec![(fresh_machine(arena, comp.clone(), env), 0)];
        let mut cutoff = false;
        while let Some((m, depth)) = stack.pop() {
            if depth >= depth_limit {
                cutoff = true;
                continue;
            }
            let results = m.run_to_branch();
            let is_branch = results.len() > 1;
            for m in results.into_iter().rev() {
                if m.done {
                    if let MComputation::Return(v) = &*m.comp {
                        if let Some(s) = output(v.clone(), m.env, &m.lenv, &m.senv) {
                            if seen.insert(s.clone()) {
                                if print {
                                    println!("> {}", s);
                                }
                                solns += 1;
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
    solns
}

fn eval_fair<'a>(arena: &'a Bump, comp: MComputation, env: Env<'a>, print: bool) -> usize {
    const QUOTA: usize = 10000;
    let mut queue = VecDeque::new();
    queue.push_back(fresh_machine(arena, comp, env));
    let mut solns = 0;
    while let Some(m) = queue.pop_front() {
        let mut local = vec![m];
        let mut steps = 0;
        while let Some(m) = local.pop() {
            if steps >= QUOTA {
                queue.push_back(m);
                queue.extend(local.drain(..));
                break;
            }
            steps += 1;
            for m in m.run_to_branch().into_iter().rev() {
                if m.done {
                    record_solution(&m, &mut solns, print);
                } else {
                    local.push(m);
                }
            }
        }
    }
    solns
}

fn output<'a>(val: Rc<MValue>, env: Env<'a>, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Option<String> {
    Some(VClosure::Clos { val, env }.close(lenv, senv)?.to_string())
}
