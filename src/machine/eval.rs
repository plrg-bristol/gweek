use std::rc::Rc;
use std::collections::VecDeque;

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::SuspEnv;
use super::step::{Stack, Machine};
use super::vclosure::VClosure;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy { Bfs, Dfs, Iddfs }

pub fn eval(comp: MComputation, env: Rc<Env>, strategy: Strategy) {
    match strategy {
        Strategy::Bfs => eval_bfs(comp, env),
        Strategy::Dfs => eval_dfs(comp, env),
        Strategy::Iddfs => eval_iddfs(comp, env),
    }
}

fn fresh_machine(comp: MComputation, env: Rc<Env>) -> Machine {
    Machine {
        comp: comp.into(),
        env,
        stack: Stack::empty_stack(),
        lenv: LogicEnv::new(),
        senv: SuspEnv::new(),
        done: false,
    }
}

fn handle_done(m: &Machine, solns: &mut usize) {
    if let MComputation::Return(v) = &*m.comp {
        if let Some(s) = output(v.clone(), m.env.clone(), &m.lenv, &m.senv) {
            println!("> {}", s);
            *solns += 1;
        }
    }
}

fn eval_bfs(comp: MComputation, env: Rc<Env>) {
    let mut machines = vec![fresh_machine(comp, env)];
    let mut next = Vec::new();
    let mut solns = 0;
    while !machines.is_empty() {
        for m in machines.drain(..) {
            for m in m.step() {
                if m.done {
                    handle_done(&m, &mut solns);
                } else {
                    next.push(m);
                }
            }
        }
        std::mem::swap(&mut machines, &mut next);
    }
    println!(">>> {} solutions", solns);
}

fn eval_dfs(comp: MComputation, env: Rc<Env>) {
    let mut stack = vec![fresh_machine(comp, env)];
    let mut solns = 0;
    while let Some(m) = stack.pop() {
        let results = m.step();
        for m in results.into_iter().rev() {
            if m.done {
                handle_done(&m, &mut solns);
            } else {
                stack.push(m);
            }
        }
    }
    println!(">>> {} solutions", solns);
}

fn eval_iddfs(comp: MComputation, env: Rc<Env>) {
    let mut solns = 0;
    let mut depth_limit: usize = 1;
    let mut seen = std::collections::HashSet::new();
    loop {
        let mut stack: Vec<(Machine, usize)> = vec![(fresh_machine(comp.clone(), env.clone()), 0)];
        let mut cutoff = false;
        while let Some((m, depth)) = stack.pop() {
            if depth >= depth_limit {
                cutoff = true;
                continue;
            }
            let results = m.step();
            let n = results.len();
            let is_branch = n > 1;
            for m in results.into_iter().rev() {
                if m.done {
                    if let MComputation::Return(v) = &*m.comp {
                        if let Some(s) = output(v.clone(), m.env.clone(), &m.lenv, &m.senv) {
                            if seen.insert(s.clone()) {
                                println!("> {}", s);
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
        if !cutoff { break; }
        depth_limit *= 2;
    }
    println!(">>> {} solutions", solns);
}

fn output(val: Rc<MValue>, env: Rc<Env>, lenv: &LogicEnv, senv: &SuspEnv) -> Option<String> {
    Some(VClosure::Clos { val, env }.close(lenv, senv)?.to_string())
}
