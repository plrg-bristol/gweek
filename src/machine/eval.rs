use std::rc::Rc;

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::SuspEnv;
use super::step::{Stack, Machine};
use super::vclosure::VClosure;

pub fn eval(comp: MComputation, env: Rc<Env>) {
    let m = Machine { comp: comp.into(), env: env.clone(), stack: Stack::empty_stack(), lenv: LogicEnv::new(), senv: SuspEnv::new(), done: false };
    let mut machines = vec![m];
    let mut next = Vec::new();
    let mut solns = 0;
    while !machines.is_empty() {
        for m in machines.drain(..) {
            for m in m.step() {
                if m.done {
                    if let MComputation::Return(v) = &*m.comp {
                        if let Some(s) = output(v.clone(), m.env.clone(), &m.lenv, &m.senv) {
                            println!("> {}", s);
                            solns += 1;
                        }
                    }
                } else {
                    next.push(m);
                }
            }
        }
        std::mem::swap(&mut machines, &mut next);
    }

    println!(">>> {} solutions", solns);
}

fn output(val: Rc<MValue>, env: Rc<Env>, lenv: &LogicEnv, senv: &SuspEnv) -> Option<String> {
    Some(VClosure::Clos { val, env }.close(lenv, senv)?.to_string())
}
