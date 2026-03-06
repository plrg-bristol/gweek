use std::rc::Rc;

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::SuspEnv;
use super::step::{Stack, Machine};
use super::vclosure::VClosure;

pub fn eval(comp: MComputation, env: Rc<Env>) {
    let m = Machine { comp: comp.into(), env: env.clone(), stack: Stack::empty_stack(), lenv: LogicEnv::new().into(), senv: SuspEnv::new().into(), done: false };
    let mut machines = vec![m];
    let mut solns = 0;
    while !machines.is_empty() {
        let (done, ms): (Vec<Machine>, Vec<Machine>) = machines.into_iter()
            .flat_map(|m| m.step())
            .partition(|m| m.done);

        let mut dones = done.iter();
        while let Some(m) = dones.next() {
            match &*m.comp {
                MComputation::Return(v) => {
                    let out = output(v.clone(), m.env.clone(), &m.lenv, &m.senv);
                    match out {
                        Some(xs) => { println!("> {}", xs); solns += 1 }
                        None => ()
                    }
                },
                _ => unreachable!()
            }
        }
        machines = ms;
    }

    println!(">>> {} solutions", solns);
}

fn output(val: Rc<MValue>, env: Rc<Env>, lenv: &LogicEnv, senv: &SuspEnv) -> Option<String> {
    Some(VClosure::Clos { val, env }.close(lenv, senv)?.to_string())
}
