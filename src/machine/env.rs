use std::rc::Rc;

use super::mterms::MValue;
use super::{Ident, VClosure};

/// Optimize every function in the environment, rebuilding closure chains so
/// that each function's closure env contains already-optimized predecessors.
pub fn map_env_vals<F: Fn(&Rc<MValue>) -> Rc<MValue>>(env: &Rc<Env>, f: &F) -> Rc<Env> {
    let mut new_env = Env::empty();
    for vc in &env.vec {
        match vc {
            VClosure::Clos { val, .. } => {
                new_env = new_env.extend_val(f(val), new_env.clone());
            }
            VClosure::LogicVar { ident } => {
                new_env = new_env.extend_lvar(*ident);
            }
            VClosure::Susp { ident } => {
                new_env = new_env.extend_susp(*ident);
            }
        }
    }
    new_env
}

#[derive(Clone, Debug)]
pub struct Env {
    vec: Vec<VClosure>,
}

impl Env {
    pub fn empty() -> Rc<Env> {
        Env { vec: Vec::new() }.into()
    }

    pub fn lookup(&self, i: usize) -> Option<VClosure> {
        let len = self.vec.len();
        if i < len {
            Some(self.vec[len - 1 - i].clone())
        } else {
            None
        }
    }

    fn extend(&self, vclos: VClosure) -> Env {
        let mut vec = self.vec.clone();
        vec.push(vclos);
        Env { vec }
    }

    pub fn extend_val(&self, val: Rc<MValue>, env: Rc<Env>) -> Rc<Env> {
        self.extend(VClosure::Clos { val, env }).into()
    }

    pub fn extend_lvar(&self, ident: Ident) -> Rc<Env> {
        self.extend(VClosure::LogicVar { ident }).into()
    }

    pub fn extend_susp(&self, ident: Ident) -> Rc<Env> {
        self.extend(VClosure::Susp { ident }).into()
    }
}
