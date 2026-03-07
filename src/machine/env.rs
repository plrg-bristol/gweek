use std::rc::Rc;

use super::mterms::MValue;
use super::{Ident, VClosure};

/// Apply a transformation to every MValue in the environment.
pub fn map_env_vals<F: Fn(&Rc<MValue>) -> Rc<MValue>>(env: &Rc<Env>, f: &F) -> Rc<Env> {
    Env {
        vec: env
            .vec
            .iter()
            .map(|vc| match vc {
                VClosure::Clos { val, env } => VClosure::Clos {
                    val: f(val),
                    env: env.clone(),
                },
                other => other.clone(),
            })
            .collect(),
    }
    .into()
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
