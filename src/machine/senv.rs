use std::rc::Rc;

use super::env::Env;
use super::mterms::MComputation;
use super::{Ident, VClosure};

use super::mterms::MValue;

type CClosure = (Rc<MComputation>, Env);

#[derive(Clone)]
pub struct SuspEnv {
    entries: Rc<Vec<Result<VClosure, CClosure>>>,
    next_pending: usize,
}

#[derive(Clone, Debug)]
pub struct SuspAt {
    pub ident: Ident,
    pub comp: Rc<MComputation>,
    pub env: Env,
}

impl SuspEnv {
    pub fn new() -> SuspEnv {
        SuspEnv {
            entries: Rc::new(Vec::new()),
            next_pending: 0,
        }
    }

    pub fn fresh(&mut self, comp: &Rc<MComputation>, env: &Env) -> Ident {
        let entries = Rc::make_mut(&mut self.entries);
        let next = entries.len();
        entries.push(Err((comp.clone(), env.clone())));
        next
    }

    pub fn lookup(&self, ident: &Ident) -> Result<VClosure, SuspAt> {
        match &self.entries[*ident] {
            Ok(vclos) => Ok(vclos.clone()),
            Err((comp, env)) => Err(SuspAt {
                ident: *ident,
                comp: comp.clone(),
                env: env.clone(),
            }),
        }
    }

    pub fn set(&mut self, ident: &Ident, val: &Rc<MValue>, env: &Env) {
        Rc::make_mut(&mut self.entries)[*ident] = Ok(VClosure::mk_clos(val, env));
    }

    pub fn next(&mut self) -> Option<SuspAt> {
        while self.next_pending < self.entries.len() {
            match &self.entries[self.next_pending] {
                Ok(_) => self.next_pending += 1,
                Err((comp, env)) => {
                    return Some(SuspAt {
                        ident: self.next_pending,
                        comp: comp.clone(),
                        env: env.clone(),
                    })
                }
            }
        }
        None
    }
}
