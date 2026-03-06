use std::collections::VecDeque;
use std::rc::Rc;

use super::{env::Env, mterms::{MComputation, MValue}, Ident, VClosure};

type CClosure = (Rc<MComputation>, Rc<Env>);

#[derive(Clone)]
pub struct SuspEnv {
    entries: Vec<Result<VClosure, CClosure>>,
    pending: VecDeque<Ident>,
}

#[derive(Clone, Debug)]
pub struct SuspAt {
    pub ident: Ident,
    pub comp: Rc<MComputation>,
    pub env: Rc<Env>,
}

impl SuspEnv {

    pub fn new() -> SuspEnv {
        SuspEnv {
            entries: Vec::new(),
            pending: VecDeque::new(),
        }
    }

    pub fn size(&self) -> usize { self.entries.len() }

    pub fn fresh(&mut self, comp: &Rc<MComputation>, env: &Rc<Env>) -> Ident {
        let next = self.entries.len();
        self.entries.push(Err((comp.clone(), env.clone())));
        self.pending.push_back(next);
        next
    }

    pub fn lookup(&self, ident: &Ident) -> Result<VClosure, SuspAt> {
        match &self.entries[*ident] {
            Ok(vclos) => Ok(vclos.clone()),
            Err((comp, env)) => Err(SuspAt { ident: *ident, comp: comp.clone(), env: env.clone() }),
        }
    }

    pub fn set(&mut self, ident: &Ident, val: &Rc<MValue>, env: &Rc<Env>) {
        self.entries[*ident] = Ok(VClosure::mk_clos(val, env));
    }

    pub fn next(&self) -> Option<SuspAt> {
        for &ident in &self.pending {
            if self.entries[ident].is_err() {
                if let Err((comp, env)) = &self.entries[ident] {
                    return Some(SuspAt { ident, comp: comp.clone(), env: env.clone() });
                }
            }
        }
        None
    }
}
