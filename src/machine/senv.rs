use std::rc::Rc;

use super::env::Env;
use super::mterms::MComputation;
use super::{Ident, VClosure};

use super::mterms::MValue;

type CClosure<'a> = (Rc<MComputation>, Env<'a>);

#[derive(Clone)]
pub struct SuspEnv<'a> {
    entries: Rc<Vec<Result<VClosure<'a>, CClosure<'a>>>>,
    next_pending: usize,
}

#[derive(Clone, Debug)]
pub struct SuspAt<'a> {
    pub ident: Ident,
    pub comp: Rc<MComputation>,
    pub env: Env<'a>,
}

impl<'a> SuspEnv<'a> {
    pub fn new() -> SuspEnv<'a> {
        SuspEnv {
            entries: Rc::new(Vec::new()),
            next_pending: 0,
        }
    }

    pub fn fresh(&mut self, comp: &Rc<MComputation>, env: Env<'a>) -> Ident {
        let entries = Rc::make_mut(&mut self.entries);
        let next = entries.len();
        entries.push(Err((comp.clone(), env)));
        next
    }

    pub fn lookup(&self, ident: &Ident) -> Result<VClosure<'a>, SuspAt<'a>> {
        match &self.entries[*ident] {
            Ok(vclos) => Ok(vclos.clone()),
            Err((comp, env)) => Err(SuspAt {
                ident: *ident,
                comp: comp.clone(),
                env: *env,
            }),
        }
    }

    pub fn set(&mut self, ident: &Ident, val: &Rc<MValue>, env: Env<'a>) {
        Rc::make_mut(&mut self.entries)[*ident] = Ok(VClosure::mk_clos(val, env));
    }

    pub fn next(&mut self) -> Option<SuspAt<'a>> {
        while self.next_pending < self.entries.len() {
            match &self.entries[self.next_pending] {
                Ok(_) => self.next_pending += 1,
                Err((comp, env)) => {
                    return Some(SuspAt {
                        ident: self.next_pending,
                        comp: comp.clone(),
                        env: *env,
                    })
                }
            }
        }
        None
    }
}
