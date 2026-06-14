use std::rc::Rc;

use super::env::Env;
use super::mterms::MValue;
use super::{CClosure, SuspId, VClosure};

#[derive(Clone)]
pub struct SuspEnv<'a> {
    entries: Rc<Vec<Result<VClosure<'a>, CClosure<'a>>>>,
    next_pending: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct SuspAt<'a> {
    pub ident: SuspId,
    pub cclos: CClosure<'a>,
}

impl<'a> SuspAt<'a> {
    pub fn comp(&self) -> &'a super::mterms::MComputation<'a> {
        self.cclos.0
    }

    pub fn env(&self) -> Env<'a> {
        self.cclos.1
    }
}

impl<'a> SuspEnv<'a> {
    pub fn new() -> SuspEnv<'a> {
        SuspEnv {
            entries: Rc::new(Vec::new()),
            next_pending: 0,
        }
    }

    pub fn fresh(&mut self, cclos: CClosure<'a>) -> SuspId {
        let entries = Rc::make_mut(&mut self.entries);
        let next = entries.len();
        entries.push(Err(cclos));
        SuspId(next)
    }

    pub fn lookup(&self, ident: &SuspId) -> Result<VClosure<'a>, SuspAt<'a>> {
        match &self.entries[ident.0] {
            Ok(vclos) => Ok(*vclos),
            Err(cclos) => Err(SuspAt {
                ident: *ident,
                cclos: *cclos,
            }),
        }
    }

    pub fn set(&mut self, ident: &SuspId, val: &'a MValue<'a>, env: Env<'a>) {
        Rc::make_mut(&mut self.entries)[ident.0] = Ok(VClosure::mk_clos(val, env));
    }

    pub fn next(&mut self) -> Option<SuspAt<'a>> {
        while self.next_pending < self.entries.len() {
            match &self.entries[self.next_pending] {
                Ok(_) => self.next_pending += 1,
                Err(cclos) => {
                    return Some(SuspAt {
                        ident: SuspId(self.next_pending),
                        cclos: *cclos,
                    })
                }
            }
        }
        None
    }
}
