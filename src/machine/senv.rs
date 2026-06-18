//! # The suspension environment
//!
//! [`SuspEnv`] stores **suspensions** — `let`-bound computations that have not yet run. Each
//! entry is `Err(cclos)` while still a pending computation closure and becomes `Ok(vclos)` once
//! forced to a value; a `next_pending` cursor tracks where to resume draining. Suspensions are
//! identified by the `SuspId` newtype, distinct from logic variables' `LVar`.
//!
//! The entries sit behind an `Rc`, giving copy-on-write backtracking like the logic store:
//! cloning a machine at a branch is cheap, and the first write of a shared clone deep-copies the
//! vector. [`fresh`](SuspEnv::fresh) appends a pending entry (called when a non-strict `let`
//! freezes its right-hand side); [`lookup`](SuspEnv::lookup) returns the value or an
//! [`SuspAt`] signalling "still pending, reschedule"; [`set`](SuspEnv::set) records a forced
//! result; [`next`](SuspEnv::next) yields the first still-pending suspension when draining at
//! the end of a run.

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
