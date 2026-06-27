//! # The suspension environment
//!
//! [`SuspEnv`] holds *suspensions* — `let`-bound computations that have not yet run. An entry is
//! `Err(cclos)` while it remains a frozen computation and becomes `Ok(vclos)` once forced; the
//! entries sit behind an `Rc`, so backtracking clones them copy-on-write. The signal that matters
//! is [`lookup`](SuspEnv::lookup): it returns the value, or an [`SuspAt`] meaning *not yet — force
//! it and come back*.

use std::rc::Rc;

use super::env::Env;
use super::heap::{CompId, Heap};
use super::{CClosure, NodeId, SuspId, VClosure};

#[derive(Clone)]
pub struct SuspEnv {
    entries: Rc<Vec<Result<VClosure, CClosure>>>,
    next_pending: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct SuspAt {
    pub ident: SuspId,
    pub cclos: CClosure,
}

impl SuspAt {
    pub fn comp(&self) -> CompId {
        self.cclos.0
    }

    pub fn env(&self) -> Env {
        self.cclos.1
    }
}

impl SuspEnv {
    pub fn new() -> SuspEnv {
        SuspEnv {
            entries: Rc::new(Vec::new()),
            next_pending: 0,
        }
    }

    pub fn fresh(&mut self, cclos: CClosure) -> SuspId {
        let entries = Rc::make_mut(&mut self.entries);
        let next = entries.len();
        entries.push(Err(cclos));
        SuspId(next)
    }

    pub fn lookup(&self, ident: &SuspId) -> Result<VClosure, SuspAt> {
        match &self.entries[ident.0] {
            Ok(vclos) => Ok(*vclos),
            Err(cclos) => Err(SuspAt {
                ident: *ident,
                cclos: *cclos,
            }),
        }
    }

    pub fn set(&mut self, ident: &SuspId, val: NodeId, env: Env) {
        Rc::make_mut(&mut self.entries)[ident.0] = Ok(VClosure::mk_clos(val, env));
    }

    /// Set a suspension entry directly from a VClosure (for branch-level use).
    pub fn set_done(&mut self, ident: SuspId, vclos: VClosure) {
        Rc::make_mut(&mut self.entries)[ident.0] = Ok(vclos);
    }

    pub fn next(&mut self) -> Option<SuspAt> {
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

    /// Returns true when all entries are done (no pending suspensions).
    pub fn all_done(&self) -> bool {
        self.entries.iter().all(|e| matches!(e, Ok(_)))
    }

    /// Identity of the shared store, so a collection can rebuild each distinct
    /// `SuspEnv` once and share it back across the machines that aliased it.
    pub(crate) fn store_ptr(&self) -> usize {
        Rc::as_ptr(&self.entries) as *const () as usize
    }

    /// Rebuild every stored closure against the new heap during a collection,
    /// returning a fresh store the survivors can share.
    pub(crate) fn forwarded(&self, heap: &mut Heap) -> SuspEnv {
        let mut entries = (*self.entries).clone();
        for entry in entries.iter_mut() {
            match entry {
                Ok(vc) => *vc = (*vc).forward(heap),
                Err((_, env)) => *env = heap.forward_env(*env),
            }
        }
        SuspEnv {
            entries: Rc::new(entries),
            next_pending: self.next_pending,
        }
    }
}

