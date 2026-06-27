//! # The suspension environment
//!
//! [`SuspEnv`] holds *suspensions* — `let`-bound computations that have not yet run.
//! Each entry is one of three states: [`SuspState::Suspended`] (a frozen computation),
//! [`SuspState::Running`] (currently being forced by a thread), or [`SuspState::Done`]
//! (fully evaluated and memoized). Entries sit behind an `Rc`, so backtracking clones
//! them copy-on-write. The signal that matters is [`lookup`](SuspEnv::lookup): it returns
//! the value, or an [`SuspAt`] meaning *not yet — force it and come back*.

use std::rc::Rc;

use super::env::Env;
use super::heap::{CompId, Heap};
use super::{CClosure, NodeId, SuspId, VClosure};

/// The three states a suspension can be in.
#[derive(Clone, Copy, Debug)]
pub(crate) enum SuspState {
    /// Not yet evaluated — the frozen computation.
    Suspended(CClosure),
    /// Currently being evaluated by some thread.
    Running(CClosure),
    /// Evaluation complete, value memoized.
    Done(VClosure),
}

#[derive(Clone)]
pub struct SuspEnv {
    entries: Rc<Vec<SuspState>>,
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
        entries.push(SuspState::Suspended(cclos));
        SuspId(next)
    }

    pub fn lookup(&self, ident: &SuspId) -> Result<VClosure, SuspAt> {
        match &self.entries[ident.0] {
            SuspState::Done(vclos) => Ok(*vclos),
            SuspState::Suspended(cclos) | SuspState::Running(cclos) => Err(SuspAt {
                ident: *ident,
                cclos: *cclos,
            }),
        }
    }

    pub fn set(&mut self, ident: &SuspId, val: NodeId, env: Env) {
        Rc::make_mut(&mut self.entries)[ident.0] = SuspState::Done(VClosure::mk_clos(val, env));
    }

    /// Set a suspension entry directly from a VClosure (for branch-level use).
    pub fn set_done(&mut self, ident: SuspId, vclos: VClosure) {
        Rc::make_mut(&mut self.entries)[ident.0] = SuspState::Done(vclos);
    }

    /// Get a reference to the state of a suspension entry.
    pub(crate) fn get(&self, ident: SuspId) -> SuspState {
        self.entries[ident.0]
    }

    /// Get the CClosure for a suspension that is not yet done.
    pub fn get_suspension(&self, ident: SuspId) -> CClosure {
        match &self.entries[ident.0] {
            SuspState::Suspended(cclos) | SuspState::Running(cclos) => *cclos,
            SuspState::Done(_) => panic!("get_suspension on done entry"),
        }
    }

    /// Reset a Running suspension back to Suspended (used when forking branches).
    pub fn reset_to_suspended(&mut self, ident: SuspId, cclos: CClosure) {
        let entries = Rc::make_mut(&mut self.entries);
        entries[ident.0] = SuspState::Suspended(cclos);
    }

    /// Mark a suspension as running (being evaluated by a thread).
    pub fn mark_running(&mut self, ident: SuspId) {
        let entries = Rc::make_mut(&mut self.entries);
        if let SuspState::Suspended(cclos) = entries[ident.0] {
            entries[ident.0] = SuspState::Running(cclos);
        }
    }

    pub fn next(&mut self) -> Option<SuspAt> {
        while self.next_pending < self.entries.len() {
            match &self.entries[self.next_pending] {
                SuspState::Done(_) | SuspState::Running(_) => self.next_pending += 1,
                SuspState::Suspended(cclos) => {
                    return Some(SuspAt {
                        ident: SuspId(self.next_pending),
                        cclos: *cclos,
                    })
                }
            }
        }
        None
    }

    /// Returns true when all entries are done (no pending or running suspensions).
    pub fn all_done(&self) -> bool {
        self.entries.iter().all(|e| matches!(e, SuspState::Done(_)))
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
                SuspState::Done(vc) => *vc = (*vc).forward(heap),
                SuspState::Suspended((_, env)) | SuspState::Running((_, env)) => {
                    *env = heap.forward_env(*env)
                }
            }
        }
        SuspEnv {
            entries: Rc::new(entries),
            next_pending: self.next_pending,
        }
    }
}
