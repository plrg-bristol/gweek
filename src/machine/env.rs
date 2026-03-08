use std::rc::Rc;

use bumpalo::Bump;

use super::mterms::MValue;
use super::{Ident, VClosure};

enum EnvInner<'a> {
    Nil,
    Cons(VClosure<'a>, Env<'a>),
}

/// Persistent cons-list environment backed by a bump arena.
/// Clone/Copy is O(1) — just a pointer copy.
#[derive(Clone, Copy)]
pub struct Env<'a>(&'a EnvInner<'a>);

impl<'a> std::fmt::Debug for Env<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Env(...)")
    }
}

impl<'a> Env<'a> {
    pub fn empty(arena: &'a Bump) -> Env<'a> {
        Env(arena.alloc(EnvInner::Nil))
    }

    pub fn lookup(&self, i: usize) -> Option<VClosure<'a>> {
        let mut cur = self.0;
        let mut remaining = i;
        loop {
            match cur {
                EnvInner::Nil => return None,
                EnvInner::Cons(vc, tail) => {
                    if remaining == 0 {
                        return Some(vc.clone());
                    }
                    remaining -= 1;
                    cur = tail.0;
                }
            }
        }
    }

    pub fn extend_val(&self, arena: &'a Bump, val: Rc<MValue>, env: Env<'a>) -> Env<'a> {
        Env(arena.alloc(EnvInner::Cons(VClosure::Clos { val, env }, *self)))
    }

    pub fn extend_lvar(&self, arena: &'a Bump, ident: Ident) -> Env<'a> {
        Env(arena.alloc(EnvInner::Cons(VClosure::LogicVar { ident }, *self)))
    }

    pub fn extend_susp(&self, arena: &'a Bump, ident: Ident) -> Env<'a> {
        Env(arena.alloc(EnvInner::Cons(VClosure::Susp { ident }, *self)))
    }

    /// Count total IR nodes across all function definitions (top-level vals only).
    #[cfg(feature = "opt-stats")]
    pub fn count_nodes(&self) -> usize {
        let mut total = 0;
        let mut cur = self.0;
        loop {
            match cur {
                EnvInner::Nil => return total,
                EnvInner::Cons(vc, tail) => {
                    if let VClosure::Clos { val, .. } = vc {
                        total += val.count_nodes();
                    }
                    cur = tail.0;
                }
            }
        }
    }
}
