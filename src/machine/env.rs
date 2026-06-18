//! # The de Bruijn value environment
//!
//! [`Env`] is the runtime variable environment: a persistent cons-list of `VClosure`s backed by
//! the bump arena, indexed by de Bruijn position. The list cells are an internal `EnvInner` enum
//! and `Env` is a single pointer to the head cell — so `Env` is `Copy` and O(1) to clone, which
//! is what makes cloning a machine at a branch cheap. Each `extend_*` allocates one fresh cell
//! pointing at the current head, so sibling branches share the tail.
//!
//! **Subtlety:** [`extend_val`](Env::extend_val) *dealiases*. If the value is itself a `Var(i)`,
//! it follows the variable chain to a non-`Var` closure and pushes *that*, collapsing
//! indirection eagerly so a later [`lookup`](Env::lookup) lands on a real closure in one hop.
//! This eager resolution is load-bearing for the correctness of the closing operations.

use bumpalo::Bump;

use super::mterms::MValue;
use super::{LVar, SuspId, VClosure};

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
                        return Some(*vc);
                    }
                    remaining -= 1;
                    cur = tail.0;
                }
            }
        }
    }

    pub fn extend_val(&self, arena: &'a Bump, val: &'a MValue<'a>, env: Env<'a>) -> Env<'a> {
        let mut vclos = VClosure::Clos { val, env };
        while let VClosure::Clos { val: MValue::Var(i), env: e } = vclos {
            vclos = e.lookup(*i).expect("var lookup in extend");
        }
        Env(arena.alloc(EnvInner::Cons(vclos, *self)))
    }

    pub fn extend_lvar(&self, arena: &'a Bump, ident: LVar) -> Env<'a> {
        Env(arena.alloc(EnvInner::Cons(VClosure::LogicVar { ident }, *self)))
    }

    pub fn extend_susp(&self, arena: &'a Bump, ident: SuspId) -> Env<'a> {
        Env(arena.alloc(EnvInner::Cons(VClosure::Susp { ident }, *self)))
    }

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
