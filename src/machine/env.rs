//! # The environment
//!
//! [`Env`] maps variables (de Bruijn indices) to value closures (`VClosure`). It is a persistent
//! cons-list of heap cells, so every environment is one [`NodeId`] handle and a clone is a single
//! integer copy.
//!
//! The [`extend_val`](Env::extend_val) extends an environment by a value closure, which it
//! de-aliases: if handed a `Var` it dereferences it to a value closure whose value is a head. Every
//! subsequent [`lookup`](Env::lookup) yields a head form which can immediately be pattern-matched.

use super::heap::Heap;
use super::mterms::MValue;
use super::{LVar, NodeId, SuspId, VClosure};

#[derive(Clone, Copy)]
pub(crate) enum EnvInner {
    Nil,
    Cons(VClosure, Env),
}

/// Persistent cons-list environment of heap cells. Clone/Copy is O(1).
#[derive(Clone, Copy)]
pub struct Env(pub(crate) NodeId);

/// Resolve a value to a head closure, following `Var` indices through `env`
/// so the stored closure is always in head form (every `lookup` yields a head).
fn dealias(heap: &Heap, val: NodeId, env: Env) -> VClosure {
    let mut vclos = VClosure::Clos { val, env };
    while let VClosure::Clos { val, env: e } = vclos {
        match heap.val(val) {
            MValue::Var(i) => vclos = e.lookup(heap, i).expect("var lookup in extend"),
            _ => break,
        }
    }
    vclos
}

impl Env {
    pub fn empty(heap: &mut Heap) -> Env {
        heap.alloc_env(EnvInner::Nil)
    }

    /// The empty environment in the immortal region: built once at program setup,
    /// it must outlive every collection, so its handle stays valid forever.
    pub fn empty_imm(heap: &mut Heap) -> Env {
        heap.alloc_imm_env(EnvInner::Nil)
    }

    pub fn lookup(&self, heap: &Heap, i: usize) -> Option<VClosure> {
        let mut cur = *self;
        let mut remaining = i;
        loop {
            match heap.env_inner(cur) {
                EnvInner::Nil => return None,
                EnvInner::Cons(vc, tail) => {
                    if remaining == 0 {
                        return Some(vc);
                    }
                    remaining -= 1;
                    cur = tail;
                }
            }
        }
    }

    pub fn extend_val(&self, heap: &mut Heap, val: NodeId, env: Env) -> Env {
        let vclos = dealias(heap, val, env);
        heap.alloc_env(EnvInner::Cons(vclos, *self))
    }

    /// Like [`extend_val`](Env::extend_val), but allocates the new cell in the
    /// immortal region: program setup that must outlive every collection, so the
    /// returned handle stays valid forever.
    pub fn extend_val_imm(&self, heap: &mut Heap, val: NodeId, env: Env) -> Env {
        let vclos = dealias(heap, val, env);
        heap.alloc_imm_env(EnvInner::Cons(vclos, *self))
    }

    pub fn extend_lvar(&self, heap: &mut Heap, ident: LVar) -> Env {
        heap.alloc_env(EnvInner::Cons(VClosure::LogicVar { ident }, *self))
    }

    pub fn extend_susp(&self, heap: &mut Heap, ident: SuspId) -> Env {
        heap.alloc_env(EnvInner::Cons(VClosure::Susp { ident }, *self))
    }
}

impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Env(...)")
    }
}
