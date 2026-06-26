//! # The CBPV IR
//!
//! The machine's term language: values ([`MValue`]) and computations ([`MComputation`]) in
//! Call-By-Push-Value. Every child is a heap handle — a [`NodeId`] for values, a [`CompId`] for
//! computations — so the terms are `Copy` and a clone of a machine moves only integers.

use crate::machine::value_type::ValueType;

use super::{CompId, NodeId};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum MValue {
    Var(usize),
    Unit,
    Nat(u64),
    Zero,
    Succ(NodeId),
    Pair(NodeId, NodeId),
    Inl(NodeId),
    Inr(NodeId),
    Nil,
    Cons(NodeId, NodeId),
    Thunk(CompId),
}

#[derive(PartialEq, Clone, Debug)]
pub enum MComputation {
    // Value eliminators
    Ifz {
        num: NodeId,
        zk: CompId,
        sk: CompId,
    },
    Match {
        list: NodeId,
        nilk: CompId,
        consk: CompId,
    },
    Case {
        sum: NodeId,
        inlk: CompId,
        inrk: CompId,
    },
    // CBPV primitives
    Return(NodeId),
    Bind {
        comp: CompId,
        cont: CompId,
    },
    Force(NodeId),
    Lambda {
        body: CompId,
    },
    App {
        op: CompId,
        arg: NodeId,
    },
    // FLP
    Choice(Box<[CompId]>),
    Exists {
        ptype: ValueType,
        body: CompId,
    },
    Equate {
        lhs: NodeId,
        rhs: NodeId,
        body: CompId,
    },
    // Recursion
    Rec {
        body: CompId,
    },
}

#[cfg(feature = "opt-stats")]
use super::heap::Heap;

#[cfg(feature = "opt-stats")]
pub fn count_nodes_comp(heap: &Heap, id: CompId) -> usize {
    match heap.comp(id) {
        MComputation::Return(v) => 1 + count_nodes_val(heap, *v),
        MComputation::Bind { comp, cont } => {
            1 + count_nodes_comp(heap, *comp) + count_nodes_comp(heap, *cont)
        }
        MComputation::Force(v) => 1 + count_nodes_val(heap, *v),
        MComputation::Lambda { body } => 1 + count_nodes_comp(heap, *body),
        MComputation::App { op, arg } => {
            1 + count_nodes_comp(heap, *op) + count_nodes_val(heap, *arg)
        }
        MComputation::Choice(cs) => 1 + cs.iter().map(|c| count_nodes_comp(heap, *c)).sum::<usize>(),
        MComputation::Exists { body, .. } => 1 + count_nodes_comp(heap, *body),
        MComputation::Equate { lhs, rhs, body } => {
            1 + count_nodes_val(heap, *lhs)
                + count_nodes_val(heap, *rhs)
                + count_nodes_comp(heap, *body)
        }
        MComputation::Ifz { num, zk, sk } => {
            1 + count_nodes_val(heap, *num)
                + count_nodes_comp(heap, *zk)
                + count_nodes_comp(heap, *sk)
        }
        MComputation::Match { list, nilk, consk } => {
            1 + count_nodes_val(heap, *list)
                + count_nodes_comp(heap, *nilk)
                + count_nodes_comp(heap, *consk)
        }
        MComputation::Case { sum, inlk, inrk } => {
            1 + count_nodes_val(heap, *sum)
                + count_nodes_comp(heap, *inlk)
                + count_nodes_comp(heap, *inrk)
        }
        MComputation::Rec { body } => 1 + count_nodes_comp(heap, *body),
    }
}

#[cfg(feature = "opt-stats")]
pub fn count_nodes_val(heap: &Heap, id: NodeId) -> usize {
    match heap.val(id) {
        MValue::Var(_) | MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => 1,
        MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => 1 + count_nodes_val(heap, v),
        MValue::Pair(a, b) | MValue::Cons(a, b) => {
            1 + count_nodes_val(heap, a) + count_nodes_val(heap, b)
        }
        MValue::Thunk(c) => 1 + count_nodes_comp(heap, c),
    }
}
