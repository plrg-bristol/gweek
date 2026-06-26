//! # The heap
//!
//! Every runtime cell — values, environment links, stack frames — lives in one [`Heap`] and is
//! named by a small integer handle rather than a pointer, so a machine clone copies only ids. The
//! heap is split: immortal program computations ([`CompId`]) and AST literals never move, while
//! runtime cells ([`NodeId`], top bit clear) live in a collected space that a Cheney two-space copy
//! reclaims at a safe point. Forwarding rewrites every handle to a shared node to one survivor, so
//! sharing is preserved across a collection.

use std::mem;

use super::env::{Env, EnvInner};
use super::mterms::{MComputation, MValue};
use super::step::{Stack, StackInner, StkFrame};

/// Top bit of a [`NodeId`]: set marks the immortal-value region, clear the collected space.
const IMMORTAL: u32 = 1 << 31;

/// Default minimum collected-space size before a collection is considered.
const MIN_WATERMARK: usize = 1 << 16;
/// Target headroom factor applied to the live set after a collection.
const GROWTH: usize = 2;

/// A handle to a value, environment, or stack cell. The top bit tags the region:
/// set = the immortal value store, clear = the collected space.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(u32);

/// A handle to an immortal program computation. Computations are never collected.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CompId(u32);

impl NodeId {
    fn is_immortal(self) -> bool {
        self.0 & IMMORTAL != 0
    }

    fn index(self) -> usize {
        (self.0 & !IMMORTAL) as usize
    }
}

/// The unit of the collected space. Kept `Copy` so the collector can move a cell
/// by a plain read/write; `Forwarded` is the Cheney tombstone left in from-space.
#[derive(Clone, Copy)]
enum Node {
    Val(MValue),
    Env(EnvInner),
    Stack(StackInner),
    Forwarded(NodeId),
}

pub struct Heap {
    /// Immortal program computations, indexed by [`CompId`].
    comps: Vec<MComputation>,
    /// Immortal AST values, indexed by a [`NodeId`] with the immortal bit set.
    imm_vals: Vec<MValue>,
    /// The collected heap (from-space), indexed by a [`NodeId`] with the bit clear.
    space: Vec<Node>,
    /// Cheney to-space, populated during a collection.
    to_space: Vec<Node>,
    /// Collect once the collected space reaches this many cells.
    watermark: usize,
    /// Floor on the watermark recomputed after each collection.
    min_watermark: usize,
}

impl Heap {
    pub fn new() -> Heap {
        Heap {
            comps: Vec::new(),
            imm_vals: Vec::new(),
            space: Vec::new(),
            to_space: Vec::new(),
            // Milestone 1: collection is inert; the watermark is never reached.
            watermark: usize::MAX,
            min_watermark: MIN_WATERMARK,
        }
    }

    /// A heap that collects aggressively once `min_nodes` cells are live, for
    /// tests that want to exercise the collector under pressure.
    pub fn with_watermark(min_nodes: usize) -> Heap {
        Heap {
            comps: Vec::new(),
            imm_vals: Vec::new(),
            space: Vec::new(),
            to_space: Vec::new(),
            watermark: min_nodes,
            min_watermark: min_nodes,
        }
    }

    // --- Immortal allocation (compile time) ---

    pub fn alloc_comp(&mut self, comp: MComputation) -> CompId {
        let id = self.comps.len() as u32;
        self.comps.push(comp);
        CompId(id)
    }

    pub fn alloc_imm_val(&mut self, val: MValue) -> NodeId {
        let id = self.imm_vals.len() as u32;
        self.imm_vals.push(val);
        NodeId(id | IMMORTAL)
    }

    // --- Runtime allocation (collected) ---

    pub fn alloc_val(&mut self, val: MValue) -> NodeId {
        let id = self.space.len() as u32;
        self.space.push(Node::Val(val));
        NodeId(id)
    }

    pub fn alloc_thunk(&mut self, comp: CompId) -> NodeId {
        self.alloc_val(MValue::Thunk(comp))
    }

    pub(crate) fn alloc_env(&mut self, inner: EnvInner) -> Env {
        let id = self.space.len() as u32;
        self.space.push(Node::Env(inner));
        Env(NodeId(id))
    }

    pub(crate) fn alloc_stack(&mut self, inner: StackInner) -> Stack {
        let id = self.space.len() as u32;
        self.space.push(Node::Stack(inner));
        Stack(NodeId(id))
    }

    // --- Reads ---

    pub fn comp(&self, id: CompId) -> &MComputation {
        &self.comps[id.0 as usize]
    }

    pub fn val(&self, id: NodeId) -> MValue {
        if id.is_immortal() {
            self.imm_vals[id.index()]
        } else {
            match self.space[id.index()] {
                Node::Val(v) => v,
                _ => panic!("val() on a non-value node"),
            }
        }
    }

    pub(crate) fn env_inner(&self, env: Env) -> EnvInner {
        match self.space[env.0.index()] {
            Node::Env(e) => e,
            _ => panic!("env_inner() on a non-env node"),
        }
    }

    pub(crate) fn stack_inner(&self, stack: Stack) -> StackInner {
        match self.space[stack.0.index()] {
            Node::Stack(s) => s,
            _ => panic!("stack_inner() on a non-stack node"),
        }
    }

    // --- Collector ---

    pub(crate) fn over_watermark(&self) -> bool {
        self.space.len() >= self.watermark
    }

    pub(crate) fn begin_collection(&mut self) {
        self.to_space.clear();
    }

    /// Move a node to to-space if it has not been moved already, returning its
    /// new handle. Immortal handles are leaves and pass through unchanged.
    pub(crate) fn forward(&mut self, id: NodeId) -> NodeId {
        if id.is_immortal() {
            return id;
        }
        if let Node::Forwarded(n) = self.space[id.index()] {
            return n;
        }
        let node = self.space[id.index()];
        let new = NodeId(self.to_space.len() as u32);
        self.to_space.push(node);
        self.space[id.index()] = Node::Forwarded(new);
        new
    }

    pub(crate) fn forward_env(&mut self, env: Env) -> Env {
        Env(self.forward(env.0))
    }

    pub(crate) fn forward_stack(&mut self, stack: Stack) -> Stack {
        Stack(self.forward(stack.0))
    }

    /// Cheney scan: walk to-space, forwarding the children of each moved node,
    /// until the frontier catches up with the allocation pointer.
    pub(crate) fn scan(&mut self) {
        let mut i = 0;
        while i < self.to_space.len() {
            let node = self.to_space[i];
            let scanned = match node {
                Node::Val(v) => Node::Val(self.forward_val(v)),
                Node::Env(EnvInner::Nil) => Node::Env(EnvInner::Nil),
                Node::Env(EnvInner::Cons(vc, tail)) => {
                    Node::Env(EnvInner::Cons(vc.forward(self), self.forward_env(tail)))
                }
                Node::Stack(StackInner::Nil) => Node::Stack(StackInner::Nil),
                Node::Stack(StackInner::Cons(sc, tail)) => {
                    let mut sc = sc;
                    if let StkFrame::Value(id) = sc.frame {
                        sc.frame = StkFrame::Value(self.forward(id));
                    }
                    sc.env = self.forward_env(sc.env);
                    Node::Stack(StackInner::Cons(sc, self.forward_stack(tail)))
                }
                Node::Forwarded(_) => unreachable!("forwarded node in to-space"),
            };
            self.to_space[i] = scanned;
            i += 1;
        }
    }

    fn forward_val(&mut self, val: MValue) -> MValue {
        match val {
            MValue::Succ(a) => MValue::Succ(self.forward(a)),
            MValue::Pair(a, b) => MValue::Pair(self.forward(a), self.forward(b)),
            MValue::Inl(a) => MValue::Inl(self.forward(a)),
            MValue::Inr(a) => MValue::Inr(self.forward(a)),
            MValue::Cons(a, b) => MValue::Cons(self.forward(a), self.forward(b)),
            MValue::Var(_)
            | MValue::Unit
            | MValue::Nat(_)
            | MValue::Zero
            | MValue::Nil
            | MValue::Thunk(_) => val,
        }
    }

    pub(crate) fn end_collection(&mut self) {
        self.space = mem::take(&mut self.to_space);
        self.watermark = self.space.len().saturating_mul(GROWTH).max(self.min_watermark);
    }
}
