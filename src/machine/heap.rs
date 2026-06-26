//! # The heap
//!
//! Every runtime cell — values, environment links, stack frames — lives in one [`Heap`] and is
//! named by a small integer handle rather than a pointer, so a machine clone copies only ids. The
//! heap is split three ways: immortal program computations ([`CompId`]) and AST literals never move;
//! a small **nursery** holds freshly-allocated cells; and an **old** generation holds cells that
//! have survived a collection.
//!
//! Allocation bumps the nursery. When it fills, a **minor** collection (a Cheney two-space copy)
//! promotes the live nursery cells into the old generation and resets the nursery — its cost is
//! proportional to the survivors, not to all that was allocated. When the old generation grows past
//! its watermark, a **major** collection compacts it the same way. Both passes forward every handle
//! to a shared cell onto one survivor, so sharing is preserved.
//!
//! No write barrier is needed: cells are immutable once allocated and only ever point at
//! older cells, so there are never any old→young edges to remember (a debug assertion checks this
//! after each minor collection). The only mutable runtime state — the logic and suspension
//! environments — lives outside the heap and is scanned wholesale as part of the root set.

use std::mem;

use super::env::{Env, EnvInner};
use super::mterms::{MComputation, MValue};
use super::step::{Stack, StackInner, StkFrame};

/// Top bit of a [`NodeId`]: set marks the immortal-value region.
const IMMORTAL: u32 = 1 << 31;
/// Second bit of a [`NodeId`]: among collected cells, set marks the old generation and clear the
/// nursery. (Don't-care for immortal ids, whose region is decided by [`IMMORTAL`] first.)
const OLD: u32 = 1 << 30;
/// The remaining bits address a cell within its region.
const INDEX_MASK: u32 = !(IMMORTAL | OLD);

/// Default nursery capacity, in cells, before a minor collection is triggered.
const NURSERY_LIMIT: usize = 1 << 16;
/// Floor on the major-collection watermark, recomputed after each major collection.
const MIN_MAJOR_WATERMARK: usize = 1 << 16;
/// Headroom factor applied to the live old set when recomputing the major watermark.
const GROWTH: usize = 2;

/// The region a [`NodeId`] addresses.
enum Region {
    Immortal,
    Old,
    Nursery,
}

/// A handle to a value, environment, or stack cell. Two top bits tag the region (immortal value
/// store, old generation, or nursery); the rest is an index within that region.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(u32);

/// A handle to an immortal program computation. Computations are never collected.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CompId(u32);

impl NodeId {
    fn region(self) -> Region {
        if self.0 & IMMORTAL != 0 {
            Region::Immortal
        } else if self.0 & OLD != 0 {
            Region::Old
        } else {
            Region::Nursery
        }
    }

    fn index(self) -> usize {
        (self.0 & INDEX_MASK) as usize
    }
}

/// The unit of the collected space. Kept `Copy` so the collector can move a cell
/// by a plain read/write; `Forwarded` is the Cheney tombstone left behind in the
/// space a cell was copied out of.
#[derive(Clone, Copy)]
enum Node {
    Val(MValue),
    Env(EnvInner),
    Stack(StackInner),
    Forwarded(NodeId),
}

/// The collector's current activity, recorded for the duration of a collection so that the shared
/// `forward`/`scan` machinery knows which generations are live and where survivors go.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Outside a collection.
    Idle,
    /// A minor collection: the nursery is live, the old generation is treated as
    /// leaves, and survivors are appended to the old generation.
    Minor,
    /// A major collection: both generations are live and survivors are copied
    /// into `to_space`, which becomes the new old generation.
    Major,
}

pub struct Heap {
    /// Immortal program computations, indexed by [`CompId`].
    comps: Vec<MComputation>,
    /// Immortal AST values, indexed by a [`NodeId`] with the immortal bit set.
    imm_vals: Vec<MValue>,
    /// Immortal environments, indexed by a [`NodeId`] with the immortal bit set.
    imm_envs: Vec<EnvInner>,
    /// The old generation: cells that have survived at least one collection.
    old: Vec<Node>,
    /// The nursery: freshly-allocated cells, collected by a minor GC.
    nursery: Vec<Node>,
    /// To-space scratch for a major collection; becomes the new old generation.
    to_space: Vec<Node>,
    /// Trigger a minor collection once the nursery reaches this many cells.
    nursery_limit: usize,
    /// Trigger a major collection once the old generation reaches this many cells.
    major_watermark: usize,
    /// Floor on the major watermark, recomputed after each major collection.
    min_major_watermark: usize,
    /// The collector's activity for the duration of a collection.
    mode: Mode,
    /// During a minor collection, the index in `old` at which promoted cells begin
    /// — the start of the Cheney scan.
    scan_base: usize,
}

impl Heap {
    pub fn new() -> Heap {
        Heap::with_limits(NURSERY_LIMIT, MIN_MAJOR_WATERMARK)
    }

    /// A heap that collects aggressively — a minor GC once `min_nodes` cells are
    /// in the nursery and a major GC once that many survive into the old
    /// generation — for tests that want to exercise both passes under pressure.
    pub fn with_watermark(min_nodes: usize) -> Heap {
        Heap::with_limits(min_nodes, min_nodes)
    }

    fn with_limits(nursery_limit: usize, major_watermark: usize) -> Heap {
        Heap {
            comps: Vec::new(),
            imm_vals: Vec::new(),
            imm_envs: Vec::new(),
            old: Vec::new(),
            nursery: Vec::new(),
            to_space: Vec::new(),
            nursery_limit,
            major_watermark,
            min_major_watermark: major_watermark,
            mode: Mode::Idle,
            scan_base: 0,
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

    pub(crate) fn alloc_imm_env(&mut self, inner: EnvInner) -> Env {
        let id = self.imm_envs.len() as u32;
        self.imm_envs.push(inner);
        Env(NodeId(id | IMMORTAL))
    }

    // --- Runtime allocation (into the nursery) ---

    pub fn alloc_val(&mut self, val: MValue) -> NodeId {
        let id = self.nursery.len() as u32;
        self.nursery.push(Node::Val(val));
        NodeId(id)
    }

    pub fn alloc_thunk(&mut self, comp: CompId) -> NodeId {
        self.alloc_val(MValue::Thunk(comp))
    }

    pub(crate) fn alloc_env(&mut self, inner: EnvInner) -> Env {
        let id = self.nursery.len() as u32;
        self.nursery.push(Node::Env(inner));
        Env(NodeId(id))
    }

    pub(crate) fn alloc_stack(&mut self, inner: StackInner) -> Stack {
        let id = self.nursery.len() as u32;
        self.nursery.push(Node::Stack(inner));
        Stack(NodeId(id))
    }

    // --- Reads ---

    pub fn comp(&self, id: CompId) -> &MComputation {
        &self.comps[id.0 as usize]
    }

    /// The collected cell a handle names. Immortal handles do not name a `Node`.
    fn node(&self, id: NodeId) -> Node {
        match id.region() {
            Region::Old => self.old[id.index()],
            Region::Nursery => self.nursery[id.index()],
            Region::Immortal => unreachable!("immortal handle does not name a heap cell"),
        }
    }

    pub fn val(&self, id: NodeId) -> MValue {
        if let Region::Immortal = id.region() {
            return self.imm_vals[id.index()];
        }
        match self.node(id) {
            Node::Val(v) => v,
            _ => panic!("val() on a non-value node"),
        }
    }

    pub(crate) fn env_inner(&self, env: Env) -> EnvInner {
        if let Region::Immortal = env.0.region() {
            return self.imm_envs[env.0.index()];
        }
        match self.node(env.0) {
            Node::Env(e) => e,
            _ => panic!("env_inner() on a non-env node"),
        }
    }

    pub(crate) fn stack_inner(&self, stack: Stack) -> StackInner {
        match self.node(stack.0) {
            Node::Stack(s) => s,
            _ => panic!("stack_inner() on a non-stack node"),
        }
    }

    // --- Collector ---

    /// The nursery is full and the scheduler should collect at the next safe point.
    pub(crate) fn nursery_full(&self) -> bool {
        self.nursery.len() >= self.nursery_limit
    }

    /// The old generation has grown past its watermark and wants a major collection.
    pub(crate) fn needs_major(&self) -> bool {
        self.old.len() >= self.major_watermark
    }

    pub(crate) fn begin_minor(&mut self) {
        self.mode = Mode::Minor;
        self.scan_base = self.old.len();
    }

    pub(crate) fn end_minor(&mut self) {
        #[cfg(debug_assertions)]
        self.assert_no_old_to_young();
        self.nursery.clear();
        self.mode = Mode::Idle;
    }

    pub(crate) fn begin_major(&mut self) {
        self.mode = Mode::Major;
        self.to_space.clear();
    }

    pub(crate) fn end_major(&mut self) {
        self.old = mem::take(&mut self.to_space);
        self.major_watermark = self
            .old
            .len()
            .saturating_mul(GROWTH)
            .max(self.min_major_watermark);
        self.mode = Mode::Idle;
    }

    /// Append a surviving cell to the to-space — the old generation during a minor
    /// collection, the scratch space during a major — and return its new handle.
    /// Survivors always land in the old generation, hence the `OLD` tag.
    fn emit(&mut self, node: Node) -> NodeId {
        let dst = match self.mode {
            Mode::Minor => &mut self.old,
            Mode::Major => &mut self.to_space,
            Mode::Idle => unreachable!("emit outside a collection"),
        };
        let new = NodeId(dst.len() as u32 | OLD);
        dst.push(node);
        new
    }

    /// Move a cell into the to-space if it has not been moved already, returning
    /// its new handle. Immortal handles are leaves; old-generation handles are
    /// leaves during a minor collection (the generational shortcut) and copied
    /// during a major one. Forwarding a cell twice resolves to the same survivor,
    /// which is what preserves sharing.
    pub(crate) fn forward(&mut self, id: NodeId) -> NodeId {
        match id.region() {
            Region::Immortal => id,
            Region::Old => {
                if self.mode == Mode::Minor {
                    return id;
                }
                let idx = id.index();
                if let Node::Forwarded(n) = self.old[idx] {
                    return n;
                }
                let node = self.old[idx];
                let new = self.emit(node);
                self.old[idx] = Node::Forwarded(new);
                new
            }
            Region::Nursery => {
                let idx = id.index();
                if let Node::Forwarded(n) = self.nursery[idx] {
                    return n;
                }
                let node = self.nursery[idx];
                let new = self.emit(node);
                self.nursery[idx] = Node::Forwarded(new);
                new
            }
        }
    }

    pub(crate) fn forward_env(&mut self, env: Env) -> Env {
        Env(self.forward(env.0))
    }

    pub(crate) fn forward_stack(&mut self, stack: Stack) -> Stack {
        Stack(self.forward(stack.0))
    }

    /// Cheney scan: walk the freshly-copied cells, forwarding the children of each,
    /// until the frontier catches up with the allocation pointer. A minor scan
    /// walks the cells promoted into the old generation; a major scan walks all of
    /// to-space.
    pub(crate) fn scan(&mut self) {
        match self.mode {
            Mode::Minor => {
                let mut i = self.scan_base;
                while i < self.old.len() {
                    let node = self.old[i];
                    let scanned = self.scan_node(node);
                    self.old[i] = scanned;
                    i += 1;
                }
            }
            Mode::Major => {
                let mut i = 0;
                while i < self.to_space.len() {
                    let node = self.to_space[i];
                    let scanned = self.scan_node(node);
                    self.to_space[i] = scanned;
                    i += 1;
                }
            }
            Mode::Idle => unreachable!("scan outside a collection"),
        }
    }

    fn scan_node(&mut self, node: Node) -> Node {
        match node {
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

    /// Debug check of the generational invariant: after a minor collection no
    /// old-generation cell may point into the nursery. A violation means a live
    /// edge was missed and the nursery cells are about to be reclaimed from under
    /// it — a use-after-free in waiting.
    #[cfg(debug_assertions)]
    fn assert_no_old_to_young(&self) {
        for node in &self.old {
            node.for_each_child(|id| {
                debug_assert!(
                    !matches!(id.region(), Region::Nursery),
                    "old->young edge after a minor collection"
                );
            });
        }
    }
}

#[cfg(debug_assertions)]
impl Node {
    /// Visit every heap handle this cell points at. Used only by the
    /// generational-invariant assertion.
    fn for_each_child(self, mut f: impl FnMut(NodeId)) {
        use super::vclosure::VClosure;
        match self {
            Node::Val(v) => match v {
                MValue::Succ(a) | MValue::Inl(a) | MValue::Inr(a) => f(a),
                MValue::Pair(a, b) | MValue::Cons(a, b) => {
                    f(a);
                    f(b);
                }
                MValue::Var(_)
                | MValue::Unit
                | MValue::Nat(_)
                | MValue::Zero
                | MValue::Nil
                | MValue::Thunk(_) => {}
            },
            Node::Env(EnvInner::Cons(vc, tail)) => {
                if let VClosure::Clos { val, env } = vc {
                    f(val);
                    f(env.0);
                }
                f(tail.0);
            }
            Node::Stack(StackInner::Cons(sc, tail)) => {
                if let StkFrame::Value(id) = sc.frame {
                    f(id);
                }
                f(sc.env.0);
                f(tail.0);
            }
            Node::Env(EnvInner::Nil) | Node::Stack(StackInner::Nil) | Node::Forwarded(_) => {}
        }
    }
}
