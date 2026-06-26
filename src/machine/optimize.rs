//! # The equational optimiser
//!
//! An optional peephole optimiser over CBPV terms (enabled by `-o`) that rewrites a program by the
//! equational laws of the theory while preserving its multiset of solutions. [`optimize`] rewrites
//! the main computation, [`optimize_val`] a function value. The machinery is one generic
//! binder-aware traversal (`map_val`/`map_comp`), which the de Bruijn passes — shift, subst, swap —
//! merely wrap; the driver optimises subterms under a compile-time environment, then applies the
//! top-level rules to a fixpoint: beta and eta, dead-bind, the pull/assoc family, choice
//! flattening, equate decomposition, and eliminator beta.

use super::heap::{CompId, Heap};
use super::mterms::{MComputation, MValue};
use super::NodeId;

/// Optimize a computation using equational laws from the CBPV theory.
pub fn optimize(heap: &mut Heap, comp: CompId) -> CompId {
    #[cfg(feature = "opt-stats")]
    let before = super::mterms::count_nodes_comp(heap, comp);
    let result = opt_comp(heap, comp);
    #[cfg(feature = "opt-stats")]
    {
        let after = super::mterms::count_nodes_comp(heap, result);
        eprintln!(
            "[opt] main:  {before} -> {after} nodes ({:+.1}%)",
            pct(before, after)
        );
        stats::report();
    }
    result
}

/// Optimize an MValue (recursing into Thunks to optimize computations).
pub fn optimize_val(heap: &mut Heap, val: NodeId) -> NodeId {
    opt_val(heap, val, &[])
}

/// Optimize an entire environment and print per-function stats.
#[cfg(feature = "opt-stats")]
pub fn optimize_env_with_stats(
    heap: &mut Heap,
    env: &[NodeId],
    f: &dyn Fn(&mut Heap, NodeId) -> NodeId,
) -> Vec<NodeId> {
    let before_total: usize = env
        .iter()
        .map(|v| super::mterms::count_nodes_val(heap, *v))
        .sum();
    let result: Vec<NodeId> = env.iter().map(|v| f(heap, *v)).collect();
    let after_total: usize = result
        .iter()
        .map(|v| super::mterms::count_nodes_val(heap, *v))
        .sum();
    eprintln!(
        "[opt] env:   {before_total} -> {after_total} nodes ({:+.1}%)",
        pct(before_total, after_total)
    );
    stats::report();
    result
}

#[cfg(feature = "opt-stats")]
fn pct(before: usize, after: usize) -> f64 {
    if before == 0 {
        0.0
    } else {
        (after as f64 - before as f64) / before as f64 * 100.0
    }
}

#[cfg(feature = "opt-stats")]
mod stats {
    use std::cell::Cell;
    thread_local! {
        static APP_BIND: Cell<u32> = const { Cell::new(0) };
        static LAM_CHOICE: Cell<u32> = const { Cell::new(0) };
        static LAM_EXISTS: Cell<u32> = const { Cell::new(0) };
        static LAM_EQUATE: Cell<u32> = const { Cell::new(0) };
        static EQ_EXISTS: Cell<u32> = const { Cell::new(0) };
        static EQ_CHOICE: Cell<u32> = const { Cell::new(0) };
        static DEAD_END: Cell<u32> = const { Cell::new(0) };
        static CYCLE: Cell<u32> = const { Cell::new(0) };
        static IFZ_BETA: Cell<u32> = const { Cell::new(0) };
        static MATCH_BETA: Cell<u32> = const { Cell::new(0) };
        static CASE_BETA: Cell<u32> = const { Cell::new(0) };
        static FORCE_BETA: Cell<u32> = const { Cell::new(0) };
        static DEAD_BIND: Cell<u32> = const { Cell::new(0) };
        static BIND_ETA: Cell<u32> = const { Cell::new(0) };
        static LAM_BETA: Cell<u32> = const { Cell::new(0) };
    }
    pub fn bump(name: &str) {
        match name {
            "app-bind" => APP_BIND.with(|c| c.set(c.get() + 1)),
            "lam-choice" => LAM_CHOICE.with(|c| c.set(c.get() + 1)),
            "lam-exists" => LAM_EXISTS.with(|c| c.set(c.get() + 1)),
            "lam-equate" => LAM_EQUATE.with(|c| c.set(c.get() + 1)),
            "eq-exists" => EQ_EXISTS.with(|c| c.set(c.get() + 1)),
            "eq-choice" => EQ_CHOICE.with(|c| c.set(c.get() + 1)),
            "dead-end" => DEAD_END.with(|c| c.set(c.get() + 1)),
            "cycle" => CYCLE.with(|c| c.set(c.get() + 1)),
            "ifz-beta" => IFZ_BETA.with(|c| c.set(c.get() + 1)),
            "match-beta" => MATCH_BETA.with(|c| c.set(c.get() + 1)),
            "case-beta" => CASE_BETA.with(|c| c.set(c.get() + 1)),
            "force-beta" => FORCE_BETA.with(|c| c.set(c.get() + 1)),
            "dead-bind" => DEAD_BIND.with(|c| c.set(c.get() + 1)),
            "bind-eta" => BIND_ETA.with(|c| c.set(c.get() + 1)),
            "lam-beta" => LAM_BETA.with(|c| c.set(c.get() + 1)),
            _ => {}
        }
    }
    pub fn report() {
        let rules = [
            ("app-bind", &APP_BIND),
            ("lam-choice", &LAM_CHOICE),
            ("lam-exists", &LAM_EXISTS),
            ("lam-equate", &LAM_EQUATE),
            ("eq-exists", &EQ_EXISTS),
            ("eq-choice", &EQ_CHOICE),
            ("dead-end", &DEAD_END),
            ("cycle", &CYCLE),
            ("ifz-beta", &IFZ_BETA),
            ("match-beta", &MATCH_BETA),
            ("case-beta", &CASE_BETA),
            ("force-beta", &FORCE_BETA),
            ("dead-bind", &DEAD_BIND),
            ("bind-eta", &BIND_ETA),
            ("lam-beta", &LAM_BETA),
        ];
        let fired: Vec<_> = rules
            .iter()
            .filter_map(|(name, cell)| {
                let n = cell.with(|c| c.get());
                if n > 0 {
                    Some(format!("{name}={n}"))
                } else {
                    None
                }
            })
            .collect();
        if !fired.is_empty() {
            eprintln!("[opt] rules: {}", fired.join(", "));
        }
        // reset
        for (_, cell) in &rules {
            cell.with(|c| c.set(0));
        }
    }
}

// --- Structural equality ---
// Term handles are not pointer-unique, so deep equality must follow the heap.

fn val_eq(heap: &Heap, a: NodeId, b: NodeId) -> bool {
    match (heap.val(a), heap.val(b)) {
        (MValue::Var(i), MValue::Var(j)) => i == j,
        (MValue::Unit, MValue::Unit)
        | (MValue::Zero, MValue::Zero)
        | (MValue::Nil, MValue::Nil) => true,
        (MValue::Nat(i), MValue::Nat(j)) => i == j,
        (MValue::Succ(x), MValue::Succ(y))
        | (MValue::Inl(x), MValue::Inl(y))
        | (MValue::Inr(x), MValue::Inr(y)) => val_eq(heap, x, y),
        (MValue::Pair(x1, x2), MValue::Pair(y1, y2))
        | (MValue::Cons(x1, x2), MValue::Cons(y1, y2)) => {
            val_eq(heap, x1, y1) && val_eq(heap, x2, y2)
        }
        (MValue::Thunk(c), MValue::Thunk(d)) => comp_eq(heap, c, d),
        _ => false,
    }
}

fn comp_eq(heap: &Heap, a: CompId, b: CompId) -> bool {
    match (heap.comp(a), heap.comp(b)) {
        (MComputation::Return(x), MComputation::Return(y))
        | (MComputation::Force(x), MComputation::Force(y)) => val_eq(heap, *x, *y),
        (
            MComputation::Bind { comp: c1, cont: k1 },
            MComputation::Bind { comp: c2, cont: k2 },
        ) => comp_eq(heap, *c1, *c2) && comp_eq(heap, *k1, *k2),
        (
            MComputation::Need { comp: c1, cont: k1 },
            MComputation::Need { comp: c2, cont: k2 },
        ) => comp_eq(heap, *c1, *c2) && comp_eq(heap, *k1, *k2),
        (MComputation::Lambda { body: b1 }, MComputation::Lambda { body: b2 })
        | (MComputation::Rec { body: b1 }, MComputation::Rec { body: b2 }) => {
            comp_eq(heap, *b1, *b2)
        }
        (MComputation::App { op: o1, arg: a1 }, MComputation::App { op: o2, arg: a2 }) => {
            comp_eq(heap, *o1, *o2) && val_eq(heap, *a1, *a2)
        }
        (MComputation::Choice(c1), MComputation::Choice(c2)) => {
            c1.len() == c2.len()
                && c1.iter().zip(c2.iter()).all(|(x, y)| comp_eq(heap, *x, *y))
        }
        (
            MComputation::Exists { ptype: p1, body: b1 },
            MComputation::Exists { ptype: p2, body: b2 },
        ) => p1 == p2 && comp_eq(heap, *b1, *b2),
        (
            MComputation::Equate { lhs: l1, rhs: r1, body: b1 },
            MComputation::Equate { lhs: l2, rhs: r2, body: b2 },
        ) => val_eq(heap, *l1, *l2) && val_eq(heap, *r1, *r2) && comp_eq(heap, *b1, *b2),
        (
            MComputation::Ifz { num: n1, zk: z1, sk: s1 },
            MComputation::Ifz { num: n2, zk: z2, sk: s2 },
        ) => val_eq(heap, *n1, *n2) && comp_eq(heap, *z1, *z2) && comp_eq(heap, *s1, *s2),
        (
            MComputation::Match { list: l1, nilk: n1, consk: c1 },
            MComputation::Match { list: l2, nilk: n2, consk: c2 },
        ) => val_eq(heap, *l1, *l2) && comp_eq(heap, *n1, *n2) && comp_eq(heap, *c1, *c2),
        (
            MComputation::Case { sum: s1, inlk: i1, inrk: r1 },
            MComputation::Case { sum: s2, inlk: i2, inrk: r2 },
        ) => val_eq(heap, *s1, *s2) && comp_eq(heap, *i1, *i2) && comp_eq(heap, *r1, *r2),
        _ => false,
    }
}

// --- Generic binder-aware traversal ---
// map_val/map_comp rebuild the term, rewriting each Var leaf via `f`, which is
// given the number of binders crossed from the traversal root to that leaf.
// The per-binder depth table (which binders bind, and by how much) lives here once.

fn map_val(
    heap: &mut Heap,
    val: NodeId,
    binders: usize,
    f: &dyn Fn(&mut Heap, usize, NodeId) -> NodeId,
) -> NodeId {
    match heap.val(val) {
        MValue::Var(_) => f(heap, binders, val),
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => val,
        MValue::Succ(v) => {
            let nv = map_val(heap, v, binders, f);
            heap.alloc_imm_val(MValue::Succ(nv))
        }
        MValue::Pair(a, b) => {
            let na = map_val(heap, a, binders, f);
            let nb = map_val(heap, b, binders, f);
            heap.alloc_imm_val(MValue::Pair(na, nb))
        }
        MValue::Inl(v) => {
            let nv = map_val(heap, v, binders, f);
            heap.alloc_imm_val(MValue::Inl(nv))
        }
        MValue::Inr(v) => {
            let nv = map_val(heap, v, binders, f);
            heap.alloc_imm_val(MValue::Inr(nv))
        }
        MValue::Cons(h, t) => {
            let nh = map_val(heap, h, binders, f);
            let nt = map_val(heap, t, binders, f);
            heap.alloc_imm_val(MValue::Cons(nh, nt))
        }
        MValue::Thunk(c) => {
            let nc = map_comp(heap, c, binders, f);
            heap.alloc_imm_val(MValue::Thunk(nc))
        }
    }
}

fn map_comp(
    heap: &mut Heap,
    comp: CompId,
    binders: usize,
    f: &dyn Fn(&mut Heap, usize, NodeId) -> NodeId,
) -> CompId {
    match heap.comp(comp) {
        MComputation::Return(v) => {
            let v = *v;
            let nv = map_val(heap, v, binders, f);
            heap.alloc_comp(MComputation::Return(nv))
        }
        MComputation::Bind { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            let nc = map_comp(heap, c, binders, f);
            let nk = map_comp(heap, cont, binders + 1, f);
            heap.alloc_comp(MComputation::Bind { comp: nc, cont: nk })
        }
        MComputation::Need { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            let nc = map_comp(heap, c, binders, f);
            let nk = map_comp(heap, cont, binders + 1, f);
            heap.alloc_comp(MComputation::Need { comp: nc, cont: nk })
        }
        MComputation::Force(v) => {
            let v = *v;
            let nv = map_val(heap, v, binders, f);
            heap.alloc_comp(MComputation::Force(nv))
        }
        MComputation::Lambda { body } => {
            let body = *body;
            let nb = map_comp(heap, body, binders + 1, f);
            heap.alloc_comp(MComputation::Lambda { body: nb })
        }
        MComputation::App { op, arg } => {
            let (op, arg) = (*op, *arg);
            let no = map_comp(heap, op, binders, f);
            let na = map_val(heap, arg, binders, f);
            heap.alloc_comp(MComputation::App { op: no, arg: na })
        }
        MComputation::Choice(cs) => {
            let cs: Vec<CompId> = cs.iter().copied().collect();
            let mapped: Vec<CompId> = cs.iter().map(|c| map_comp(heap, *c, binders, f)).collect();
            heap.alloc_comp(MComputation::Choice(mapped.into_boxed_slice()))
        }
        MComputation::Exists { ptype, body } => {
            let ptype = ptype.clone();
            let body = *body;
            let nb = map_comp(heap, body, binders + 1, f);
            heap.alloc_comp(MComputation::Exists { ptype, body: nb })
        }
        MComputation::Equate { lhs, rhs, body } => {
            let (lhs, rhs, body) = (*lhs, *rhs, *body);
            let nl = map_val(heap, lhs, binders, f);
            let nr = map_val(heap, rhs, binders, f);
            let nb = map_comp(heap, body, binders, f);
            heap.alloc_comp(MComputation::Equate {
                lhs: nl,
                rhs: nr,
                body: nb,
            })
        }
        MComputation::Ifz { num, zk, sk } => {
            let (num, zk, sk) = (*num, *zk, *sk);
            let nn = map_val(heap, num, binders, f);
            let nz = map_comp(heap, zk, binders, f);
            let ns = map_comp(heap, sk, binders + 1, f);
            heap.alloc_comp(MComputation::Ifz {
                num: nn,
                zk: nz,
                sk: ns,
            })
        }
        MComputation::Match { list, nilk, consk } => {
            let (list, nilk, consk) = (*list, *nilk, *consk);
            let nl = map_val(heap, list, binders, f);
            let nn = map_comp(heap, nilk, binders, f);
            let nc = map_comp(heap, consk, binders + 2, f);
            heap.alloc_comp(MComputation::Match {
                list: nl,
                nilk: nn,
                consk: nc,
            })
        }
        MComputation::Case { sum, inlk, inrk } => {
            let (sum, inlk, inrk) = (*sum, *inlk, *inrk);
            let ns = map_val(heap, sum, binders, f);
            let ni = map_comp(heap, inlk, binders + 1, f);
            let nr = map_comp(heap, inrk, binders + 1, f);
            heap.alloc_comp(MComputation::Case {
                sum: ns,
                inlk: ni,
                inrk: nr,
            })
        }
        MComputation::Rec { body } => {
            let body = *body;
            let nb = map_comp(heap, body, binders + 1, f);
            heap.alloc_comp(MComputation::Rec { body: nb })
        }
    }
}

// --- De Bruijn shifting ---

fn shift_val(heap: &mut Heap, val: NodeId, delta: isize, cutoff: usize) -> NodeId {
    map_val(heap, val, cutoff, &move |heap, binders, id| {
        let MValue::Var(i) = heap.val(id) else {
            unreachable!()
        };
        if i >= binders {
            heap.alloc_imm_val(MValue::Var((i as isize + delta) as usize))
        } else {
            id
        }
    })
}

fn shift_comp(heap: &mut Heap, comp: CompId, delta: isize, cutoff: usize) -> CompId {
    if delta == 0 {
        return comp;
    }
    map_comp(heap, comp, cutoff, &move |heap, binders, id| {
        let MValue::Var(i) = heap.val(id) else {
            unreachable!()
        };
        if i >= binders {
            heap.alloc_imm_val(MValue::Var((i as isize + delta) as usize))
        } else {
            id
        }
    })
}

// --- De Bruijn substitution ---
// subst_comp replaces Var(depth) with shift(repl, depth, 0),
// and decrements all Var(i) where i > depth.

fn subst_comp(heap: &mut Heap, comp: CompId, repl: NodeId, depth: usize) -> CompId {
    map_comp(heap, comp, depth, &move |heap, binders, id| {
        let MValue::Var(i) = heap.val(id) else {
            unreachable!()
        };
        if i == binders {
            shift_val(heap, repl, binders as isize, 0)
        } else if i > binders {
            heap.alloc_imm_val(MValue::Var(i - 1))
        } else {
            id
        }
    })
}

// --- Helpers ---

/// Check if a value structurally contains `needle` as a sub-value.
/// Used for cycle detection in equate: `V =:= C[V]` -> fail.
fn val_contains(heap: &Heap, needle: NodeId, haystack: NodeId) -> bool {
    if val_eq(heap, needle, haystack) {
        return true;
    }
    match heap.val(haystack) {
        MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => val_contains(heap, needle, v),
        MValue::Pair(a, b) | MValue::Cons(a, b) => {
            val_contains(heap, needle, a) || val_contains(heap, needle, b)
        }
        _ => false,
    }
}

/// Check if `target` de Bruijn index appears free in a value.
fn has_free_var_val(heap: &Heap, val: NodeId, target: usize) -> bool {
    match heap.val(val) {
        MValue::Var(i) => i == target,
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => false,
        MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => has_free_var_val(heap, v, target),
        MValue::Pair(a, b) | MValue::Cons(a, b) => {
            has_free_var_val(heap, a, target) || has_free_var_val(heap, b, target)
        }
        MValue::Thunk(c) => has_free_var_comp(heap, c, target),
    }
}

fn has_free_var_comp(heap: &Heap, comp: CompId, target: usize) -> bool {
    match heap.comp(comp) {
        MComputation::Return(v) | MComputation::Force(v) => has_free_var_val(heap, *v, target),
        MComputation::Bind { comp: c, cont } => {
            has_free_var_comp(heap, *c, target) || has_free_var_comp(heap, *cont, target + 1)
        }
        MComputation::Need { comp: c, cont } => {
            has_free_var_comp(heap, *c, target) || has_free_var_comp(heap, *cont, target + 1)
        }
        MComputation::Lambda { body }
        | MComputation::Exists { body, .. }
        | MComputation::Rec { body } => has_free_var_comp(heap, *body, target + 1),
        MComputation::App { op, arg } => {
            has_free_var_comp(heap, *op, target) || has_free_var_val(heap, *arg, target)
        }
        MComputation::Choice(cs) => cs.iter().any(|c| has_free_var_comp(heap, *c, target)),
        MComputation::Equate { lhs, rhs, body } => {
            has_free_var_val(heap, *lhs, target)
                || has_free_var_val(heap, *rhs, target)
                || has_free_var_comp(heap, *body, target)
        }
        MComputation::Ifz { num, zk, sk } => {
            has_free_var_val(heap, *num, target)
                || has_free_var_comp(heap, *zk, target)
                || has_free_var_comp(heap, *sk, target + 1)
        }
        MComputation::Match { list, nilk, consk } => {
            has_free_var_val(heap, *list, target)
                || has_free_var_comp(heap, *nilk, target)
                || has_free_var_comp(heap, *consk, target + 2)
        }
        MComputation::Case { sum, inlk, inrk } => {
            has_free_var_val(heap, *sum, target)
                || has_free_var_comp(heap, *inlk, target + 1)
                || has_free_var_comp(heap, *inrk, target + 1)
        }
    }
}

/// Swap two adjacent binders at `depth` and `depth+1`.
fn swap_comp(heap: &mut Heap, comp: CompId, depth: usize) -> CompId {
    map_comp(heap, comp, depth, &move |heap, binders, id| {
        let MValue::Var(i) = heap.val(id) else {
            unreachable!()
        };
        if i == binders {
            heap.alloc_imm_val(MValue::Var(binders + 1))
        } else if i == binders + 1 {
            heap.alloc_imm_val(MValue::Var(binders))
        } else {
            id
        }
    })
}

// --- Optimizer ---

fn is_fail(heap: &Heap, comp: CompId) -> bool {
    matches!(heap.comp(comp), MComputation::Choice(cs) if cs.is_empty())
}

fn fail(heap: &mut Heap) -> CompId {
    heap.alloc_comp(MComputation::Choice(Vec::new().into_boxed_slice()))
}

type Env = Vec<Option<NodeId>>;

fn push_env(env: &[Option<NodeId>], entry: Option<NodeId>) -> Env {
    let mut e = Vec::with_capacity(env.len() + 1);
    e.push(entry);
    e.extend_from_slice(env);
    e
}

/// Recursively resolve all variables in a value through the compile-time env.
/// Used to build fully-concrete env entries for decision-making.
fn deep_resolve(heap: &mut Heap, val: NodeId, env: &[Option<NodeId>]) -> NodeId {
    match heap.val(val) {
        MValue::Var(i) => {
            if let Some(Some(v)) = env.get(i) {
                let v = *v;
                let shifted = shift_val(heap, v, (i as isize) + 1, 0);
                deep_resolve(heap, shifted, env)
            } else {
                val
            }
        }
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => val,
        MValue::Succ(v) => {
            let nv = deep_resolve(heap, v, env);
            heap.alloc_imm_val(MValue::Succ(nv))
        }
        MValue::Pair(a, b) => {
            let na = deep_resolve(heap, a, env);
            let nb = deep_resolve(heap, b, env);
            heap.alloc_imm_val(MValue::Pair(na, nb))
        }
        MValue::Inl(v) => {
            let nv = deep_resolve(heap, v, env);
            heap.alloc_imm_val(MValue::Inl(nv))
        }
        MValue::Inr(v) => {
            let nv = deep_resolve(heap, v, env);
            heap.alloc_imm_val(MValue::Inr(nv))
        }
        MValue::Cons(h, t) => {
            let nh = deep_resolve(heap, h, env);
            let nt = deep_resolve(heap, t, env);
            heap.alloc_imm_val(MValue::Cons(nh, nt))
        }
        MValue::Thunk(_) => val,
    }
}

fn opt_val(heap: &mut Heap, val: NodeId, env: &[Option<NodeId>]) -> NodeId {
    match heap.val(val) {
        MValue::Thunk(c) => {
            let nc = opt_comp_env(heap, c, env);
            heap.alloc_imm_val(MValue::Thunk(nc))
        }
        MValue::Succ(v) => {
            let nv = opt_val(heap, v, env);
            heap.alloc_imm_val(MValue::Succ(nv))
        }
        MValue::Pair(a, b) => {
            let na = opt_val(heap, a, env);
            let nb = opt_val(heap, b, env);
            heap.alloc_imm_val(MValue::Pair(na, nb))
        }
        MValue::Inl(v) => {
            let nv = opt_val(heap, v, env);
            heap.alloc_imm_val(MValue::Inl(nv))
        }
        MValue::Inr(v) => {
            let nv = opt_val(heap, v, env);
            heap.alloc_imm_val(MValue::Inr(nv))
        }
        MValue::Cons(h, t) => {
            let nh = opt_val(heap, h, env);
            let nt = opt_val(heap, t, env);
            heap.alloc_imm_val(MValue::Cons(nh, nt))
        }
        _ => val,
    }
}

fn opt_comp(heap: &mut Heap, comp: CompId) -> CompId {
    opt_comp_env(heap, comp, &[])
}

fn opt_comp_env(heap: &mut Heap, comp: CompId, env: &[Option<NodeId>]) -> CompId {
    let rebuilt = opt_subterms(heap, comp, env);
    rewrite(heap, rebuilt, env)
}

fn opt_subterms(heap: &mut Heap, comp: CompId, env: &[Option<NodeId>]) -> CompId {
    match heap.comp(comp) {
        MComputation::Return(v) => {
            let v = *v;
            let nv = opt_val(heap, v, env);
            heap.alloc_comp(MComputation::Return(nv))
        }
        MComputation::Bind { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            let oc = opt_comp_env(heap, c, env);
            let entry = if let MComputation::Return(v) = heap.comp(oc) {
                let v = *v;
                Some(deep_resolve(heap, v, env))
            } else {
                None
            };
            let cenv = push_env(env, entry);
            let ncont = opt_comp_env(heap, cont, &cenv);
            heap.alloc_comp(MComputation::Bind {
                comp: oc,
                cont: ncont,
            })
        }
        MComputation::Need { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            let oc = opt_comp_env(heap, c, env);
            let entry = if let MComputation::Return(v) = heap.comp(oc) {
                let v = *v;
                Some(deep_resolve(heap, v, env))
            } else {
                None
            };
            let cenv = push_env(env, entry);
            let ncont = opt_comp_env(heap, cont, &cenv);
            heap.alloc_comp(MComputation::Need {
                comp: oc,
                cont: ncont,
            })
        }
        MComputation::Force(v) => {
            let v = *v;
            let nv = opt_val(heap, v, env);
            heap.alloc_comp(MComputation::Force(nv))
        }
        MComputation::Lambda { body } => {
            let body = *body;
            let nb = opt_comp_env(heap, body, &push_env(env, None));
            heap.alloc_comp(MComputation::Lambda { body: nb })
        }
        MComputation::App { op, arg } => {
            let (op, arg) = (*op, *arg);
            let no = opt_comp_env(heap, op, env);
            let na = opt_val(heap, arg, env);
            heap.alloc_comp(MComputation::App { op: no, arg: na })
        }
        MComputation::Choice(cs) => {
            let cs: Vec<CompId> = cs.iter().copied().collect();
            let optimized: Vec<CompId> = cs.iter().map(|c| opt_comp_env(heap, *c, env)).collect();
            heap.alloc_comp(MComputation::Choice(optimized.into_boxed_slice()))
        }
        MComputation::Exists { ptype, body } => {
            let ptype = ptype.clone();
            let body = *body;
            let nb = opt_comp_env(heap, body, &push_env(env, None));
            heap.alloc_comp(MComputation::Exists { ptype, body: nb })
        }
        MComputation::Equate { lhs, rhs, body } => {
            let (lhs, rhs, body) = (*lhs, *rhs, *body);
            let nl = opt_val(heap, lhs, env);
            let nr = opt_val(heap, rhs, env);
            let nb = opt_comp_env(heap, body, env);
            heap.alloc_comp(MComputation::Equate {
                lhs: nl,
                rhs: nr,
                body: nb,
            })
        }
        MComputation::Ifz { num, zk, sk } => {
            let (num, zk, sk) = (*num, *zk, *sk);
            let nn = opt_val(heap, num, env);
            let nz = opt_comp_env(heap, zk, env);
            let ns = opt_comp_env(heap, sk, &push_env(env, None));
            heap.alloc_comp(MComputation::Ifz {
                num: nn,
                zk: nz,
                sk: ns,
            })
        }
        MComputation::Match { list, nilk, consk } => {
            let (list, nilk, consk) = (*list, *nilk, *consk);
            let nl = opt_val(heap, list, env);
            let nn = opt_comp_env(heap, nilk, env);
            let nc = opt_comp_env(heap, consk, &push_env(&push_env(env, None), None));
            heap.alloc_comp(MComputation::Match {
                list: nl,
                nilk: nn,
                consk: nc,
            })
        }
        MComputation::Case { sum, inlk, inrk } => {
            let (sum, inlk, inrk) = (*sum, *inlk, *inrk);
            let ns = opt_val(heap, sum, env);
            let ni = opt_comp_env(heap, inlk, &push_env(env, None));
            let nr = opt_comp_env(heap, inrk, &push_env(env, None));
            heap.alloc_comp(MComputation::Case {
                sum: ns,
                inlk: ni,
                inrk: nr,
            })
        }
        MComputation::Rec { body } => {
            let body = *body;
            let nb = opt_comp_env(heap, body, &push_env(env, None));
            heap.alloc_comp(MComputation::Rec { body: nb })
        }
    }
}

/// Try rewrite rules at the top level. If a rewrite fires, re-optimize the result.
fn rewrite(heap: &mut Heap, comp: CompId, env: &[Option<NodeId>]) -> CompId {
    match heap.comp(comp) {
        // Bind rules:
        // fail to x. M  -->  fail
        // eta: M to x. return x  -->  M
        // dead-bind: return V to x. M  -->  M↓  (when x not in FV(M))
        // dead-end: M to x. fail  -->  fail
        // bind-assoc, pull-choice, pull-exists, pull-equate
        MComputation::Bind { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            if let MComputation::Return(v) = heap.comp(c) {
                let v = *v;
                // eta: return V to x. return x -> return V
                if let MComputation::Return(rv) = heap.comp(cont) {
                    if matches!(heap.val(*rv), MValue::Var(0)) {
                        #[cfg(feature = "opt-stats")]
                        stats::bump("bind-eta");
                        return c;
                    }
                }
                // dead-bind: cont doesn't use Var(0) -> drop the bind
                if !has_free_var_comp(heap, cont, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("dead-bind");
                    return shift_comp(heap, cont, -1, 0);
                }
                // Variable aliasing: Bind { Return(Var(i)), cont } is just renaming
                if matches!(heap.val(v), MValue::Var(_)) {
                    let s = subst_comp(heap, cont, v, 0);
                    return opt_comp_env(heap, s, env);
                }
            }
            if is_fail(heap, c) {
                return fail(heap);
            }
            // eta for non-Return c
            if let MComputation::Return(rv) = heap.comp(cont) {
                if matches!(heap.val(*rv), MValue::Var(0)) {
                    return c;
                }
            }
            // Dead-End: M to x. fail  -->  fail
            if is_fail(heap, cont) {
                #[cfg(feature = "opt-stats")]
                stats::bump("dead-end");
                return fail(heap);
            }
            // Bind-assoc: (M to x. N) to y. P -> M to x. (N to y'. P')
            if let MComputation::Bind {
                comp: inner_c,
                cont: inner_k,
            } = heap.comp(c)
            {
                let (inner_c, inner_k) = (*inner_c, *inner_k);
                let assoc = match heap.comp(inner_k) {
                    MComputation::Return(_)
                    | MComputation::Exists { .. }
                    | MComputation::Equate { .. } => true,
                    MComputation::Choice(branches) => !branches.is_empty(),
                    _ => false,
                };
                if assoc {
                    let shifted_cont = shift_comp(heap, cont, 1, 1);
                    let new_inner = heap.alloc_comp(MComputation::Bind {
                        comp: inner_k,
                        cont: shifted_cont,
                    });
                    let new_outer = heap.alloc_comp(MComputation::Bind {
                        comp: inner_c,
                        cont: new_inner,
                    });
                    return opt_comp_env(heap, new_outer, env);
                }
            }
            // Pull-Choice
            if let MComputation::Choice(branches) = heap.comp(c) {
                if !branches.is_empty() {
                    let branches: Vec<CompId> = branches.iter().copied().collect();
                    let new_branches: Vec<CompId> = branches
                        .iter()
                        .map(|b| heap.alloc_comp(MComputation::Bind { comp: *b, cont }))
                        .collect();
                    let choice =
                        heap.alloc_comp(MComputation::Choice(new_branches.into_boxed_slice()));
                    return opt_comp_env(heap, choice, env);
                }
            }
            // Pull-Exists
            if let MComputation::Exists { ptype, body } = heap.comp(c) {
                let ptype = ptype.clone();
                let body = *body;
                let shifted_cont = shift_comp(heap, cont, 1, 1);
                let new_bind = heap.alloc_comp(MComputation::Bind {
                    comp: body,
                    cont: shifted_cont,
                });
                let new_exists = heap.alloc_comp(MComputation::Exists {
                    ptype,
                    body: new_bind,
                });
                return opt_comp_env(heap, new_exists, env);
            }
            // Pull-Equate
            if let MComputation::Equate { lhs, rhs, body } = heap.comp(c) {
                let (lhs, rhs, body) = (*lhs, *rhs, *body);
                let new_bind = heap.alloc_comp(MComputation::Bind { comp: body, cont });
                let new_equate = heap.alloc_comp(MComputation::Equate {
                    lhs,
                    rhs,
                    body: new_bind,
                });
                return opt_comp_env(heap, new_equate, env);
            }
            comp
        }
        // Need rules (like Bind but always lazy):
        // fail need x. M  -->  fail
        // dead-bind: return V need x. M  -->  M↓  (when x not in FV(M))
        // dead-end: M need x. fail  -->  fail
        MComputation::Need { comp: c, cont } => {
            let (c, cont) = (*c, *cont);
            if let MComputation::Return(v) = heap.comp(c) {
                let v = *v;
                // dead-bind: cont doesn't use Var(0) -> drop the need
                if !has_free_var_comp(heap, cont, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("dead-bind");
                    return shift_comp(heap, cont, -1, 0);
                }
            }
            if is_fail(heap, c) {
                return fail(heap);
            }
            // Dead-End: M need x. fail  -->  fail
            if is_fail(heap, cont) {
                #[cfg(feature = "opt-stats")]
                stats::bump("dead-end");
                return fail(heap);
            }
            comp
        }

        // force(thunk M)  -->  M  (resolve through env)
        MComputation::Force(v) => {
            let v = *v;
            let resolved = deep_resolve(heap, v, env);
            if let MValue::Thunk(c) = heap.val(resolved) {
                #[cfg(feature = "opt-stats")]
                stats::bump("force-beta");
                return opt_comp_env(heap, c, env);
            }
            comp
        }

        // (lam x. M)(V)  -->  M[V/x]
        // app-bind: (M to x. N)(V)  -->  M to x. N(V)
        MComputation::App { op, arg } => {
            let (op, arg) = (*op, *arg);
            if let MComputation::Lambda { body } = heap.comp(op) {
                let body = *body;
                #[cfg(feature = "opt-stats")]
                stats::bump("lam-beta");
                let s = subst_comp(heap, body, arg, 0);
                return opt_comp_env(heap, s, env);
            }
            if let MComputation::Bind { comp: c, cont } = heap.comp(op) {
                let (c, cont) = (*c, *cont);
                #[cfg(feature = "opt-stats")]
                stats::bump("app-bind");
                let shifted_arg = shift_val(heap, arg, 1, 0);
                let new_app = heap.alloc_comp(MComputation::App {
                    op: cont,
                    arg: shifted_arg,
                });
                let new_bind = heap.alloc_comp(MComputation::Bind {
                    comp: c,
                    cont: new_app,
                });
                return opt_comp_env(heap, new_bind, env);
            }
            if let MComputation::Need { comp: c, cont } = heap.comp(op) {
                let (c, cont) = (*c, *cont);
                #[cfg(feature = "opt-stats")]
                stats::bump("app-need");
                let shifted_arg = shift_val(heap, arg, 1, 0);
                let new_app = heap.alloc_comp(MComputation::App {
                    op: cont,
                    arg: shifted_arg,
                });
                let new_need = heap.alloc_comp(MComputation::Need {
                    comp: c,
                    cont: new_app,
                });
                return opt_comp_env(heap, new_need, env);
            }
            comp
        }

        // Choice: flatten nested choices, remove fail branches, unwrap singletons
        MComputation::Choice(cs) => {
            let cs: Vec<CompId> = cs.iter().copied().collect();
            let mut flat: Vec<CompId> = Vec::new();
            let mut changed = false;
            for c in cs {
                match heap.comp(c) {
                    MComputation::Choice(inner) => {
                        changed = true;
                        let inner: Vec<CompId> = inner.iter().copied().collect();
                        for ic in inner {
                            if !is_fail(heap, ic) {
                                flat.push(ic);
                            }
                        }
                    }
                    _ if is_fail(heap, c) => {
                        changed = true;
                    }
                    _ => {
                        flat.push(c);
                    }
                }
            }
            if !changed {
                return comp;
            }
            match flat.len() {
                0 => fail(heap),
                1 => flat[0],
                _ => heap.alloc_comp(MComputation::Choice(flat.into_boxed_slice())),
            }
        }

        // exists fail  -->  fail
        MComputation::Exists { body, .. } => {
            let body = *body;
            if is_fail(heap, body) {
                return fail(heap);
            }
            comp
        }

        // equate rules: reflexivity, cycle, parameter laws, etc.
        MComputation::Equate { lhs, rhs, body } => {
            let (lhs, rhs, body) = (*lhs, *rhs, *body);
            if is_fail(heap, body) {
                return fail(heap);
            }
            // Resolve through env so parameter laws can see constructors
            let rlhs = deep_resolve(heap, lhs, env);
            let rrhs = deep_resolve(heap, rhs, env);
            if val_eq(heap, rlhs, rrhs) {
                return body;
            }
            if val_contains(heap, rlhs, rrhs) || val_contains(heap, rrhs, rlhs) {
                #[cfg(feature = "opt-stats")]
                stats::bump("cycle");
                return fail(heap);
            }
            if let MComputation::Exists { ptype, body: ebody } = heap.comp(body) {
                let ptype = ptype.clone();
                let ebody = *ebody;
                #[cfg(feature = "opt-stats")]
                stats::bump("eq-exists");
                let slhs = shift_val(heap, lhs, 1, 0);
                let srhs = shift_val(heap, rhs, 1, 0);
                let new_equate = heap.alloc_comp(MComputation::Equate {
                    lhs: slhs,
                    rhs: srhs,
                    body: ebody,
                });
                let new_exists = heap.alloc_comp(MComputation::Exists {
                    ptype,
                    body: new_equate,
                });
                return opt_comp_env(heap, new_exists, env);
            }
            if let MComputation::Choice(branches) = heap.comp(body) {
                if !branches.is_empty() {
                    let branches: Vec<CompId> = branches.iter().copied().collect();
                    #[cfg(feature = "opt-stats")]
                    stats::bump("eq-choice");
                    let new_branches: Vec<CompId> = branches
                        .iter()
                        .map(|b| heap.alloc_comp(MComputation::Equate { lhs, rhs, body: *b }))
                        .collect();
                    let choice =
                        heap.alloc_comp(MComputation::Choice(new_branches.into_boxed_slice()));
                    return opt_comp_env(heap, choice, env);
                }
            }
            match (heap.val(rlhs), heap.val(rrhs)) {
                (MValue::Succ(v), MValue::Succ(w)) => {
                    let new_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: v,
                        rhs: w,
                        body,
                    });
                    return opt_comp_env(heap, new_equate, env);
                }
                (MValue::Succ(_), MValue::Zero) | (MValue::Zero, MValue::Succ(_)) => {
                    return fail(heap);
                }
                (MValue::Cons(v1, w1), MValue::Cons(v2, w2)) => {
                    let inner_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: w1,
                        rhs: w2,
                        body,
                    });
                    let outer_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: v1,
                        rhs: v2,
                        body: inner_equate,
                    });
                    return opt_comp_env(heap, outer_equate, env);
                }
                (MValue::Cons(..), MValue::Nil) | (MValue::Nil, MValue::Cons(..)) => {
                    return fail(heap);
                }
                (MValue::Pair(v1, v2), MValue::Pair(w1, w2)) => {
                    let inner_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: v2,
                        rhs: w2,
                        body,
                    });
                    let outer_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: v1,
                        rhs: w1,
                        body: inner_equate,
                    });
                    return opt_comp_env(heap, outer_equate, env);
                }
                (MValue::Inl(v), MValue::Inl(w)) | (MValue::Inr(v), MValue::Inr(w)) => {
                    let new_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: v,
                        rhs: w,
                        body,
                    });
                    return opt_comp_env(heap, new_equate, env);
                }
                (MValue::Inl(_), MValue::Inr(_)) | (MValue::Inr(_), MValue::Inl(_)) => {
                    return fail(heap);
                }
                _ => {}
            }
            comp
        }

        // lam x. fail  -->  fail
        // lam x. (M || N)  -->  (lam x. M) || (lam x. N)
        // lam x. (exists z:s. M)  -->  exists z:s. (lam x. M')  [swap binders]
        // lam x. (V =:= W. M)  -->  V' =:= W'. (lam x. M)  [if V,W don't ref x]
        MComputation::Lambda { body } => {
            let body = *body;
            if is_fail(heap, body) {
                return fail(heap);
            }
            if let MComputation::Choice(branches) = heap.comp(body) {
                if !branches.is_empty() {
                    let branches: Vec<CompId> = branches.iter().copied().collect();
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-choice");
                    let new_branches: Vec<CompId> = branches
                        .iter()
                        .map(|b| heap.alloc_comp(MComputation::Lambda { body: *b }))
                        .collect();
                    let choice =
                        heap.alloc_comp(MComputation::Choice(new_branches.into_boxed_slice()));
                    return opt_comp_env(heap, choice, env);
                }
            }
            if let MComputation::Exists { ptype, body: ebody } = heap.comp(body) {
                let ptype = ptype.clone();
                let ebody = *ebody;
                #[cfg(feature = "opt-stats")]
                stats::bump("lam-exists");
                let swapped = swap_comp(heap, ebody, 0);
                let new_lam = heap.alloc_comp(MComputation::Lambda { body: swapped });
                let new_exists = heap.alloc_comp(MComputation::Exists {
                    ptype,
                    body: new_lam,
                });
                return opt_comp_env(heap, new_exists, env);
            }
            if let MComputation::Equate {
                lhs,
                rhs,
                body: ebody,
            } = heap.comp(body)
            {
                let (lhs, rhs, ebody) = (*lhs, *rhs, *ebody);
                if !has_free_var_val(heap, lhs, 0) && !has_free_var_val(heap, rhs, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-equate");
                    let new_lam = heap.alloc_comp(MComputation::Lambda { body: ebody });
                    let slhs = shift_val(heap, lhs, -1, 0);
                    let srhs = shift_val(heap, rhs, -1, 0);
                    let new_equate = heap.alloc_comp(MComputation::Equate {
                        lhs: slhs,
                        rhs: srhs,
                        body: new_lam,
                    });
                    return opt_comp_env(heap, new_equate, env);
                }
            }
            comp
        }

        // ifz(num, zk, n.sk): resolve num through env, then subst
        MComputation::Ifz { num, zk, sk } => {
            let (num, zk, sk) = (*num, *zk, *sk);
            let resolved = deep_resolve(heap, num, env);
            match heap.val(resolved) {
                MValue::Zero => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("ifz-beta");
                    zk
                }
                MValue::Succ(pred) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("ifz-beta");
                    let s = subst_comp(heap, sk, pred, 0);
                    opt_comp_env(heap, s, env)
                }
                _ => comp,
            }
        }

        // match(list, nilk, x.xs.consk): resolve list through env, then subst
        MComputation::Match { list, nilk, consk } => {
            let (list, nilk, consk) = (*list, *nilk, *consk);
            let resolved = deep_resolve(heap, list, env);
            match heap.val(resolved) {
                MValue::Nil => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("match-beta");
                    nilk
                }
                MValue::Cons(head, tail) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("match-beta");
                    let step1 = subst_comp(heap, consk, tail, 0);
                    let step2 = subst_comp(heap, step1, head, 0);
                    opt_comp_env(heap, step2, env)
                }
                _ => comp,
            }
        }

        // case(sum, x.inlk, y.inrk): resolve sum through env, then subst
        MComputation::Case { sum, inlk, inrk } => {
            let (sum, inlk, inrk) = (*sum, *inlk, *inrk);
            let resolved = deep_resolve(heap, sum, env);
            match heap.val(resolved) {
                MValue::Inl(v) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("case-beta");
                    let s = subst_comp(heap, inlk, v, 0);
                    opt_comp_env(heap, s, env)
                }
                MValue::Inr(v) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("case-beta");
                    let s = subst_comp(heap, inrk, v, 0);
                    opt_comp_env(heap, s, env)
                }
                _ => comp,
            }
        }

        _ => comp,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::value_type::ValueType;

    fn imm(heap: &mut Heap, v: MValue) -> NodeId {
        heap.alloc_imm_val(v)
    }

    fn ret(heap: &mut Heap, v: NodeId) -> CompId {
        heap.alloc_comp(MComputation::Return(v))
    }

    fn bind(heap: &mut Heap, c: CompId, k: CompId) -> CompId {
        heap.alloc_comp(MComputation::Bind { comp: c, cont: k })
    }

    fn fail_comp(heap: &mut Heap) -> CompId {
        heap.alloc_comp(MComputation::Choice(Vec::new().into_boxed_slice()))
    }

    fn choice(heap: &mut Heap, branches: Vec<CompId>) -> CompId {
        heap.alloc_comp(MComputation::Choice(branches.into_boxed_slice()))
    }

    /// `return (succ (var i))`.
    fn ret_succ_var(heap: &mut Heap, i: usize) -> CompId {
        let v = imm(heap, MValue::Var(i));
        let s = imm(heap, MValue::Succ(v));
        ret(heap, s)
    }

    /// `return (var i)`.
    fn ret_var(heap: &mut Heap, i: usize) -> CompId {
        let v = imm(heap, MValue::Var(i));
        ret(heap, v)
    }

    /// `return zero`.
    fn ret_zero(heap: &mut Heap) -> CompId {
        let z = imm(heap, MValue::Zero);
        ret(heap, z)
    }

    #[test]
    fn bind_return_beta() {
        let mut heap = Heap::new();
        // (return 0) to x. return (succ x) -- env approach keeps bind
        let z = ret_zero(&mut heap);
        let s = ret_succ_var(&mut heap, 0);
        let term = bind(&mut heap, z, s);
        let result = opt_comp(&mut heap, term);
        let ez = ret_zero(&mut heap);
        let es = ret_succ_var(&mut heap, 0);
        let expected = bind(&mut heap, ez, es);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn bind_return_chain() {
        let mut heap = Heap::new();
        // (return 0) to x. (return x) to y. return (succ y)
        // var-alias eliminates inner bind: (return 0) to x. return (succ x)
        let z = ret_zero(&mut heap);
        let inner_ret = ret_var(&mut heap, 0);
        let inner_succ = ret_succ_var(&mut heap, 0);
        let inner = bind(&mut heap, inner_ret, inner_succ);
        let term = bind(&mut heap, z, inner);
        let result = opt_comp(&mut heap, term);
        let ez = ret_zero(&mut heap);
        let es = ret_succ_var(&mut heap, 0);
        let expected = bind(&mut heap, ez, es);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn force_thunk_beta() {
        let mut heap = Heap::new();
        // force(thunk(return 0)) --> return 0
        let inner = ret_zero(&mut heap);
        let thunk = imm(&mut heap, MValue::Thunk(inner));
        let term = heap.alloc_comp(MComputation::Force(thunk));
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, inner));
    }

    #[test]
    fn fail_to_is_fail() {
        let mut heap = Heap::new();
        // fail to x. M --> fail
        let f = fail_comp(&mut heap);
        let s = ret_succ_var(&mut heap, 0);
        let term = bind(&mut heap, f, s);
        let result = opt_comp(&mut heap, term);
        assert!(is_fail(&heap, result));
    }

    #[test]
    fn choice_removes_fail_branches() {
        let mut heap = Heap::new();
        // (fail [] return 0) --> return 0
        let fail_branch = fail_comp(&mut heap);
        let ret_branch = ret_zero(&mut heap);
        let term = choice(&mut heap, vec![fail_branch, ret_branch]);
        let result = opt_comp(&mut heap, term);
        let expected = ret_zero(&mut heap);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn bind_return_eta() {
        let mut heap = Heap::new();
        // M to x. return x --> M
        let m = ret_zero(&mut heap);
        let rv = ret_var(&mut heap, 0);
        let term = bind(&mut heap, m, rv);
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, m));
    }

    #[test]
    fn exists_fail() {
        let mut heap = Heap::new();
        let body = fail_comp(&mut heap);
        let term = heap.alloc_comp(MComputation::Exists {
            ptype: ValueType::Nat,
            body,
        });
        let result = opt_comp(&mut heap, term);
        assert!(is_fail(&heap, result));
    }

    #[test]
    fn equate_refl() {
        let mut heap = Heap::new();
        let v = imm(&mut heap, MValue::Zero);
        let inner = imm(&mut heap, MValue::Zero);
        let succ = imm(&mut heap, MValue::Succ(inner));
        let body = ret(&mut heap, succ);
        let term = heap.alloc_comp(MComputation::Equate { lhs: v, rhs: v, body });
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, body));
    }

    #[test]
    fn ifz_zero_beta() {
        let mut heap = Heap::new();
        let nil = imm(&mut heap, MValue::Nil);
        let zk = ret(&mut heap, nil);
        let sk = ret_succ_var(&mut heap, 0);
        let num = imm(&mut heap, MValue::Zero);
        let term = heap.alloc_comp(MComputation::Ifz { num, zk, sk });
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, zk));
    }

    #[test]
    fn ifz_succ_beta() {
        let mut heap = Heap::new();
        // ifz(succ(0), zk, n. return (succ n)) --> return (succ 0)
        let zero = imm(&mut heap, MValue::Zero);
        let num = imm(&mut heap, MValue::Succ(zero));
        let nil = imm(&mut heap, MValue::Nil);
        let zk = ret(&mut heap, nil);
        let sk = ret_succ_var(&mut heap, 0);
        let term = heap.alloc_comp(MComputation::Ifz { num, zk, sk });
        let result = opt_comp(&mut heap, term);
        let ez = imm(&mut heap, MValue::Zero);
        let es = imm(&mut heap, MValue::Succ(ez));
        let expected = ret(&mut heap, es);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn match_nil_beta() {
        let mut heap = Heap::new();
        let z = imm(&mut heap, MValue::Zero);
        let nilk = ret(&mut heap, z);
        let v1 = imm(&mut heap, MValue::Var(1));
        let v0 = imm(&mut heap, MValue::Var(0));
        let pair = imm(&mut heap, MValue::Pair(v1, v0));
        let consk = ret(&mut heap, pair);
        let list = imm(&mut heap, MValue::Nil);
        let term = heap.alloc_comp(MComputation::Match { list, nilk, consk });
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, nilk));
    }

    #[test]
    fn match_cons_beta() {
        let mut heap = Heap::new();
        // match(cons(0, nil), nilk, x.xs. return (x, xs)) --> return (0, nil)
        let z = imm(&mut heap, MValue::Zero);
        let nil = imm(&mut heap, MValue::Nil);
        let list = imm(&mut heap, MValue::Cons(z, nil));
        let nz = imm(&mut heap, MValue::Nil);
        let nilk = ret(&mut heap, nz);
        let v1 = imm(&mut heap, MValue::Var(1));
        let v0 = imm(&mut heap, MValue::Var(0));
        let pair = imm(&mut heap, MValue::Pair(v1, v0));
        let consk = ret(&mut heap, pair);
        let term = heap.alloc_comp(MComputation::Match { list, nilk, consk });
        let result = opt_comp(&mut heap, term);
        let ez = imm(&mut heap, MValue::Zero);
        let enil = imm(&mut heap, MValue::Nil);
        let epair = imm(&mut heap, MValue::Pair(ez, enil));
        let expected = ret(&mut heap, epair);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn nested_bind_return_succ_succ() {
        let mut heap = Heap::new();
        // (return x) to a. (return (succ a)) to b. return (succ b)
        // var-alias eliminates outer bind: (return (succ x)) to b. return (succ b)
        let rv = ret_var(&mut heap, 0);
        let s1 = ret_succ_var(&mut heap, 0);
        let s2 = ret_succ_var(&mut heap, 0);
        let inner = bind(&mut heap, s1, s2);
        let term = bind(&mut heap, rv, inner);
        let result = opt_comp(&mut heap, term);
        let es1 = ret_succ_var(&mut heap, 0);
        let es2 = ret_succ_var(&mut heap, 0);
        let expected = bind(&mut heap, es1, es2);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn pull_choice() {
        let mut heap = Heap::new();
        // (return 0 [] return 1) to x. return (succ x)
        let b1 = ret_zero(&mut heap);
        let z = imm(&mut heap, MValue::Zero);
        let one = imm(&mut heap, MValue::Succ(z));
        let b2 = ret(&mut heap, one);
        let ch = choice(&mut heap, vec![b1, b2]);
        let s = ret_succ_var(&mut heap, 0);
        let term = bind(&mut heap, ch, s);
        let result = opt_comp(&mut heap, term);
        // expected: (return 0 to x. return (succ x)) [] (return 1 to x. return (succ x))
        let eb1a = ret_zero(&mut heap);
        let eb1b = ret_succ_var(&mut heap, 0);
        let eb1 = bind(&mut heap, eb1a, eb1b);
        let ez = imm(&mut heap, MValue::Zero);
        let eone = imm(&mut heap, MValue::Succ(ez));
        let eb2a = ret(&mut heap, eone);
        let eb2b = ret_succ_var(&mut heap, 0);
        let eb2 = bind(&mut heap, eb2a, eb2b);
        let expected = choice(&mut heap, vec![eb1, eb2]);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn pull_choice_eliminates_fail_branch() {
        let mut heap = Heap::new();
        // (return 0 [] fail) to x. return x --> return 0
        let b1 = ret_zero(&mut heap);
        let b2 = fail_comp(&mut heap);
        let ch = choice(&mut heap, vec![b1, b2]);
        let rv = ret_var(&mut heap, 0);
        let term = bind(&mut heap, ch, rv);
        let result = opt_comp(&mut heap, term);
        let expected = ret_zero(&mut heap);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn pull_exists() {
        let mut heap = Heap::new();
        // (exists z:Nat. return z) to x. return (succ x)
        // --> exists z:Nat. return (succ z)
        let body = ret_var(&mut heap, 0);
        let ex = heap.alloc_comp(MComputation::Exists {
            ptype: ValueType::Nat,
            body,
        });
        let s = ret_succ_var(&mut heap, 0);
        let term = bind(&mut heap, ex, s);
        let result = opt_comp(&mut heap, term);
        let ebody = ret_succ_var(&mut heap, 0);
        let expected = heap.alloc_comp(MComputation::Exists {
            ptype: ValueType::Nat,
            body: ebody,
        });
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn pull_equate() {
        let mut heap = Heap::new();
        // (0 =:= 0. return 1) to x. return (succ x)
        // equate-refl fires -> (return 1) to x. return (succ x) -- bind kept
        let z1 = imm(&mut heap, MValue::Zero);
        let one_inner = imm(&mut heap, MValue::Zero);
        let one = imm(&mut heap, MValue::Succ(one_inner));
        let eq_body = ret(&mut heap, one);
        let lhs = imm(&mut heap, MValue::Zero);
        let rhs = imm(&mut heap, MValue::Zero);
        let eq = heap.alloc_comp(MComputation::Equate {
            lhs,
            rhs,
            body: eq_body,
        });
        let s = ret_succ_var(&mut heap, 0);
        let term = bind(&mut heap, eq, s);
        let _ = z1;
        let result = opt_comp(&mut heap, term);
        let eone_inner = imm(&mut heap, MValue::Zero);
        let eone = imm(&mut heap, MValue::Succ(eone_inner));
        let ebody = ret(&mut heap, eone);
        let es = ret_succ_var(&mut heap, 0);
        let expected = bind(&mut heap, ebody, es);
        assert!(comp_eq(&heap, result, expected));
    }

    #[test]
    fn equate_succ_succ_decompose() {
        let mut heap = Heap::new();
        // succ(0) =:= succ(0). M --> M
        let nil = imm(&mut heap, MValue::Nil);
        let body = ret(&mut heap, nil);
        let z1 = imm(&mut heap, MValue::Zero);
        let lhs = imm(&mut heap, MValue::Succ(z1));
        let z2 = imm(&mut heap, MValue::Zero);
        let rhs = imm(&mut heap, MValue::Succ(z2));
        let term = heap.alloc_comp(MComputation::Equate { lhs, rhs, body });
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, body));
    }

    #[test]
    fn equate_succ_zero_fail() {
        let mut heap = Heap::new();
        let z1 = imm(&mut heap, MValue::Zero);
        let lhs = imm(&mut heap, MValue::Succ(z1));
        let rhs = imm(&mut heap, MValue::Zero);
        let nil = imm(&mut heap, MValue::Nil);
        let body = ret(&mut heap, nil);
        let term = heap.alloc_comp(MComputation::Equate { lhs, rhs, body });
        let result = opt_comp(&mut heap, term);
        assert!(is_fail(&heap, result));
    }

    #[test]
    fn equate_cons_nil_fail() {
        let mut heap = Heap::new();
        let z = imm(&mut heap, MValue::Zero);
        let n = imm(&mut heap, MValue::Nil);
        let lhs = imm(&mut heap, MValue::Cons(z, n));
        let rhs = imm(&mut heap, MValue::Nil);
        let nil = imm(&mut heap, MValue::Nil);
        let body = ret(&mut heap, nil);
        let term = heap.alloc_comp(MComputation::Equate { lhs, rhs, body });
        let result = opt_comp(&mut heap, term);
        assert!(is_fail(&heap, result));
    }

    #[test]
    fn equate_pair_decompose() {
        let mut heap = Heap::new();
        // (0, 1) =:= (0, 1). M --> M
        let nil = imm(&mut heap, MValue::Nil);
        let body = ret(&mut heap, nil);
        let lz = imm(&mut heap, MValue::Zero);
        let lo_inner = imm(&mut heap, MValue::Zero);
        let lo = imm(&mut heap, MValue::Succ(lo_inner));
        let lhs = imm(&mut heap, MValue::Pair(lz, lo));
        let rz = imm(&mut heap, MValue::Zero);
        let ro_inner = imm(&mut heap, MValue::Zero);
        let ro = imm(&mut heap, MValue::Succ(ro_inner));
        let rhs = imm(&mut heap, MValue::Pair(rz, ro));
        let term = heap.alloc_comp(MComputation::Equate { lhs, rhs, body });
        let result = opt_comp(&mut heap, term);
        assert!(comp_eq(&heap, result, body));
    }
}
