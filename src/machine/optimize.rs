//! # The equational optimiser
//!
//! An optional peephole optimiser over CBPV terms (enabled by `-o`) that rewrites a program by the
//! equational laws of the theory while preserving its multiset of solutions. [`optimize`] rewrites
//! the main computation, [`optimize_val`] a function value. The machinery is one generic
//! binder-aware traversal (`map_val`/`map_comp`), which the de Bruijn passes — shift, subst, swap —
//! merely wrap; the driver optimises subterms under a compile-time environment, then applies the
//! top-level rules to a fixpoint: beta and eta, dead-bind, the pull/assoc family, choice
//! flattening, equate decomposition, and eliminator beta.

use bumpalo::Bump;

use super::mterms::{MComputation, MValue};

/// Optimize a computation using equational laws from the CBPV theory.
pub fn optimize<'a>(arena: &'a Bump, comp: &'a MComputation<'a>) -> &'a MComputation<'a> {
    #[cfg(feature = "opt-stats")]
    let before = comp.count_nodes();
    let result = opt_comp(arena, comp);
    #[cfg(feature = "opt-stats")]
    {
        let after = result.count_nodes();
        eprintln!("[opt] main:  {before} -> {after} nodes ({:+.1}%)", pct(before, after));
        stats::report();
    }
    result
}

/// Optimize an MValue (recursing into Thunks to optimize computations).
pub fn optimize_val<'a>(arena: &'a Bump, val: &'a MValue<'a>) -> &'a MValue<'a> {
    opt_val(arena, val, &[])
}

/// Optimize an entire environment and print per-function stats.
#[cfg(feature = "opt-stats")]
pub fn optimize_env_with_stats<'a>(
    arena: &'a Bump,
    env: &[&'a MValue<'a>],
    f: &dyn Fn(&'a Bump, &'a MValue<'a>) -> &'a MValue<'a>,
) -> Vec<&'a MValue<'a>> {
    let before_total: usize = env.iter().map(|v| v.count_nodes()).sum();
    let result: Vec<_> = env.iter().map(|v| f(arena, v)).collect();
    let after_total: usize = result.iter().map(|v| v.count_nodes()).sum();
    eprintln!("[opt] env:   {before_total} -> {after_total} nodes ({:+.1}%)", pct(before_total, after_total));
    stats::report();
    result
}

#[cfg(feature = "opt-stats")]
fn pct(before: usize, after: usize) -> f64 {
    if before == 0 { 0.0 } else { (after as f64 - before as f64) / before as f64 * 100.0 }
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
            ("app-bind", &APP_BIND), ("lam-choice", &LAM_CHOICE),
            ("lam-exists", &LAM_EXISTS), ("lam-equate", &LAM_EQUATE),
            ("eq-exists", &EQ_EXISTS), ("eq-choice", &EQ_CHOICE),
            ("dead-end", &DEAD_END), ("cycle", &CYCLE),
            ("ifz-beta", &IFZ_BETA), ("match-beta", &MATCH_BETA),
            ("case-beta", &CASE_BETA), ("force-beta", &FORCE_BETA),
            ("dead-bind", &DEAD_BIND), ("bind-eta", &BIND_ETA),
            ("lam-beta", &LAM_BETA),
        ];
        let fired: Vec<_> = rules.iter()
            .filter_map(|(name, cell)| {
                let n = cell.with(|c| c.get());
                if n > 0 { Some(format!("{name}={n}")) } else { None }
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

// --- Generic binder-aware traversal ---
// map_val/map_comp rebuild the term, rewriting each Var leaf via `f`, which is
// given the number of binders crossed from the traversal root to that leaf.
// The per-binder depth table (which binders bind, and by how much) lives here once.

fn map_val<'a>(
    arena: &'a Bump,
    val: &'a MValue<'a>,
    binders: usize,
    f: &dyn Fn(usize, &'a MValue<'a>) -> &'a MValue<'a>,
) -> &'a MValue<'a> {
    match val {
        MValue::Var(_) => f(binders, val),
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => val,
        MValue::Succ(v) => arena.alloc(MValue::Succ(map_val(arena, v, binders, f))),
        MValue::Pair(a, b) => arena.alloc(MValue::Pair(
            map_val(arena, a, binders, f),
            map_val(arena, b, binders, f),
        )),
        MValue::Inl(v) => arena.alloc(MValue::Inl(map_val(arena, v, binders, f))),
        MValue::Inr(v) => arena.alloc(MValue::Inr(map_val(arena, v, binders, f))),
        MValue::Cons(h, t) => arena.alloc(MValue::Cons(
            map_val(arena, h, binders, f),
            map_val(arena, t, binders, f),
        )),
        MValue::Thunk(c) => arena.alloc(MValue::Thunk(map_comp(arena, c, binders, f))),
    }
}

fn map_comp<'a>(
    arena: &'a Bump,
    comp: &'a MComputation<'a>,
    binders: usize,
    f: &dyn Fn(usize, &'a MValue<'a>) -> &'a MValue<'a>,
) -> &'a MComputation<'a> {
    match comp {
        MComputation::Return(v) => arena.alloc(MComputation::Return(map_val(arena, v, binders, f))),
        MComputation::Bind { comp: c, cont } => arena.alloc(MComputation::Bind {
            comp: map_comp(arena, c, binders, f),
            cont: map_comp(arena, cont, binders + 1, f),
        }),
        MComputation::Force(v) => arena.alloc(MComputation::Force(map_val(arena, v, binders, f))),
        MComputation::Lambda { body } => arena.alloc(MComputation::Lambda {
            body: map_comp(arena, body, binders + 1, f),
        }),
        MComputation::App { op, arg } => arena.alloc(MComputation::App {
            op: map_comp(arena, op, binders, f),
            arg: map_val(arena, arg, binders, f),
        }),
        MComputation::Choice(cs) => {
            let mapped: Vec<&'a MComputation<'a>> = cs.iter().map(|c| map_comp(arena, c, binders, f)).collect();
            arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&mapped)))
        }
        MComputation::Exists { ptype, body } => arena.alloc(MComputation::Exists {
            ptype: ptype.clone(),
            body: map_comp(arena, body, binders + 1, f),
        }),
        MComputation::Equate { lhs, rhs, body } => arena.alloc(MComputation::Equate {
            lhs: map_val(arena, lhs, binders, f),
            rhs: map_val(arena, rhs, binders, f),
            body: map_comp(arena, body, binders, f),
        }),
        MComputation::Ifz { num, zk, sk } => arena.alloc(MComputation::Ifz {
            num: map_val(arena, num, binders, f),
            zk: map_comp(arena, zk, binders, f),
            sk: map_comp(arena, sk, binders + 1, f),
        }),
        MComputation::Match { list, nilk, consk } => arena.alloc(MComputation::Match {
            list: map_val(arena, list, binders, f),
            nilk: map_comp(arena, nilk, binders, f),
            consk: map_comp(arena, consk, binders + 2, f),
        }),
        MComputation::Case { sum, inlk, inrk } => arena.alloc(MComputation::Case {
            sum: map_val(arena, sum, binders, f),
            inlk: map_comp(arena, inlk, binders + 1, f),
            inrk: map_comp(arena, inrk, binders + 1, f),
        }),
        MComputation::Rec { body } => arena.alloc(MComputation::Rec {
            body: map_comp(arena, body, binders + 1, f),
        }),
    }
}

// --- De Bruijn shifting ---

fn shift_val<'a>(arena: &'a Bump, val: &'a MValue<'a>, delta: isize, cutoff: usize) -> &'a MValue<'a> {
    map_val(arena, val, cutoff, &move |binders, v| {
        let MValue::Var(i) = v else { unreachable!() };
        if *i >= binders {
            arena.alloc(MValue::Var((*i as isize + delta) as usize))
        } else {
            v
        }
    })
}

fn shift_comp<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, delta: isize, cutoff: usize) -> &'a MComputation<'a> {
    if delta == 0 {
        return comp;
    }
    map_comp(arena, comp, cutoff, &move |binders, v| {
        let MValue::Var(i) = v else { unreachable!() };
        if *i >= binders {
            arena.alloc(MValue::Var((*i as isize + delta) as usize))
        } else {
            v
        }
    })
}

// --- De Bruijn substitution ---
// subst_comp replaces Var(depth) with shift(repl, depth, 0),
// and decrements all Var(i) where i > depth.

fn subst_comp<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, repl: &'a MValue<'a>, depth: usize) -> &'a MComputation<'a> {
    map_comp(arena, comp, depth, &move |binders, v| {
        let MValue::Var(i) = v else { unreachable!() };
        if *i == binders {
            shift_val(arena, repl, binders as isize, 0)
        } else if *i > binders {
            arena.alloc(MValue::Var(i - 1))
        } else {
            v
        }
    })
}

// --- Helpers ---

/// Check if a value structurally contains `needle` as a strict sub-value.
/// Used for cycle detection in equate: `V =:= C[V]` -> fail.
fn val_contains(needle: &MValue, haystack: &MValue) -> bool {
    if needle == haystack {
        return true;
    }
    match haystack {
        MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => val_contains(needle, v),
        MValue::Pair(a, b) | MValue::Cons(a, b) => {
            val_contains(needle, a) || val_contains(needle, b)
        }
        _ => false,
    }
}

/// Check if `target` de Bruijn index appears free in a value.
fn has_free_var_val(val: &MValue, target: usize) -> bool {
    match val {
        MValue::Var(i) => *i == target,
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => false,
        MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => has_free_var_val(v, target),
        MValue::Pair(a, b) | MValue::Cons(a, b) => {
            has_free_var_val(a, target) || has_free_var_val(b, target)
        }
        MValue::Thunk(c) => has_free_var_comp(c, target),
    }
}

fn has_free_var_comp(comp: &MComputation, target: usize) -> bool {
    match comp {
        MComputation::Return(v) | MComputation::Force(v) => has_free_var_val(v, target),
        MComputation::Bind { comp: c, cont } => {
            has_free_var_comp(c, target) || has_free_var_comp(cont, target + 1)
        }
        MComputation::Lambda { body } | MComputation::Exists { body, .. } | MComputation::Rec { body } => {
            has_free_var_comp(body, target + 1)
        }
        MComputation::App { op, arg } => {
            has_free_var_comp(op, target) || has_free_var_val(arg, target)
        }
        MComputation::Choice(cs) => cs.iter().any(|c| has_free_var_comp(c, target)),
        MComputation::Equate { lhs, rhs, body } => {
            has_free_var_val(lhs, target) || has_free_var_val(rhs, target) || has_free_var_comp(body, target)
        }
        MComputation::Ifz { num, zk, sk } => {
            has_free_var_val(num, target) || has_free_var_comp(zk, target) || has_free_var_comp(sk, target + 1)
        }
        MComputation::Match { list, nilk, consk } => {
            has_free_var_val(list, target) || has_free_var_comp(nilk, target) || has_free_var_comp(consk, target + 2)
        }
        MComputation::Case { sum, inlk, inrk } => {
            has_free_var_val(sum, target) || has_free_var_comp(inlk, target + 1) || has_free_var_comp(inrk, target + 1)
        }
    }
}

/// Swap two adjacent binders at `depth` and `depth+1`.
fn swap_comp<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, depth: usize) -> &'a MComputation<'a> {
    map_comp(arena, comp, depth, &move |binders, v| {
        let MValue::Var(i) = v else { unreachable!() };
        if *i == binders {
            arena.alloc(MValue::Var(binders + 1))
        } else if *i == binders + 1 {
            arena.alloc(MValue::Var(binders))
        } else {
            v
        }
    })
}

// --- Optimizer ---

fn is_fail(comp: &MComputation) -> bool {
    matches!(comp, MComputation::Choice(cs) if cs.is_empty())
}

fn fail<'a>(arena: &'a Bump) -> &'a MComputation<'a> {
    arena.alloc(MComputation::Choice(&[]))
}

type Env<'a> = Vec<Option<&'a MValue<'a>>>;

fn push_env<'a>(env: &[Option<&'a MValue<'a>>], entry: Option<&'a MValue<'a>>) -> Env<'a> {
    let mut e = Vec::with_capacity(env.len() + 1);
    e.push(entry);
    e.extend_from_slice(env);
    e
}

/// Recursively resolve all variables in a value through the compile-time env.
/// Used to build fully-concrete env entries for decision-making.
fn deep_resolve<'a>(arena: &'a Bump, val: &'a MValue<'a>, env: &[Option<&'a MValue<'a>>]) -> &'a MValue<'a> {
    match val {
        MValue::Var(i) => {
            if let Some(Some(v)) = env.get(*i) {
                let shifted = shift_val(arena, v, (*i as isize) + 1, 0);
                deep_resolve(arena, shifted, env)
            } else {
                val
            }
        }
        MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => val,
        MValue::Succ(v) => arena.alloc(MValue::Succ(deep_resolve(arena, v, env))),
        MValue::Pair(a, b) => arena.alloc(MValue::Pair(deep_resolve(arena, a, env), deep_resolve(arena, b, env))),
        MValue::Inl(v) => arena.alloc(MValue::Inl(deep_resolve(arena, v, env))),
        MValue::Inr(v) => arena.alloc(MValue::Inr(deep_resolve(arena, v, env))),
        MValue::Cons(h, t) => arena.alloc(MValue::Cons(deep_resolve(arena, h, env), deep_resolve(arena, t, env))),
        MValue::Thunk(_) => val,
    }
}

fn opt_val<'a>(arena: &'a Bump, val: &'a MValue<'a>, env: &[Option<&'a MValue<'a>>]) -> &'a MValue<'a> {
    match val {
        MValue::Thunk(c) => arena.alloc(MValue::Thunk(opt_comp_env(arena, c, env))),
        MValue::Succ(v) => arena.alloc(MValue::Succ(opt_val(arena, v, env))),
        MValue::Pair(a, b) => arena.alloc(MValue::Pair(opt_val(arena, a, env), opt_val(arena, b, env))),
        MValue::Inl(v) => arena.alloc(MValue::Inl(opt_val(arena, v, env))),
        MValue::Inr(v) => arena.alloc(MValue::Inr(opt_val(arena, v, env))),
        MValue::Cons(h, t) => arena.alloc(MValue::Cons(opt_val(arena, h, env), opt_val(arena, t, env))),
        _ => val,
    }
}

fn opt_comp<'a>(arena: &'a Bump, comp: &'a MComputation<'a>) -> &'a MComputation<'a> {
    opt_comp_env(arena, comp, &[])
}

fn opt_comp_env<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: &[Option<&'a MValue<'a>>]) -> &'a MComputation<'a> {
    let rebuilt = opt_subterms(arena, comp, env);
    rewrite(arena, rebuilt, env)
}

fn opt_subterms<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: &[Option<&'a MValue<'a>>]) -> &'a MComputation<'a> {
    match comp {
        MComputation::Return(v) => arena.alloc(MComputation::Return(opt_val(arena, v, env))),
        MComputation::Bind { comp: c, cont } => {
            let oc = opt_comp_env(arena, c, env);
            let entry = if let MComputation::Return(v) = oc {
                Some(deep_resolve(arena, v, env))
            } else {
                None
            };
            let cenv = push_env(env, entry);
            arena.alloc(MComputation::Bind { comp: oc, cont: opt_comp_env(arena, cont, &cenv) })
        }
        MComputation::Force(v) => arena.alloc(MComputation::Force(opt_val(arena, v, env))),
        MComputation::Lambda { body } => arena.alloc(MComputation::Lambda {
            body: opt_comp_env(arena, body, &push_env(env, None)),
        }),
        MComputation::App { op, arg } => arena.alloc(MComputation::App {
            op: opt_comp_env(arena, op, env),
            arg: opt_val(arena, arg, env),
        }),
        MComputation::Choice(cs) => {
            let optimized: Vec<&'a MComputation<'a>> = cs.iter().map(|c| opt_comp_env(arena, c, env)).collect();
            arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&optimized)))
        }
        MComputation::Exists { ptype, body } => arena.alloc(MComputation::Exists {
            ptype: ptype.clone(),
            body: opt_comp_env(arena, body, &push_env(env, None)),
        }),
        MComputation::Equate { lhs, rhs, body } => arena.alloc(MComputation::Equate {
            lhs: opt_val(arena, lhs, env),
            rhs: opt_val(arena, rhs, env),
            body: opt_comp_env(arena, body, env),
        }),
        MComputation::Ifz { num, zk, sk } => arena.alloc(MComputation::Ifz {
            num: opt_val(arena, num, env),
            zk: opt_comp_env(arena, zk, env),
            sk: opt_comp_env(arena, sk, &push_env(env, None)),
        }),
        MComputation::Match { list, nilk, consk } => arena.alloc(MComputation::Match {
            list: opt_val(arena, list, env),
            nilk: opt_comp_env(arena, nilk, env),
            consk: opt_comp_env(arena, consk, &push_env(&push_env(env, None), None)),
        }),
        MComputation::Case { sum, inlk, inrk } => arena.alloc(MComputation::Case {
            sum: opt_val(arena, sum, env),
            inlk: opt_comp_env(arena, inlk, &push_env(env, None)),
            inrk: opt_comp_env(arena, inrk, &push_env(env, None)),
        }),
        MComputation::Rec { body } => arena.alloc(MComputation::Rec {
            body: opt_comp_env(arena, body, &push_env(env, None)),
        }),
    }
}

/// Try rewrite rules at the top level. If a rewrite fires, re-optimize the result.
fn rewrite<'a>(arena: &'a Bump, comp: &'a MComputation<'a>, env: &[Option<&'a MValue<'a>>]) -> &'a MComputation<'a> {
    match comp {
        // Bind rules:
        // fail to x. M  -->  fail
        // eta: M to x. return x  -->  M
        // dead-bind: return V to x. M  -->  M↓  (when x not in FV(M))
        // dead-end: M to x. fail  -->  fail
        // bind-assoc, pull-choice, pull-exists, pull-equate
        MComputation::Bind { comp: c, cont } => {
            if let MComputation::Return(v) = c {
                // eta: return V to x. return x -> return V
                if let MComputation::Return(rv) = cont {
                    if matches!(rv, MValue::Var(0)) {
                        #[cfg(feature = "opt-stats")]
                        stats::bump("bind-eta");
                        return c;
                    }
                }
                // dead-bind: cont doesn't use Var(0) -> drop the bind
                if !has_free_var_comp(cont, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("dead-bind");
                    return shift_comp(arena, cont, -1, 0);
                }
                // Variable aliasing: Bind { Return(Var(i)), cont } is just renaming
                if matches!(v, MValue::Var(_)) {
                    return opt_comp_env(arena, subst_comp(arena, cont, v, 0), env);
                }
            }
            if is_fail(c) {
                return fail(arena);
            }
            // eta for non-Return c
            if let MComputation::Return(v) = cont {
                if matches!(v, MValue::Var(0)) {
                    return c;
                }
            }
            // Dead-End: M to x. fail  -->  fail
            if is_fail(cont) {
                #[cfg(feature = "opt-stats")]
                stats::bump("dead-end");
                return fail(arena);
            }
            // Bind-assoc: (M to x. N) to y. P -> M to x. (N to y'. P')
            if let MComputation::Bind {
                comp: inner_c,
                cont: inner_k,
            } = c
            {
                match inner_k {
                    MComputation::Return(_)
                    | MComputation::Exists { .. }
                    | MComputation::Equate { .. } => {
                        let shifted_cont = shift_comp(arena, cont, 1, 1);
                        let new_inner = arena.alloc(MComputation::Bind {
                            comp: inner_k,
                            cont: shifted_cont,
                        });
                        let new_outer = arena.alloc(MComputation::Bind {
                            comp: inner_c,
                            cont: new_inner,
                        });
                        return opt_comp_env(arena, new_outer, env);
                    }
                    MComputation::Choice(branches) if !branches.is_empty() =>
                    {
                        let shifted_cont = shift_comp(arena, cont, 1, 1);
                        let new_inner = arena.alloc(MComputation::Bind {
                            comp: inner_k,
                            cont: shifted_cont,
                        });
                        let new_outer = arena.alloc(MComputation::Bind {
                            comp: inner_c,
                            cont: new_inner,
                        });
                        return opt_comp_env(arena, new_outer, env);
                    }
                    _ => {}
                }
            }
            // Pull-Choice
            if let MComputation::Choice(branches) = c {
                if !branches.is_empty() {
                    let new_branches: Vec<&'a MComputation<'a>> = branches
                        .iter()
                        .map(|b| -> &'a MComputation<'a> {
                            arena.alloc(MComputation::Bind {
                                comp: b,
                                cont,
                            })
                        })
                        .collect();
                    let choice = arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&new_branches)));
                    return opt_comp_env(arena, choice, env);
                }
            }
            // Pull-Exists
            if let MComputation::Exists { ptype, body } = c {
                let shifted_cont = shift_comp(arena, cont, 1, 1);
                let new_bind = arena.alloc(MComputation::Bind {
                    comp: body,
                    cont: shifted_cont,
                });
                let new_exists = arena.alloc(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: new_bind,
                });
                return opt_comp_env(arena, new_exists, env);
            }
            // Pull-Equate
            if let MComputation::Equate { lhs, rhs, body } = c {
                let new_bind = arena.alloc(MComputation::Bind {
                    comp: body,
                    cont,
                });
                let new_equate = arena.alloc(MComputation::Equate {
                    lhs,
                    rhs,
                    body: new_bind,
                });
                return opt_comp_env(arena, new_equate, env);
            }
            comp
        }

        // force(thunk M)  -->  M  (resolve through env)
        MComputation::Force(v) => {
            let resolved = deep_resolve(arena, v, env);
            if let MValue::Thunk(c) = resolved {
                #[cfg(feature = "opt-stats")]
                stats::bump("force-beta");
                return opt_comp_env(arena, c, env);
            }
            comp
        }

        // (lam x. M)(V)  -->  M[V/x]
        // app-bind: (M to x. N)(V)  -->  M to x. N(V)
        MComputation::App { op, arg } => {
            if let MComputation::Lambda { body } = op {
                #[cfg(feature = "opt-stats")]
                stats::bump("lam-beta");
                return opt_comp_env(arena, subst_comp(arena, body, arg, 0), env);
            }
            if let MComputation::Bind { comp: c, cont } = op {
                #[cfg(feature = "opt-stats")]
                stats::bump("app-bind");
                let new_app = arena.alloc(MComputation::App {
                    op: cont,
                    arg: shift_val(arena, arg, 1, 0),
                });
                let new_bind = arena.alloc(MComputation::Bind {
                    comp: c,
                    cont: new_app,
                });
                return opt_comp_env(arena, new_bind, env);
            }
            comp
        }

        // Choice: flatten nested choices, remove fail branches, unwrap singletons
        MComputation::Choice(cs) => {
            let mut flat: Vec<&'a MComputation<'a>> = Vec::new();
            let mut changed = false;
            for c in cs.iter() {
                match c {
                    MComputation::Choice(inner) => {
                        changed = true;
                        for ic in inner.iter() {
                            if !is_fail(ic) {
                                flat.push(ic);
                            }
                        }
                    }
                    _ if is_fail(c) => {
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
                0 => fail(arena),
                1 => flat[0],
                _ => arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&flat))),
            }
        }

        // exists fail  -->  fail
        MComputation::Exists { body, .. } => {
            if is_fail(body) {
                return fail(arena);
            }
            comp
        }

        // equate rules: reflexivity, cycle, parameter laws, etc.
        MComputation::Equate { lhs, rhs, body } => {
            if is_fail(body) {
                return fail(arena);
            }
            // Resolve through env so parameter laws can see constructors
            let rlhs = deep_resolve(arena, lhs, env);
            let rrhs = deep_resolve(arena, rhs, env);
            if rlhs == rrhs {
                return body;
            }
            if val_contains(rlhs, rrhs) || val_contains(rrhs, rlhs) {
                #[cfg(feature = "opt-stats")]
                stats::bump("cycle");
                return fail(arena);
            }
            if let MComputation::Exists { ptype, body: ebody } = body {
                #[cfg(feature = "opt-stats")]
                stats::bump("eq-exists");
                let new_equate = arena.alloc(MComputation::Equate {
                    lhs: shift_val(arena, lhs, 1, 0),
                    rhs: shift_val(arena, rhs, 1, 0),
                    body: ebody,
                });
                let new_exists = arena.alloc(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: new_equate,
                });
                return opt_comp_env(arena, new_exists, env);
            }
            if let MComputation::Choice(branches) = body {
                if !branches.is_empty() {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("eq-choice");
                    let new_branches: Vec<&'a MComputation<'a>> = branches
                        .iter()
                        .map(|b| -> &'a MComputation<'a> {
                            arena.alloc(MComputation::Equate {
                                lhs,
                                rhs,
                                body: b,
                            })
                        })
                        .collect();
                    let choice = arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&new_branches)));
                    return opt_comp_env(arena, choice, env);
                }
            }
            match (rlhs, rrhs) {
                (MValue::Succ(v), MValue::Succ(w)) => {
                    let new_equate = arena.alloc(MComputation::Equate {
                        lhs: v,
                        rhs: w,
                        body,
                    });
                    return opt_comp_env(arena, new_equate, env);
                }
                (MValue::Succ(_), MValue::Zero) | (MValue::Zero, MValue::Succ(_)) => {
                    return fail(arena);
                }
                (MValue::Cons(v1, w1), MValue::Cons(v2, w2)) => {
                    let inner_equate = arena.alloc(MComputation::Equate {
                        lhs: w1,
                        rhs: w2,
                        body,
                    });
                    let outer_equate = arena.alloc(MComputation::Equate {
                        lhs: v1,
                        rhs: v2,
                        body: inner_equate,
                    });
                    return opt_comp_env(arena, outer_equate, env);
                }
                (MValue::Cons(..), MValue::Nil) | (MValue::Nil, MValue::Cons(..)) => {
                    return fail(arena);
                }
                (MValue::Pair(v1, v2), MValue::Pair(w1, w2)) => {
                    let inner_equate = arena.alloc(MComputation::Equate {
                        lhs: v2,
                        rhs: w2,
                        body,
                    });
                    let outer_equate = arena.alloc(MComputation::Equate {
                        lhs: v1,
                        rhs: w1,
                        body: inner_equate,
                    });
                    return opt_comp_env(arena, outer_equate, env);
                }
                (MValue::Inl(v), MValue::Inl(w)) | (MValue::Inr(v), MValue::Inr(w)) => {
                    let new_equate = arena.alloc(MComputation::Equate {
                        lhs: v,
                        rhs: w,
                        body,
                    });
                    return opt_comp_env(arena, new_equate, env);
                }
                (MValue::Inl(_), MValue::Inr(_)) | (MValue::Inr(_), MValue::Inl(_)) => {
                    return fail(arena);
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
            if is_fail(body) {
                return fail(arena);
            }
            if let MComputation::Choice(branches) = body {
                if !branches.is_empty() {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-choice");
                    let new_branches: Vec<&'a MComputation<'a>> = branches
                        .iter()
                        .map(|b| -> &'a MComputation<'a> {
                            arena.alloc(MComputation::Lambda { body: b })
                        })
                        .collect();
                    let choice = arena.alloc(MComputation::Choice(arena.alloc_slice_copy(&new_branches)));
                    return opt_comp_env(arena, choice, env);
                }
            }
            if let MComputation::Exists { ptype, body: ebody } = body {
                #[cfg(feature = "opt-stats")]
                stats::bump("lam-exists");
                let new_lam = arena.alloc(MComputation::Lambda {
                    body: swap_comp(arena, ebody, 0),
                });
                let new_exists = arena.alloc(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: new_lam,
                });
                return opt_comp_env(arena, new_exists, env);
            }
            if let MComputation::Equate { lhs, rhs, body: ebody } = body {
                if !has_free_var_val(lhs, 0) && !has_free_var_val(rhs, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-equate");
                    let new_lam = arena.alloc(MComputation::Lambda { body: ebody });
                    let new_equate = arena.alloc(MComputation::Equate {
                        lhs: shift_val(arena, lhs, -1, 0),
                        rhs: shift_val(arena, rhs, -1, 0),
                        body: new_lam,
                    });
                    return opt_comp_env(arena, new_equate, env);
                }
            }
            comp
        }

        // ifz(num, zk, n.sk): resolve num through env, then subst
        MComputation::Ifz { num, zk, sk } => {
            let resolved = deep_resolve(arena, num, env);
            match resolved {
                MValue::Zero => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("ifz-beta");
                    zk
                }
                MValue::Succ(pred) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("ifz-beta");
                    opt_comp_env(arena, subst_comp(arena, sk, pred, 0), env)
                }
                _ => comp,
            }
        }

        // match(list, nilk, x.xs.consk): resolve list through env, then subst
        MComputation::Match { list, nilk, consk } => {
            let resolved = deep_resolve(arena, list, env);
            match resolved {
                MValue::Nil => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("match-beta");
                    nilk
                }
                MValue::Cons(head, tail) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("match-beta");
                    let step1 = subst_comp(arena, consk, tail, 0);
                    let step2 = subst_comp(arena, step1, head, 0);
                    opt_comp_env(arena, step2, env)
                }
                _ => comp,
            }
        }

        // case(sum, x.inlk, y.inrk): resolve sum through env, then subst
        MComputation::Case { sum, inlk, inrk } => {
            let resolved = deep_resolve(arena, sum, env);
            match resolved {
                MValue::Inl(v) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("case-beta");
                    opt_comp_env(arena, subst_comp(arena, inlk, v, 0), env)
                }
                MValue::Inr(v) => {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("case-beta");
                    opt_comp_env(arena, subst_comp(arena, inrk, v, 0), env)
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

    fn ret<'a>(arena: &'a Bump, v: MValue<'a>) -> &'a MComputation<'a> {
        arena.alloc(MComputation::Return(arena.alloc(v)))
    }

    fn bind<'a>(arena: &'a Bump, c: &'a MComputation<'a>, k: &'a MComputation<'a>) -> &'a MComputation<'a> {
        arena.alloc(MComputation::Bind { comp: c, cont: k })
    }

    fn var<'a>(arena: &'a Bump, i: usize) -> &'a MValue<'a> {
        arena.alloc(MValue::Var(i))
    }

    #[test]
    fn bind_return_beta() {
        let arena = Bump::new();
        // (return 0) to x. return (succ x) -- env approach keeps bind
        let term = bind(&arena,
            ret(&arena, MValue::Zero),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        let result = opt_comp(&arena, term);
        let expected = bind(&arena, ret(&arena, MValue::Zero), ret(&arena, MValue::Succ(var(&arena, 0))));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn bind_return_chain() {
        let arena = Bump::new();
        // (return 0) to x. (return x) to y. return (succ y)
        // var-alias eliminates inner bind: (return 0) to x. return (succ x)
        let term = bind(&arena,
            ret(&arena, MValue::Zero),
            bind(&arena,
                ret(&arena, MValue::Var(0)),
                ret(&arena, MValue::Succ(var(&arena, 0))),
            ),
        );
        let result = opt_comp(&arena, term);
        let expected = bind(&arena, ret(&arena, MValue::Zero), ret(&arena, MValue::Succ(var(&arena, 0))));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn force_thunk_beta() {
        let arena = Bump::new();
        // force(thunk(return 0)) --> return 0
        let inner = arena.alloc(MComputation::Return(arena.alloc(MValue::Zero)));
        let term = arena.alloc(MComputation::Force(arena.alloc(MValue::Thunk(inner))));
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *inner);
    }

    #[test]
    fn fail_to_is_fail() {
        let arena = Bump::new();
        // fail to x. M --> fail
        let term = bind(&arena,
            arena.alloc(MComputation::Choice(&[])),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        let result = opt_comp(&arena, term);
        assert!(is_fail(result));
    }

    #[test]
    fn choice_removes_fail_branches() {
        let arena = Bump::new();
        // (fail [] return 0) --> return 0
        let fail_branch: &MComputation = arena.alloc(MComputation::Choice(&[]));
        let ret_branch = ret(&arena, MValue::Zero);
        let branches = arena.alloc_slice_copy(&[fail_branch, ret_branch]);
        let term = arena.alloc(MComputation::Choice(branches));
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *ret(&arena, MValue::Zero));
    }

    #[test]
    fn bind_return_eta() {
        let arena = Bump::new();
        // M to x. return x --> M
        let m = ret(&arena, MValue::Zero);
        let term = bind(&arena, m, ret(&arena, MValue::Var(0)));
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *m);
    }

    #[test]
    fn exists_fail() {
        let arena = Bump::new();
        use crate::machine::value_type::ValueType;
        let term = arena.alloc(MComputation::Exists {
            ptype: ValueType::Nat,
            body: arena.alloc(MComputation::Choice(&[])),
        });
        let result = opt_comp(&arena, term);
        assert!(is_fail(result));
    }

    #[test]
    fn equate_refl() {
        let arena = Bump::new();
        let v = arena.alloc(MValue::Zero);
        let body = ret(&arena, MValue::Succ(arena.alloc(MValue::Zero)));
        let term = arena.alloc(MComputation::Equate {
            lhs: v,
            rhs: v,
            body,
        });
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *body);
    }

    #[test]
    fn ifz_zero_beta() {
        let arena = Bump::new();
        let zk = ret(&arena, MValue::Nil);
        let sk = ret(&arena, MValue::Succ(var(&arena, 0)));
        let term = arena.alloc(MComputation::Ifz {
            num: arena.alloc(MValue::Zero),
            zk,
            sk,
        });
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *zk);
    }

    #[test]
    fn ifz_succ_beta() {
        let arena = Bump::new();
        // ifz(succ(0), zk, n. return (succ n)) --> return (succ 0)  (subst at eliminator)
        let term = arena.alloc(MComputation::Ifz {
            num: arena.alloc(MValue::Succ(arena.alloc(MValue::Zero))),
            zk: ret(&arena, MValue::Nil),
            sk: ret(&arena, MValue::Succ(var(&arena, 0))),
        });
        let result = opt_comp(&arena, term);
        let expected = ret(&arena, MValue::Succ(arena.alloc(MValue::Zero)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn match_nil_beta() {
        let arena = Bump::new();
        let nilk = ret(&arena, MValue::Zero);
        let consk = ret(&arena, MValue::Pair(var(&arena, 1), var(&arena, 0)));
        let term = arena.alloc(MComputation::Match {
            list: arena.alloc(MValue::Nil),
            nilk,
            consk,
        });
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *nilk);
    }

    #[test]
    fn match_cons_beta() {
        let arena = Bump::new();
        // match(cons(0, nil), nilk, x.xs. return (x, xs)) --> return (0, nil)
        let term = arena.alloc(MComputation::Match {
            list: arena.alloc(MValue::Cons(arena.alloc(MValue::Zero), arena.alloc(MValue::Nil))),
            nilk: ret(&arena, MValue::Nil),
            consk: ret(&arena, MValue::Pair(var(&arena, 1), var(&arena, 0))),
        });
        let result = opt_comp(&arena, term);
        let expected = ret(&arena, MValue::Pair(arena.alloc(MValue::Zero), arena.alloc(MValue::Nil)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn nested_bind_return_succ_succ() {
        let arena = Bump::new();
        // (return x) to a. (return (succ a)) to b. return (succ b)
        // var-alias eliminates outer bind: (return (succ x)) to b. return (succ b)
        let term = bind(&arena,
            ret(&arena, MValue::Var(0)),
            bind(&arena,
                ret(&arena, MValue::Succ(var(&arena, 0))),
                ret(&arena, MValue::Succ(var(&arena, 0))),
            ),
        );
        let result = opt_comp(&arena, term);
        let expected = bind(&arena,
            ret(&arena, MValue::Succ(var(&arena, 0))),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_choice() {
        let arena = Bump::new();
        // (return 0 [] return 1) to x. return (succ x)
        // --> (return 0 to x. return (succ x)) [] (return 1 to x. return (succ x))
        let b1 = ret(&arena, MValue::Zero);
        let b2 = ret(&arena, MValue::Succ(arena.alloc(MValue::Zero)));
        let branches = arena.alloc_slice_copy(&[b1, b2]);
        let term = bind(&arena,
            arena.alloc(MComputation::Choice(branches)),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        let result = opt_comp(&arena, term);
        let eb1 = bind(&arena, ret(&arena, MValue::Zero), ret(&arena, MValue::Succ(var(&arena, 0))));
        let eb2 = bind(&arena, ret(&arena, MValue::Succ(arena.alloc(MValue::Zero))), ret(&arena, MValue::Succ(var(&arena, 0))));
        let expected_branches = arena.alloc_slice_copy(&[eb1, eb2]);
        let expected = arena.alloc(MComputation::Choice(expected_branches));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_choice_eliminates_fail_branch() {
        let arena = Bump::new();
        // (return 0 [] fail) to x. return x --> return 0
        let b1 = ret(&arena, MValue::Zero);
        let b2: &MComputation = arena.alloc(MComputation::Choice(&[]));
        let branches = arena.alloc_slice_copy(&[b1, b2]);
        let term = bind(&arena,
            arena.alloc(MComputation::Choice(branches)),
            ret(&arena, MValue::Var(0)),
        );
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *ret(&arena, MValue::Zero));
    }

    #[test]
    fn pull_exists() {
        let arena = Bump::new();
        use crate::machine::value_type::ValueType;
        // (exists z:Nat. return z) to x. return (succ x)
        // --> exists z:Nat. return (succ z)  (pull-exists + var-alias elimination)
        let term = bind(&arena,
            arena.alloc(MComputation::Exists {
                ptype: ValueType::Nat,
                body: ret(&arena, MValue::Var(0)),
            }),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        let result = opt_comp(&arena, term);
        let expected = arena.alloc(MComputation::Exists {
            ptype: ValueType::Nat,
            body: ret(&arena, MValue::Succ(var(&arena, 0))),
        });
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_equate() {
        let arena = Bump::new();
        // (0 =:= 0. return 1) to x. return (succ x)
        // equate-refl fires -> (return 1) to x. return (succ x) -- bind kept
        let one = arena.alloc(MValue::Succ(arena.alloc(MValue::Zero)));
        let term = bind(&arena,
            arena.alloc(MComputation::Equate {
                lhs: arena.alloc(MValue::Zero),
                rhs: arena.alloc(MValue::Zero),
                body: arena.alloc(MComputation::Return(one)),
            }),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        let result = opt_comp(&arena, term);
        let expected = bind(&arena,
            arena.alloc(MComputation::Return(one)),
            ret(&arena, MValue::Succ(var(&arena, 0))),
        );
        assert_eq!(*result, *expected);
    }

    #[test]
    fn equate_succ_succ_decompose() {
        let arena = Bump::new();
        // succ(0) =:= succ(0). M --> M
        let body = ret(&arena, MValue::Nil);
        let term = arena.alloc(MComputation::Equate {
            lhs: arena.alloc(MValue::Succ(arena.alloc(MValue::Zero))),
            rhs: arena.alloc(MValue::Succ(arena.alloc(MValue::Zero))),
            body,
        });
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *body);
    }

    #[test]
    fn equate_succ_zero_fail() {
        let arena = Bump::new();
        let term = arena.alloc(MComputation::Equate {
            lhs: arena.alloc(MValue::Succ(arena.alloc(MValue::Zero))),
            rhs: arena.alloc(MValue::Zero),
            body: ret(&arena, MValue::Nil),
        });
        let result = opt_comp(&arena, term);
        assert!(is_fail(result));
    }

    #[test]
    fn equate_cons_nil_fail() {
        let arena = Bump::new();
        let term = arena.alloc(MComputation::Equate {
            lhs: arena.alloc(MValue::Cons(arena.alloc(MValue::Zero), arena.alloc(MValue::Nil))),
            rhs: arena.alloc(MValue::Nil),
            body: ret(&arena, MValue::Nil),
        });
        let result = opt_comp(&arena, term);
        assert!(is_fail(result));
    }

    #[test]
    fn equate_pair_decompose() {
        let arena = Bump::new();
        // (0, 1) =:= (0, 1). M --> M
        let one = arena.alloc(MValue::Succ(arena.alloc(MValue::Zero)));
        let body = ret(&arena, MValue::Nil);
        let term = arena.alloc(MComputation::Equate {
            lhs: arena.alloc(MValue::Pair(arena.alloc(MValue::Zero), one)),
            rhs: arena.alloc(MValue::Pair(arena.alloc(MValue::Zero), one)),
            body,
        });
        let result = opt_comp(&arena, term);
        assert_eq!(*result, *body);
    }
}
