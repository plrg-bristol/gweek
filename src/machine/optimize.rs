use std::rc::Rc;

use super::mterms::{MComputation, MValue};

/// Optimize a computation using equational laws from the CBPV theory.
pub fn optimize(comp: MComputation) -> MComputation {
    #[cfg(feature = "opt-stats")]
    let before = comp.count_nodes();
    let result = opt_comp(&Rc::new(comp));
    let result = Rc::try_unwrap(result).unwrap_or_else(|rc| (*rc).clone());
    #[cfg(feature = "opt-stats")]
    {
        let after = result.count_nodes();
        eprintln!("[opt] main:  {before} -> {after} nodes ({:+.1}%)", pct(before, after));
        stats::report();
    }
    result
}

/// Optimize an MValue (recursing into Thunks to optimize computations).
pub fn optimize_val(val: &Rc<MValue>) -> Rc<MValue> {
    opt_val(val)
}

/// Optimize an entire environment and print per-function stats.
#[cfg(feature = "opt-stats")]
pub fn optimize_env_with_stats<F: Fn(&Rc<MValue>) -> Rc<MValue>>(env: &Rc<super::Env>, f: &F) -> Rc<super::Env> {
    let before_total = env.count_nodes();
    let result = super::env::map_env_vals(env, f);
    let after_total = result.count_nodes();
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
            _ => {}
        }
    }
    pub fn report() {
        let rules = [
            ("app-bind", &APP_BIND), ("lam-choice", &LAM_CHOICE),
            ("lam-exists", &LAM_EXISTS), ("lam-equate", &LAM_EQUATE),
            ("eq-exists", &EQ_EXISTS), ("eq-choice", &EQ_CHOICE),
            ("dead-end", &DEAD_END), ("cycle", &CYCLE),
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

// --- De Bruijn shifting ---

fn shift_val(val: &Rc<MValue>, delta: isize, cutoff: usize) -> Rc<MValue> {
    match &**val {
        MValue::Var(i) => {
            if *i >= cutoff {
                Rc::new(MValue::Var((*i as isize + delta) as usize))
            } else {
                val.clone()
            }
        }
        MValue::Zero | MValue::Nil => val.clone(),
        MValue::Succ(v) => Rc::new(MValue::Succ(shift_val(v, delta, cutoff))),
        MValue::Pair(a, b) => Rc::new(MValue::Pair(
            shift_val(a, delta, cutoff),
            shift_val(b, delta, cutoff),
        )),
        MValue::Inl(v) => Rc::new(MValue::Inl(shift_val(v, delta, cutoff))),
        MValue::Inr(v) => Rc::new(MValue::Inr(shift_val(v, delta, cutoff))),
        MValue::Cons(h, t) => Rc::new(MValue::Cons(
            shift_val(h, delta, cutoff),
            shift_val(t, delta, cutoff),
        )),
        MValue::Thunk(c) => Rc::new(MValue::Thunk(shift_comp(c, delta, cutoff))),
    }
}

fn shift_comp(comp: &Rc<MComputation>, delta: isize, cutoff: usize) -> Rc<MComputation> {
    if delta == 0 {
        return comp.clone();
    }
    match &**comp {
        MComputation::Return(v) => Rc::new(MComputation::Return(shift_val(v, delta, cutoff))),
        MComputation::Bind { comp: c, cont } => Rc::new(MComputation::Bind {
            comp: shift_comp(c, delta, cutoff),
            cont: shift_comp(cont, delta, cutoff + 1),
        }),
        MComputation::Force(v) => Rc::new(MComputation::Force(shift_val(v, delta, cutoff))),
        MComputation::Lambda { body } => Rc::new(MComputation::Lambda {
            body: shift_comp(body, delta, cutoff + 1),
        }),
        MComputation::App { op, arg } => Rc::new(MComputation::App {
            op: shift_comp(op, delta, cutoff),
            arg: shift_val(arg, delta, cutoff),
        }),
        MComputation::Choice(cs) => Rc::new(MComputation::Choice(
            cs.iter().map(|c| shift_comp(c, delta, cutoff)).collect(),
        )),
        MComputation::Exists { ptype, body } => Rc::new(MComputation::Exists {
            ptype: ptype.clone(),
            body: shift_comp(body, delta, cutoff + 1),
        }),
        MComputation::Equate { lhs, rhs, body } => Rc::new(MComputation::Equate {
            lhs: shift_val(lhs, delta, cutoff),
            rhs: shift_val(rhs, delta, cutoff),
            body: shift_comp(body, delta, cutoff),
        }),
        MComputation::Ifz { num, zk, sk } => Rc::new(MComputation::Ifz {
            num: shift_val(num, delta, cutoff),
            zk: shift_comp(zk, delta, cutoff),
            sk: shift_comp(sk, delta, cutoff + 1),
        }),
        MComputation::Match { list, nilk, consk } => Rc::new(MComputation::Match {
            list: shift_val(list, delta, cutoff),
            nilk: shift_comp(nilk, delta, cutoff),
            consk: shift_comp(consk, delta, cutoff + 2),
        }),
        MComputation::Case { sum, inlk, inrk } => Rc::new(MComputation::Case {
            sum: shift_val(sum, delta, cutoff),
            inlk: shift_comp(inlk, delta, cutoff + 1),
            inrk: shift_comp(inrk, delta, cutoff + 1),
        }),
        MComputation::Rec { body } => Rc::new(MComputation::Rec {
            body: shift_comp(body, delta, cutoff + 1),
        }),
    }
}

// --- De Bruijn substitution ---
// subst_val/subst_comp replace Var(depth) with shift(repl, depth, 0),
// and decrement all Var(i) where i > depth.

fn subst_val(val: &Rc<MValue>, repl: &Rc<MValue>, depth: usize) -> Rc<MValue> {
    match &**val {
        MValue::Var(i) => {
            if *i == depth {
                shift_val(repl, depth as isize, 0)
            } else if *i > depth {
                Rc::new(MValue::Var(i - 1))
            } else {
                val.clone()
            }
        }
        MValue::Zero | MValue::Nil => val.clone(),
        MValue::Succ(v) => Rc::new(MValue::Succ(subst_val(v, repl, depth))),
        MValue::Pair(a, b) => Rc::new(MValue::Pair(
            subst_val(a, repl, depth),
            subst_val(b, repl, depth),
        )),
        MValue::Inl(v) => Rc::new(MValue::Inl(subst_val(v, repl, depth))),
        MValue::Inr(v) => Rc::new(MValue::Inr(subst_val(v, repl, depth))),
        MValue::Cons(h, t) => Rc::new(MValue::Cons(
            subst_val(h, repl, depth),
            subst_val(t, repl, depth),
        )),
        MValue::Thunk(c) => Rc::new(MValue::Thunk(subst_comp(c, repl, depth))),
    }
}

fn subst_comp(comp: &Rc<MComputation>, repl: &Rc<MValue>, depth: usize) -> Rc<MComputation> {
    match &**comp {
        MComputation::Return(v) => Rc::new(MComputation::Return(subst_val(v, repl, depth))),
        MComputation::Bind { comp: c, cont } => Rc::new(MComputation::Bind {
            comp: subst_comp(c, repl, depth),
            cont: subst_comp(cont, repl, depth + 1),
        }),
        MComputation::Force(v) => Rc::new(MComputation::Force(subst_val(v, repl, depth))),
        MComputation::Lambda { body } => Rc::new(MComputation::Lambda {
            body: subst_comp(body, repl, depth + 1),
        }),
        MComputation::App { op, arg } => Rc::new(MComputation::App {
            op: subst_comp(op, repl, depth),
            arg: subst_val(arg, repl, depth),
        }),
        MComputation::Choice(cs) => Rc::new(MComputation::Choice(
            cs.iter().map(|c| subst_comp(c, repl, depth)).collect(),
        )),
        MComputation::Exists { ptype, body } => Rc::new(MComputation::Exists {
            ptype: ptype.clone(),
            body: subst_comp(body, repl, depth + 1),
        }),
        MComputation::Equate { lhs, rhs, body } => Rc::new(MComputation::Equate {
            lhs: subst_val(lhs, repl, depth),
            rhs: subst_val(rhs, repl, depth),
            body: subst_comp(body, repl, depth),
        }),
        MComputation::Ifz { num, zk, sk } => Rc::new(MComputation::Ifz {
            num: subst_val(num, repl, depth),
            zk: subst_comp(zk, repl, depth),
            sk: subst_comp(sk, repl, depth + 1),
        }),
        MComputation::Match { list, nilk, consk } => Rc::new(MComputation::Match {
            list: subst_val(list, repl, depth),
            nilk: subst_comp(nilk, repl, depth),
            consk: subst_comp(consk, repl, depth + 2),
        }),
        MComputation::Case { sum, inlk, inrk } => Rc::new(MComputation::Case {
            sum: subst_val(sum, repl, depth),
            inlk: subst_comp(inlk, repl, depth + 1),
            inrk: subst_comp(inrk, repl, depth + 1),
        }),
        MComputation::Rec { body } => Rc::new(MComputation::Rec {
            body: subst_comp(body, repl, depth + 1),
        }),
    }
}

// --- Helpers ---

/// Check if a value structurally contains `needle` as a strict sub-value.
/// Used for cycle detection in equate: V =:= C[V] → fail.
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
        MValue::Zero | MValue::Nil => false,
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
fn swap_val(val: &Rc<MValue>, depth: usize) -> Rc<MValue> {
    match &**val {
        MValue::Var(i) => {
            if *i == depth {
                Rc::new(MValue::Var(depth + 1))
            } else if *i == depth + 1 {
                Rc::new(MValue::Var(depth))
            } else {
                val.clone()
            }
        }
        MValue::Zero | MValue::Nil => val.clone(),
        MValue::Succ(v) => Rc::new(MValue::Succ(swap_val(v, depth))),
        MValue::Pair(a, b) => Rc::new(MValue::Pair(swap_val(a, depth), swap_val(b, depth))),
        MValue::Inl(v) => Rc::new(MValue::Inl(swap_val(v, depth))),
        MValue::Inr(v) => Rc::new(MValue::Inr(swap_val(v, depth))),
        MValue::Cons(h, t) => Rc::new(MValue::Cons(swap_val(h, depth), swap_val(t, depth))),
        MValue::Thunk(c) => Rc::new(MValue::Thunk(swap_comp(c, depth))),
    }
}

fn swap_comp(comp: &Rc<MComputation>, depth: usize) -> Rc<MComputation> {
    match &**comp {
        MComputation::Return(v) => Rc::new(MComputation::Return(swap_val(v, depth))),
        MComputation::Bind { comp: c, cont } => Rc::new(MComputation::Bind {
            comp: swap_comp(c, depth),
            cont: swap_comp(cont, depth + 1),
        }),
        MComputation::Force(v) => Rc::new(MComputation::Force(swap_val(v, depth))),
        MComputation::Lambda { body } => Rc::new(MComputation::Lambda {
            body: swap_comp(body, depth + 1),
        }),
        MComputation::App { op, arg } => Rc::new(MComputation::App {
            op: swap_comp(op, depth),
            arg: swap_val(arg, depth),
        }),
        MComputation::Choice(cs) => Rc::new(MComputation::Choice(
            cs.iter().map(|c| swap_comp(c, depth)).collect(),
        )),
        MComputation::Exists { ptype, body } => Rc::new(MComputation::Exists {
            ptype: ptype.clone(),
            body: swap_comp(body, depth + 1),
        }),
        MComputation::Equate { lhs, rhs, body } => Rc::new(MComputation::Equate {
            lhs: swap_val(lhs, depth),
            rhs: swap_val(rhs, depth),
            body: swap_comp(body, depth),
        }),
        MComputation::Ifz { num, zk, sk } => Rc::new(MComputation::Ifz {
            num: swap_val(num, depth),
            zk: swap_comp(zk, depth),
            sk: swap_comp(sk, depth + 1),
        }),
        MComputation::Match { list, nilk, consk } => Rc::new(MComputation::Match {
            list: swap_val(list, depth),
            nilk: swap_comp(nilk, depth),
            consk: swap_comp(consk, depth + 2),
        }),
        MComputation::Case { sum, inlk, inrk } => Rc::new(MComputation::Case {
            sum: swap_val(sum, depth),
            inlk: swap_comp(inlk, depth + 1),
            inrk: swap_comp(inrk, depth + 1),
        }),
        MComputation::Rec { body } => Rc::new(MComputation::Rec {
            body: swap_comp(body, depth + 1),
        }),
    }
}

/// Conservative totality check: is this computation guaranteed to return?
fn is_total(comp: &MComputation) -> bool {
    match comp {
        MComputation::Return(_) => true,
        MComputation::Bind { comp: c, cont } => is_total(c) && is_total(cont),
        MComputation::Ifz { zk, sk, .. } => is_total(zk) && is_total(sk),
        MComputation::Match { nilk, consk, .. } => is_total(nilk) && is_total(consk),
        MComputation::Case { inlk, inrk, .. } => is_total(inlk) && is_total(inrk),
        _ => false,
    }
}

// --- Optimizer ---

/// Max continuation size (in AST nodes) for Pull-Choice to duplicate.
const PULL_CHOICE_THRESHOLD: usize = 32;

fn is_fail(comp: &MComputation) -> bool {
    matches!(comp, MComputation::Choice(cs) if cs.is_empty())
}

fn fail() -> Rc<MComputation> {
    Rc::new(MComputation::Choice(vec![]))
}

fn comp_size(comp: &MComputation) -> usize {
    comp.count_nodes()
}

/// Optimize a value (recurse into subterms; optimize computations inside Thunks).
fn opt_val(val: &Rc<MValue>) -> Rc<MValue> {
    match &**val {
        MValue::Thunk(c) => Rc::new(MValue::Thunk(opt_comp(c))),
        MValue::Succ(v) => Rc::new(MValue::Succ(opt_val(v))),
        MValue::Pair(a, b) => Rc::new(MValue::Pair(opt_val(a), opt_val(b))),
        MValue::Inl(v) => Rc::new(MValue::Inl(opt_val(v))),
        MValue::Inr(v) => Rc::new(MValue::Inr(opt_val(v))),
        MValue::Cons(h, t) => Rc::new(MValue::Cons(opt_val(h), opt_val(t))),
        _ => val.clone(), // Var, Zero, Nil
    }
}

/// Optimize a computation: first optimize all subterms (bottom-up), then rewrite.
fn opt_comp(comp: &Rc<MComputation>) -> Rc<MComputation> {
    let rebuilt = opt_subterms(comp);
    rewrite(&rebuilt)
}

/// Recursively optimize all immediate subterms of a computation.
fn opt_subterms(comp: &Rc<MComputation>) -> Rc<MComputation> {
    match &**comp {
        MComputation::Return(v) => Rc::new(MComputation::Return(opt_val(v))),
        MComputation::Bind { comp: c, cont } => Rc::new(MComputation::Bind {
            comp: opt_comp(c),
            cont: opt_comp(cont),
        }),
        MComputation::Force(v) => Rc::new(MComputation::Force(opt_val(v))),
        MComputation::Lambda { body } => Rc::new(MComputation::Lambda {
            body: opt_comp(body),
        }),
        MComputation::App { op, arg } => Rc::new(MComputation::App {
            op: opt_comp(op),
            arg: opt_val(arg),
        }),
        MComputation::Choice(cs) => {
            Rc::new(MComputation::Choice(cs.iter().map(|c| opt_comp(c)).collect()))
        }
        MComputation::Exists { ptype, body } => Rc::new(MComputation::Exists {
            ptype: ptype.clone(),
            body: opt_comp(body),
        }),
        MComputation::Equate { lhs, rhs, body } => Rc::new(MComputation::Equate {
            lhs: opt_val(lhs),
            rhs: opt_val(rhs),
            body: opt_comp(body),
        }),
        MComputation::Ifz { num, zk, sk } => Rc::new(MComputation::Ifz {
            num: opt_val(num),
            zk: opt_comp(zk),
            sk: opt_comp(sk),
        }),
        MComputation::Match { list, nilk, consk } => Rc::new(MComputation::Match {
            list: opt_val(list),
            nilk: opt_comp(nilk),
            consk: opt_comp(consk),
        }),
        MComputation::Case { sum, inlk, inrk } => Rc::new(MComputation::Case {
            sum: opt_val(sum),
            inlk: opt_comp(inlk),
            inrk: opt_comp(inrk),
        }),
        MComputation::Rec { body } => Rc::new(MComputation::Rec {
            body: opt_comp(body),
        }),
    }
}

/// Try rewrite rules at the top level. If a rewrite fires, re-optimize the result.
fn rewrite(comp: &Rc<MComputation>) -> Rc<MComputation> {
    match &**comp {
        // beta: return V to x. M  -->  M[V/x]
        // fail to x. M  -->  fail
        // eta: M to x. return x  -->  M
        // pull-choice: (M1 || M2) to x. N  -->  (M1 to x. N) || (M2 to x. N)
        // pull-exists: (exists z:s. M) to x. N  -->  exists z:s. (M to x. N')
        // pull-equate: (V =:= W. M) to x. N  -->  V =:= W. (M to x. N)
        MComputation::Bind { comp: c, cont } => {
            if let MComputation::Return(v) = &**c {
                return opt_comp(&subst_comp(cont, v, 0));
            }
            if is_fail(c) {
                return fail();
            }
            if let MComputation::Return(v) = &**cont {
                if matches!(&**v, MValue::Var(0)) {
                    return c.clone();
                }
            }
            // Dead-End: M to x. fail  -->  fail  (when M is guaranteed to return)
            if is_fail(cont) && is_total(c) {
                #[cfg(feature = "opt-stats")]
                stats::bump("dead-end");
                return fail();
            }
            // Bind-assoc: (M to x. return V) to y. P → M to x. P[V/y]
            // Right-associates when inner cont is Return (exposes bind-return beta)
            // or is an effect (exposes pull laws)
            if let MComputation::Bind {
                comp: inner_c,
                cont: inner_k,
            } = &**c
            {
                match &**inner_k {
                    MComputation::Return(_)
                    | MComputation::Exists { .. }
                    | MComputation::Equate { .. } => {
                        let shifted_cont = shift_comp(cont, 1, 1);
                        return opt_comp(&Rc::new(MComputation::Bind {
                            comp: inner_c.clone(),
                            cont: Rc::new(MComputation::Bind {
                                comp: inner_k.clone(),
                                cont: shifted_cont,
                            }),
                        }));
                    }
                    MComputation::Choice(branches)
                        if !branches.is_empty()
                            && comp_size(cont) <= PULL_CHOICE_THRESHOLD =>
                    {
                        let shifted_cont = shift_comp(cont, 1, 1);
                        return opt_comp(&Rc::new(MComputation::Bind {
                            comp: inner_c.clone(),
                            cont: Rc::new(MComputation::Bind {
                                comp: inner_k.clone(),
                                cont: shifted_cont,
                            }),
                        }));
                    }
                    _ => {}
                }
            }
            // Pull-Choice (with size heuristic to avoid blowup)
            if let MComputation::Choice(branches) = &**c {
                if !branches.is_empty() && comp_size(cont) <= PULL_CHOICE_THRESHOLD {
                    let new_branches: Vec<Rc<MComputation>> = branches
                        .iter()
                        .map(|b| {
                            Rc::new(MComputation::Bind {
                                comp: b.clone(),
                                cont: cont.clone(),
                            })
                        })
                        .collect();
                    return opt_comp(&Rc::new(MComputation::Choice(new_branches)));
                }
            }
            // Pull-Exists (no duplication — always apply)
            if let MComputation::Exists { ptype, body } = &**c {
                let shifted_cont = shift_comp(cont, 1, 1);
                return opt_comp(&Rc::new(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: Rc::new(MComputation::Bind {
                        comp: body.clone(),
                        cont: shifted_cont,
                    }),
                }));
            }
            // Pull-Equate (no duplication — always apply)
            if let MComputation::Equate { lhs, rhs, body } = &**c {
                return opt_comp(&Rc::new(MComputation::Equate {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                    body: Rc::new(MComputation::Bind {
                        comp: body.clone(),
                        cont: cont.clone(),
                    }),
                }));
            }
            comp.clone()
        }

        // beta: force(thunk M)  -->  M
        MComputation::Force(v) => {
            if let MValue::Thunk(c) = &**v {
                return opt_comp(c);
            }
            comp.clone()
        }

        // beta: (lam x. M)(V)  -->  M[V/x]
        // app-bind: (M to x. N)(V)  -->  M to x. N(V)
        MComputation::App { op, arg } => {
            if let MComputation::Lambda { body } = &**op {
                return opt_comp(&subst_comp(body, arg, 0));
            }
            if let MComputation::Bind { comp: c, cont } = &**op {
                #[cfg(feature = "opt-stats")]
                stats::bump("app-bind");
                return opt_comp(&Rc::new(MComputation::Bind {
                    comp: c.clone(),
                    cont: Rc::new(MComputation::App {
                        op: cont.clone(),
                        arg: shift_val(arg, 1, 0),
                    }),
                }));
            }
            comp.clone()
        }

        // Choice: flatten nested choices, remove fail branches, unwrap singletons
        MComputation::Choice(cs) => {
            let mut flat = Vec::new();
            let mut changed = false;
            for c in cs {
                match &**c {
                    MComputation::Choice(inner) => {
                        changed = true;
                        for ic in inner {
                            if !is_fail(ic) {
                                flat.push(ic.clone());
                            }
                        }
                    }
                    _ if is_fail(c) => {
                        changed = true;
                    }
                    _ => {
                        flat.push(c.clone());
                    }
                }
            }
            if !changed {
                return comp.clone();
            }
            match flat.len() {
                0 => fail(),
                1 => flat.into_iter().next().unwrap(),
                _ => Rc::new(MComputation::Choice(flat)),
            }
        }

        // exists fail  -->  fail
        MComputation::Exists { body, .. } => {
            if is_fail(body) {
                return fail();
            }
            comp.clone()
        }

        // equate V W fail  -->  fail
        // equate V V M  -->  M  (reflexivity)
        // equate V C[V] M  -->  fail  (cycle detection)
        // equate V W (exists x:s. M)  -->  exists x:s. equate V W M
        // equate V W (M || N)  -->  (equate V W M) || (equate V W N)
        // + parameter laws: constructor decomposition and mismatch
        MComputation::Equate { lhs, rhs, body } => {
            if is_fail(body) {
                return fail();
            }
            if lhs == rhs {
                return body.clone();
            }
            // Cycle detection: V =:= C[V] or C[V] =:= V → fail
            if val_contains(lhs, rhs) || val_contains(rhs, lhs) {
                #[cfg(feature = "opt-stats")]
                stats::bump("cycle");
                return fail();
            }
            // Equate-Exists: V =:= W. (∃x:σ.M) = ∃x:σ. V =:= W. M
            if let MComputation::Exists { ptype, body: ebody } = &**body {
                #[cfg(feature = "opt-stats")]
                stats::bump("eq-exists");
                return opt_comp(&Rc::new(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: Rc::new(MComputation::Equate {
                        lhs: shift_val(lhs, 1, 0),
                        rhs: shift_val(rhs, 1, 0),
                        body: ebody.clone(),
                    }),
                }));
            }
            // Equate-Choice: V =:= W. (M || N) = (V =:= W. M) || (V =:= W. N)
            if let MComputation::Choice(branches) = &**body {
                if !branches.is_empty() {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("eq-choice");
                    let new_branches: Vec<_> = branches
                        .iter()
                        .map(|b| {
                            Rc::new(MComputation::Equate {
                                lhs: lhs.clone(),
                                rhs: rhs.clone(),
                                body: b.clone(),
                            })
                        })
                        .collect();
                    return opt_comp(&Rc::new(MComputation::Choice(new_branches)));
                }
            }
            match (&**lhs, &**rhs) {
                // Succ-Succ decomposition
                (MValue::Succ(v), MValue::Succ(w)) => {

                    return opt_comp(&Rc::new(MComputation::Equate {
                        lhs: v.clone(),
                        rhs: w.clone(),
                        body: body.clone(),
                    }));
                }
                // Succ-Zero mismatch
                (MValue::Succ(_), MValue::Zero) | (MValue::Zero, MValue::Succ(_)) => {

                    return fail();
                }
                // Cons-Cons decomposition
                (MValue::Cons(v1, w1), MValue::Cons(v2, w2)) => {

                    return opt_comp(&Rc::new(MComputation::Equate {
                        lhs: v1.clone(),
                        rhs: v2.clone(),
                        body: Rc::new(MComputation::Equate {
                            lhs: w1.clone(),
                            rhs: w2.clone(),
                            body: body.clone(),
                        }),
                    }));
                }
                // Cons-Nil mismatch
                (MValue::Cons(..), MValue::Nil) | (MValue::Nil, MValue::Cons(..)) => {

                    return fail();
                }
                // Pair decomposition
                (MValue::Pair(v1, v2), MValue::Pair(w1, w2)) => {

                    return opt_comp(&Rc::new(MComputation::Equate {
                        lhs: v1.clone(),
                        rhs: w1.clone(),
                        body: Rc::new(MComputation::Equate {
                            lhs: v2.clone(),
                            rhs: w2.clone(),
                            body: body.clone(),
                        }),
                    }));
                }
                // Inl-Inl / Inr-Inr decomposition
                (MValue::Inl(v), MValue::Inl(w)) | (MValue::Inr(v), MValue::Inr(w)) => {

                    return opt_comp(&Rc::new(MComputation::Equate {
                        lhs: v.clone(),
                        rhs: w.clone(),
                        body: body.clone(),
                    }));
                }
                // Inl-Inr mismatch
                (MValue::Inl(_), MValue::Inr(_)) | (MValue::Inr(_), MValue::Inl(_)) => {

                    return fail();
                }
                _ => {}
            }
            comp.clone()
        }

        // lam x. fail  -->  fail
        // lam x. (M || N)  -->  (lam x. M) || (lam x. N)
        // lam x. (exists z:s. M)  -->  exists z:s. (lam x. M')  [swap binders]
        // lam x. (V =:= W. M)  -->  V' =:= W'. (lam x. M)  [if V,W don't ref x]
        MComputation::Lambda { body } => {
            if is_fail(body) {
                return fail();
            }
            if let MComputation::Choice(branches) = &**body {
                if !branches.is_empty() {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-choice");
                    let new_branches: Vec<_> = branches
                        .iter()
                        .map(|b| Rc::new(MComputation::Lambda { body: b.clone() }))
                        .collect();
                    return opt_comp(&Rc::new(MComputation::Choice(new_branches)));
                }
            }
            if let MComputation::Exists { ptype, body: ebody } = &**body {
                #[cfg(feature = "opt-stats")]
                stats::bump("lam-exists");
                // Swap the lambda and exists binders
                return opt_comp(&Rc::new(MComputation::Exists {
                    ptype: ptype.clone(),
                    body: Rc::new(MComputation::Lambda {
                        body: swap_comp(ebody, 0),
                    }),
                }));
            }
            if let MComputation::Equate { lhs, rhs, body: ebody } = &**body {
                // Only if lhs, rhs don't reference Var(0) (the lambda variable)
                if !has_free_var_val(lhs, 0) && !has_free_var_val(rhs, 0) {
                    #[cfg(feature = "opt-stats")]
                    stats::bump("lam-equate");
                    return opt_comp(&Rc::new(MComputation::Equate {
                        lhs: shift_val(lhs, -1, 0),
                        rhs: shift_val(rhs, -1, 0),
                        body: Rc::new(MComputation::Lambda { body: ebody.clone() }),
                    }));
                }
            }
            comp.clone()
        }

        // beta: ifz(0, M, n.N)  -->  M
        // beta: ifz(succ V, M, n.N)  -->  N[V/n]
        MComputation::Ifz { num, zk, sk } => match &**num {
            MValue::Zero => zk.clone(),
            MValue::Succ(v) => opt_comp(&subst_comp(sk, v, 0)),
            _ => comp.clone(),
        },

        // beta: match(nil, M, _)  -->  M
        // beta: match(cons(V,W), _, N)  -->  N[W/0][V/0]
        MComputation::Match { list, nilk, consk } => match &**list {
            MValue::Nil => nilk.clone(),
            MValue::Cons(v, w) => {
                // consk binds: Var(0) = tail (w), Var(1) = head (v)
                let step1 = subst_comp(consk, w, 0);
                let step2 = subst_comp(&step1, v, 0);
                opt_comp(&step2)
            }
            _ => comp.clone(),
        },

        // beta: case(inl V, M, _)  -->  M[V/x]
        // beta: case(inr W, _, N)  -->  N[W/x]
        MComputation::Case { sum, inlk, inrk } => match &**sum {
            MValue::Inl(v) => opt_comp(&subst_comp(inlk, v, 0)),
            MValue::Inr(v) => opt_comp(&subst_comp(inrk, v, 0)),
            _ => comp.clone(),
        },

        _ => comp.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ret(v: MValue) -> Rc<MComputation> {
        Rc::new(MComputation::Return(Rc::new(v)))
    }

    fn bind(c: Rc<MComputation>, k: Rc<MComputation>) -> Rc<MComputation> {
        Rc::new(MComputation::Bind { comp: c, cont: k })
    }

    fn var(i: usize) -> Rc<MValue> {
        Rc::new(MValue::Var(i))
    }

    #[test]
    fn bind_return_beta() {
        // (return 0) to x. return (succ x) --> return (succ 0)
        let term = bind(
            ret(MValue::Zero),
            ret(MValue::Succ(var(0))),
        );
        let result = opt_comp(&term);
        let expected = ret(MValue::Succ(Rc::new(MValue::Zero)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn bind_return_chain() {
        // (return 0) to x. (return x) to y. return (succ y) --> return (succ 0)
        let term = bind(
            ret(MValue::Zero),
            bind(
                ret(MValue::Var(0)),
                ret(MValue::Succ(var(0))),
            ),
        );
        let result = opt_comp(&term);
        let expected = ret(MValue::Succ(Rc::new(MValue::Zero)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn force_thunk_beta() {
        // force(thunk(return 0)) --> return 0
        let inner = Rc::new(MComputation::Return(Rc::new(MValue::Zero)));
        let term = Rc::new(MComputation::Force(Rc::new(MValue::Thunk(inner.clone()))));
        let result = opt_comp(&term);
        assert_eq!(*result, *inner);
    }

    #[test]
    fn fail_to_is_fail() {
        // fail to x. M --> fail
        let term = bind(
            Rc::new(MComputation::Choice(vec![])),
            ret(MValue::Succ(var(0))),
        );
        let result = opt_comp(&term);
        assert!(is_fail(&result));
    }

    #[test]
    fn choice_removes_fail_branches() {
        // (fail [] return 0) --> return 0
        let term = Rc::new(MComputation::Choice(vec![
            Rc::new(MComputation::Choice(vec![])),
            ret(MValue::Zero),
        ]));
        let result = opt_comp(&term);
        assert_eq!(*result, *ret(MValue::Zero));
    }

    #[test]
    fn bind_return_eta() {
        // M to x. return x --> M
        let m = ret(MValue::Zero);
        let term = bind(m.clone(), ret(MValue::Var(0)));
        let result = opt_comp(&term);
        assert_eq!(*result, *m);
    }

    #[test]
    fn exists_fail() {
        use crate::machine::value_type::ValueType;
        let term = Rc::new(MComputation::Exists {
            ptype: ValueType::Nat,
            body: Rc::new(MComputation::Choice(vec![])),
        });
        let result = opt_comp(&term);
        assert!(is_fail(&result));
    }

    #[test]
    fn equate_refl() {
        let v = Rc::new(MValue::Zero);
        let body = ret(MValue::Succ(Rc::new(MValue::Zero)));
        let term = Rc::new(MComputation::Equate {
            lhs: v.clone(),
            rhs: v,
            body: body.clone(),
        });
        let result = opt_comp(&term);
        assert_eq!(*result, *body);
    }

    #[test]
    fn ifz_zero_beta() {
        let zk = ret(MValue::Nil);
        let sk = ret(MValue::Succ(var(0)));
        let term = Rc::new(MComputation::Ifz {
            num: Rc::new(MValue::Zero),
            zk: zk.clone(),
            sk,
        });
        let result = opt_comp(&term);
        assert_eq!(*result, *zk);
    }

    #[test]
    fn ifz_succ_beta() {
        // ifz(succ(0), zk, n. return (succ n)) --> return (succ 0)
        let term = Rc::new(MComputation::Ifz {
            num: Rc::new(MValue::Succ(Rc::new(MValue::Zero))),
            zk: ret(MValue::Nil),
            sk: ret(MValue::Succ(var(0))),
        });
        let result = opt_comp(&term);
        let expected = ret(MValue::Succ(Rc::new(MValue::Zero)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn match_nil_beta() {
        let nilk = ret(MValue::Zero);
        let consk = ret(MValue::Pair(var(1), var(0)));
        let term = Rc::new(MComputation::Match {
            list: Rc::new(MValue::Nil),
            nilk: nilk.clone(),
            consk,
        });
        let result = opt_comp(&term);
        assert_eq!(*result, *nilk);
    }

    #[test]
    fn match_cons_beta() {
        // match(cons(0, nil), nilk, x.xs. return (x, xs)) --> return (0, nil)
        let term = Rc::new(MComputation::Match {
            list: Rc::new(MValue::Cons(Rc::new(MValue::Zero), Rc::new(MValue::Nil))),
            nilk: ret(MValue::Nil),
            consk: ret(MValue::Pair(var(1), var(0))),
        });
        let result = opt_comp(&term);
        let expected = ret(MValue::Pair(Rc::new(MValue::Zero), Rc::new(MValue::Nil)));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn nested_bind_return_succ_succ() {
        // Translation of succ(succ(x)) where x = Var(0):
        // (return x) to a. (return (succ a)) to b. return (succ b)
        // --> return (succ (succ x))
        let term = bind(
            ret(MValue::Var(0)),
            bind(
                ret(MValue::Succ(var(0))),
                ret(MValue::Succ(var(0))),
            ),
        );
        let result = opt_comp(&term);
        let expected = ret(MValue::Succ(Rc::new(MValue::Succ(var(0)))));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_choice() {
        // (return 0 [] return 1) to x. return (succ x)
        // --> (return (succ 0)) [] (return (succ 1))
        let term = bind(
            Rc::new(MComputation::Choice(vec![ret(MValue::Zero), ret(MValue::Succ(Rc::new(MValue::Zero)))])),
            ret(MValue::Succ(var(0))),
        );
        let result = opt_comp(&term);
        let expected = Rc::new(MComputation::Choice(vec![
            ret(MValue::Succ(Rc::new(MValue::Zero))),
            ret(MValue::Succ(Rc::new(MValue::Succ(Rc::new(MValue::Zero))))),
        ]));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_choice_eliminates_fail_branch() {
        // (return 0 [] fail) to x. return x --> return 0
        let term = bind(
            Rc::new(MComputation::Choice(vec![
                ret(MValue::Zero),
                Rc::new(MComputation::Choice(vec![])),
            ])),
            ret(MValue::Var(0)),
        );
        let result = opt_comp(&term);
        assert_eq!(*result, *ret(MValue::Zero));
    }

    #[test]
    fn pull_exists() {
        use crate::machine::value_type::ValueType;
        // (exists z:Nat. return z) to x. return (succ x) --> exists z:Nat. return (succ z)
        let term = bind(
            Rc::new(MComputation::Exists {
                ptype: ValueType::Nat,
                body: ret(MValue::Var(0)),
            }),
            ret(MValue::Succ(var(0))),
        );
        let result = opt_comp(&term);
        let expected = Rc::new(MComputation::Exists {
            ptype: ValueType::Nat,
            body: ret(MValue::Succ(var(0))),
        });
        assert_eq!(*result, *expected);
    }

    #[test]
    fn pull_equate() {
        // (0 =:= 0. return 1) to x. return (succ x) --> return (succ 1)
        // (equate-refl fires first, then bind-return)
        let one: Rc<MValue> = Rc::new(MValue::Succ(Rc::new(MValue::Zero)));
        let term = bind(
            Rc::new(MComputation::Equate {
                lhs: Rc::new(MValue::Zero),
                rhs: Rc::new(MValue::Zero),
                body: Rc::new(MComputation::Return(one.clone())),
            }),
            ret(MValue::Succ(var(0))),
        );
        let result = opt_comp(&term);
        let expected = ret(MValue::Succ(one));
        assert_eq!(*result, *expected);
    }

    #[test]
    fn equate_succ_succ_decompose() {
        // succ(0) =:= succ(0). M --> M
        let body = ret(MValue::Nil);
        let term = Rc::new(MComputation::Equate {
            lhs: Rc::new(MValue::Succ(Rc::new(MValue::Zero))),
            rhs: Rc::new(MValue::Succ(Rc::new(MValue::Zero))),
            body: body.clone(),
        });
        let result = opt_comp(&term);
        assert_eq!(*result, *body);
    }

    #[test]
    fn equate_succ_zero_fail() {
        let term = Rc::new(MComputation::Equate {
            lhs: Rc::new(MValue::Succ(Rc::new(MValue::Zero))),
            rhs: Rc::new(MValue::Zero),
            body: ret(MValue::Nil),
        });
        let result = opt_comp(&term);
        assert!(is_fail(&result));
    }

    #[test]
    fn equate_cons_nil_fail() {
        let term = Rc::new(MComputation::Equate {
            lhs: Rc::new(MValue::Cons(Rc::new(MValue::Zero), Rc::new(MValue::Nil))),
            rhs: Rc::new(MValue::Nil),
            body: ret(MValue::Nil),
        });
        let result = opt_comp(&term);
        assert!(is_fail(&result));
    }

    #[test]
    fn equate_pair_decompose() {
        // (0, 1) =:= (0, 1). M --> M
        let one: Rc<MValue> = Rc::new(MValue::Succ(Rc::new(MValue::Zero)));
        let body = ret(MValue::Nil);
        let term = Rc::new(MComputation::Equate {
            lhs: Rc::new(MValue::Pair(Rc::new(MValue::Zero), one.clone())),
            rhs: Rc::new(MValue::Pair(Rc::new(MValue::Zero), one)),
            body: body.clone(),
        });
        let result = opt_comp(&term);
        assert_eq!(*result, *body);
    }
}
