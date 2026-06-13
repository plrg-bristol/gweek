use std::collections::{HashMap, HashSet, VecDeque};

use bumpalo::Bump;

use crate::machine::value_type::ValueType;
use crate::parser::{arg::Arg, bexpr::BExpr, cases::CasesType, decl::Decl, expr::Expr, stmt::Stmt, r#type::Type};

use super::mterms::{MComputation, MValue};

struct TEnv {
    env: Vec<String>,
    /// Names of nullary functions (thunks that need forcing at use sites).
    nullary: HashSet<String>,
}

impl TEnv {
    fn new() -> TEnv {
        TEnv { env: vec![], nullary: HashSet::new() }
    }

    /*
    The location of a variable in the current execution environment
    is the number of variables that have been declared after it.
    Therefore we need to return the location of the last instance of
    a variable relative to the end of the vector.
    */
    fn find(&self, v: &str) -> usize {
        self.env
            .iter()
            .rev()
            .position(|x| x == v)
            .unwrap_or_else(|| panic!("Variable {} not found in environment", v))
    }

    fn is_nullary(&self, v: &str) -> bool {
        self.nullary.contains(v)
    }

    fn bind(&mut self, v: &str) {
        self.env.push(v.to_owned())
    }

    fn bind_nullary(&mut self, v: &str) {
        self.nullary.insert(v.to_owned());
        self.env.push(v.to_owned())
    }

    fn unbind(&mut self) {
        self.env.pop();
    }
}

/*
Translates CBV representation of terms into CBPV.
A term in the AST is either the type of a function
(FuncType), the definition of a function (Func),
or else the main program (Stmt).

Returns a pair whose first component is the main
program and second is the environment of function
names and definitions.
*/
pub fn translate<'a>(arena: &'a Bump, ast: Vec<Decl>) -> (&'a MComputation<'a>, Vec<&'a MValue<'a>>) {
    let ast = reorder_decls(ast);

    let sigs: HashMap<String, Type> = ast
        .iter()
        .filter_map(|d| match d {
            Decl::FuncType { name, r#type } => Some((name.clone(), r#type.clone())),
            _ => None,
        })
        .collect();

    let mut env = Vec::new();
    let mut tenv = TEnv::new();
    let mut main = None;

    for decl in ast {
        match decl {
            Decl::FuncType { .. } => (),
            Decl::Func { name, args, body } => {
                let nullary = args.is_empty();
                let arg_types = arg_types(sigs.get(&name), args.len());
                let result = translate_func(arena, &name, args, &arg_types, body, &mut tenv);
                if nullary {
                    tenv.bind_nullary(&name);
                } else {
                    tenv.bind(&name);
                }
                env.push(result);
            }
            Decl::Stmt(stmt) => {
                main = Some(translate_stmt(arena, stmt, &mut tenv));
            }
        }
    }

    (main.expect("empty program"), env)
}

/// Peels the first `n` argument types off a function signature.
/// Missing types (untyped functions) are reported as `None`.
fn arg_types(sig: Option<&Type>, n: usize) -> Vec<Option<Type>> {
    let mut ty = sig;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        match ty {
            Some(Type::Arrow(a, b)) => {
                out.push(Some((**a).clone()));
                ty = Some(b);
            }
            _ => out.push(None),
        }
    }
    out
}

// --- Declaration reordering (topological sort) ---

fn reorder_decls(ast: Vec<Decl>) -> Vec<Decl> {
    // Collect only the function names from the AST
    let func_names: HashSet<String> = ast
        .iter()
        .filter_map(|d| match d {
            Decl::Func { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();

    // Group declarations: each function with its optional preceding type signature
    let mut func_decls: Vec<(String, Vec<Decl>)> = Vec::new();
    let mut stms: Vec<Decl> = Vec::new();
    let mut pending_type: Option<Decl> = None;

    for decl in ast {
        match &decl {
            Decl::FuncType { .. } => pending_type = Some(decl),
            Decl::Func { name, .. } => {
                let mut group = Vec::new();
                if let Some(t) = pending_type.take() {
                    group.push(t);
                }
                let nm = name.clone();
                group.push(decl);
                func_decls.push((nm, group));
            }
            Decl::Stmt(_) => {
                if let Some(t) = pending_type.take() {
                    stms.push(t);
                }
                stms.push(decl);
            }
        }
    }

    let name_to_idx: HashMap<String, usize> = func_decls
        .iter()
        .enumerate()
        .map(|(i, (name, _))| (name.clone(), i))
        .collect();

    // Build dependency graph
    let n = func_decls.len();
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut in_deg: Vec<usize> = vec![0; n];

    for (i, (name, group)) in func_decls.iter().enumerate() {
        let body = group
            .iter()
            .find_map(|d| match d {
                Decl::Func { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let refs = collect_refs_stmt(body, &func_names);
        for r in &refs {
            if r != name {
                if let Some(&j) = name_to_idx.get(r) {
                    successors[j].push(i);
                    in_deg[i] += 1;
                }
            }
        }
    }

    // Kahn's algorithm
    let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_deg[i] == 0).collect();
    let mut order: Vec<usize> = Vec::with_capacity(n);
    while let Some(j) = queue.pop_front() {
        order.push(j);
        for &i in &successors[j] {
            in_deg[i] -= 1;
            if in_deg[i] == 0 {
                queue.push_back(i);
            }
        }
    }

    if order.len() < n {
        // Cycle detected — fall back to original order
        order = (0..n).collect();
    }

    // Rebuild in sorted order
    let mut func_groups: Vec<Option<Vec<Decl>>> =
        func_decls.into_iter().map(|(_, g)| Some(g)).collect();
    let mut result: Vec<Decl> = Vec::new();
    for idx in order {
        if let Some(group) = func_groups[idx].take() {
            result.extend(group);
        }
    }
    result.extend(stms);
    result
}

// --- AST walkers for dependency collection ---

fn collect_refs_stmt(stmt: &Stmt, names: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::new();
    walk_stmt(stmt, names, &mut refs);
    refs
}

fn walk_stmt(stmt: &Stmt, names: &HashSet<String>, refs: &mut HashSet<String>) {
    match stmt {
        Stmt::Expr(e) => walk_expr(e, names, refs),
        Stmt::Let { val, body, .. } => {
            walk_stmt(val, names, refs);
            walk_stmt(body, names, refs);
        }
        Stmt::Fail => (),
        Stmt::Exists { body, .. } => walk_stmt(body, names, refs),
        Stmt::Equate { lhs, rhs, body } => {
            walk_expr(lhs, names, refs);
            walk_expr(rhs, names, refs);
            walk_stmt(body, names, refs);
        }
        Stmt::Choice(exprs) => {
            for e in exprs {
                walk_expr(e, names, refs);
            }
        }
        Stmt::Case { expr, cases } => {
            walk_expr(expr, names, refs);
            if let Some(nc) = &cases.nat_case {
                if let Some(zk) = &nc.zk {
                    walk_stmt(zk, names, refs);
                }
                if let Some(sk) = &nc.sk {
                    walk_stmt(&sk.body, names, refs);
                }
            }
            if let Some(lc) = &cases.list_case {
                if let Some(nk) = &lc.nilk {
                    walk_stmt(nk, names, refs);
                }
                if let Some(ck) = &lc.consk {
                    walk_stmt(&ck.body, names, refs);
                }
            }
        }
        Stmt::If { cond, then, r#else } => {
            walk_stmt(cond, names, refs);
            walk_stmt(then, names, refs);
            walk_stmt(r#else, names, refs);
        }
    }
}

fn walk_expr(expr: &Expr, names: &HashSet<String>, refs: &mut HashSet<String>) {
    match expr {
        Expr::Ident(s) => {
            if names.contains(s) {
                refs.insert(s.clone());
            }
        }
        Expr::App(a, b) | Expr::Cons(a, b) | Expr::Pair(a, b) => {
            walk_expr(a, names, refs);
            walk_expr(b, names, refs);
        }
        Expr::Succ(e) => walk_expr(e, names, refs),
        Expr::Lambda(_, body) => walk_stmt(body, names, refs),
        Expr::List(es) => {
            for e in es {
                walk_expr(e, names, refs);
            }
        }
        Expr::BExpr(b) => walk_bexpr(b, names, refs),
        Expr::Stmt(s) => walk_stmt(s, names, refs),
        _ => {}
    }
}

fn walk_bexpr(bexpr: &BExpr, names: &HashSet<String>, refs: &mut HashSet<String>) {
    match bexpr {
        BExpr::Eq(a, b) | BExpr::NEq(a, b) | BExpr::And(a, b) | BExpr::Or(a, b) => {
            walk_expr(a, names, refs);
            walk_expr(b, names, refs);
        }
        BExpr::Not(e) => walk_expr(e, names, refs),
    }
}

// --- Translation ---

fn translate_func<'a>(
    arena: &'a Bump,
    name: &str,
    args: Vec<Arg>,
    arg_types: &[Option<Type>],
    body: Stmt,
    tenv: &mut TEnv,
) -> &'a MValue<'a> {
    tenv.bind(name);
    let comp = if args.is_empty() {
        translate_stmt(arena, body, tenv)
    } else {
        build_args(arena, &args, arg_types, &body, tenv)
    };
    tenv.unbind();
    let rec = arena.alloc(MComputation::Rec { body: comp });
    arena.alloc(MValue::Thunk(rec))
}

/// Builds the curried lambda chain for the remaining `args`, binding each
/// argument pattern and emitting the function `body` once all are consumed.
/// Returns the body of the lambda for the first remaining argument.
fn build_args<'a>(
    arena: &'a Bump,
    args: &[Arg],
    arg_types: &[Option<Type>],
    body: &Stmt,
    tenv: &mut TEnv,
) -> &'a MComputation<'a> {
    match args {
        [] => translate_stmt(arena, body.clone(), tenv),
        [arg, rest @ ..] => {
            let rest_types = &arg_types[1..];
            let lam_body = match arg {
                Arg::Ident(var) => {
                    tenv.bind(var);
                    let inner = curry(arena, rest, rest_types, body, tenv);
                    tenv.unbind();
                    inner
                }
                Arg::Pair(..) => {
                    let ty = arg_types[0]
                        .as_ref()
                        .expect("pair argument needs a declared product type");
                    tenv.bind("_");
                    let body_comp = bind_pattern(arena, arg, ty, 0, tenv, &mut |tenv| {
                        curry(arena, rest, rest_types, body, tenv)
                    });
                    tenv.unbind();
                    body_comp
                }
            };
            arena.alloc(MComputation::Lambda { body: lam_body })
        }
    }
}

/// Wraps the lambda chain for `rest` so that, when more arguments remain, the
/// inner chain is returned as a thunk (CBPV currying).
fn curry<'a>(
    arena: &'a Bump,
    rest: &[Arg],
    rest_types: &[Option<Type>],
    body: &Stmt,
    tenv: &mut TEnv,
) -> &'a MComputation<'a> {
    if rest.is_empty() {
        build_args(arena, rest, rest_types, body, tenv)
    } else {
        let inner = build_args(arena, rest, rest_types, body, tenv);
        let thunk = arena.alloc(MValue::Thunk(inner));
        arena.alloc(MComputation::Return(thunk))
    }
}

/// Collects the leaf variable names of a pattern together with their value
/// types, in left-to-right order, validating the pattern against the type.
fn collect_leaves(pattern: &Arg, ty: &Type, out: &mut Vec<(String, ValueType)>) {
    match pattern {
        Arg::Ident(name) => out.push((name.clone(), translate_vtype(ty.clone()))),
        Arg::Pair(a, b) => match ty {
            Type::Product(ta, tb) => {
                collect_leaves(a, ta, out);
                collect_leaves(b, tb, out);
            }
            _ => panic!("pair pattern against non-product type {ty}"),
        },
    }
}

/// Rebuilds the value matching `pattern`, addressing the leaf logic variables
/// by their de Bruijn index. With `m` leaves bound in left-to-right order, the
/// `j`-th leaf sits at index `(m - 1) - j`.
fn rebuild_pattern<'a>(arena: &'a Bump, pattern: &Arg, m: usize, next: &mut usize) -> &'a MValue<'a> {
    match pattern {
        Arg::Ident(_) => {
            let idx = (m - 1) - *next;
            *next += 1;
            arena.alloc(MValue::Var(idx))
        }
        Arg::Pair(a, b) => {
            let av = rebuild_pattern(arena, a, m, next);
            let bv = rebuild_pattern(arena, b, m, next);
            arena.alloc(MValue::Pair(av, bv))
        }
    }
}

/// Destructures the pair value at de Bruijn index `pair_idx` against `pattern`.
/// Introduces one fresh logic variable per leaf, unifies the reconstructed
/// pattern with the pair, then runs the continuation `k` with the leaves bound.
fn bind_pattern<'a>(
    arena: &'a Bump,
    pattern: &Arg,
    ty: &Type,
    pair_idx: usize,
    tenv: &mut TEnv,
    k: &mut dyn FnMut(&mut TEnv) -> &'a MComputation<'a>,
) -> &'a MComputation<'a> {
    let mut leaves = Vec::new();
    collect_leaves(pattern, ty, &mut leaves);
    let m = leaves.len();

    for (name, _) in &leaves {
        tenv.bind(name);
    }
    let body = k(tenv);
    for _ in &leaves {
        tenv.unbind();
    }

    let mut next = 0;
    let lhs = rebuild_pattern(arena, pattern, m, &mut next);
    let rhs = arena.alloc(MValue::Var(pair_idx + m));
    let mut comp: &MComputation = arena.alloc(MComputation::Equate { lhs, rhs, body });
    for (_, vty) in leaves.into_iter().rev() {
        comp = arena.alloc(MComputation::Exists { ptype: vty, body: comp });
    }
    comp
}

fn translate_vtype(ptype: Type) -> ValueType {
    match ptype {
        Type::Arrow(_, _) => panic!("don't translate thunks"),
        Type::Ident(s) if s == "Nat" => ValueType::Nat,
        Type::Ident(s) if s == "Bool" => {
            ValueType::Sum(Box::new(ValueType::Unit), Box::new(ValueType::Unit))
        }
        Type::Ident(s) => panic!("cannot translate type {}", s),
        Type::List(t) => ValueType::List(Box::new(translate_vtype(*t))),
        Type::Product(t1, t2) => {
            ValueType::Product(Box::new(translate_vtype(*t1)), Box::new(translate_vtype(*t2)))
        }
        Type::Any => panic!("cannot translate unresolved type"),
    }
}

fn translate_stmt<'a>(arena: &'a Bump, stmt: Stmt, tenv: &mut TEnv) -> &'a MComputation<'a> {
    match stmt {
        Stmt::If { cond, then, r#else } => {
            let comp = translate_stmt(arena, *cond, tenv);
            tenv.bind("_");
            let var0 = arena.alloc(MValue::Var(0));
            // Inl = true → then branch (bind unit, discard it)
            tenv.bind("_");
            let then_comp = translate_stmt(arena, *then, tenv);
            tenv.unbind();
            // Inr = false → else branch (bind unit, discard it)
            tenv.bind("_");
            let else_comp = translate_stmt(arena, *r#else, tenv);
            tenv.unbind();
            let case = arena.alloc(MComputation::Case {
                sum: var0,
                inlk: then_comp,
                inrk: else_comp,
            });
            tenv.unbind();
            arena.alloc(MComputation::Bind { comp, cont: case })
        }
        // The variable seems to disappear?
        Stmt::Let { var, val, body } => {
            let comp = translate_stmt(arena, *val, tenv);
            tenv.bind(&var);
            let cont = translate_stmt(arena, *body, tenv);
            tenv.unbind();
            arena.alloc(MComputation::Bind { comp, cont })
        }
        Stmt::Exists { var, r#type, body } => {
            tenv.bind(&var);
            let body = translate_stmt(arena, *body, tenv);
            tenv.unbind();
            arena.alloc(MComputation::Exists {
                ptype: translate_vtype(r#type),
                body,
            })
        }
        Stmt::Equate { lhs, rhs, body } => {
            let lhs_comp = translate_expr(arena, lhs, tenv);
            tenv.bind("_");
            let rhs_comp = translate_expr(arena, rhs, tenv);
            tenv.bind("_");
            let body_comp = translate_stmt(arena, *body, tenv);
            tenv.unbind();
            tenv.unbind();
            let var0 = arena.alloc(MValue::Var(0));
            let var1 = arena.alloc(MValue::Var(1));
            let equate = arena.alloc(MComputation::Equate {
                lhs: var0,
                rhs: var1,
                body: body_comp,
            });
            let inner_bind = arena.alloc(MComputation::Bind {
                comp: rhs_comp,
                cont: equate,
            });
            arena.alloc(MComputation::Bind {
                comp: lhs_comp,
                cont: inner_bind,
            })
        }
        Stmt::Fail => arena.alloc(MComputation::Choice(&[])),
        Stmt::Choice(exprs) => {
            let choices: Vec<_> = exprs
                .into_iter()
                .map(|e| translate_expr(arena, e, tenv))
                .collect();
            let slice = arena.alloc_slice_copy(&choices);
            arena.alloc(MComputation::Choice(slice))
        }
        Stmt::Case { expr, cases } => {
            tenv.bind("_");
            let var0 = arena.alloc(MValue::Var(0));
            let cont = match cases.r#type.unwrap() {
                CasesType::Nat => {
                    let nat_case = cases.nat_case.unwrap();
                    let zk = translate_stmt(arena, *nat_case.zk.unwrap(), tenv);
                    let succ_case = nat_case.sk.unwrap();
                    tenv.bind(&succ_case.var);
                    let sk = translate_stmt(arena, *succ_case.body, tenv);
                    tenv.unbind();
                    arena.alloc(MComputation::Ifz { num: var0, zk, sk })
                }
                CasesType::List => {
                    let list_case = cases.list_case.unwrap();
                    let nilk = translate_stmt(arena, *list_case.nilk.unwrap(), tenv);
                    let cons_case = list_case.consk.unwrap();
                    tenv.bind(&cons_case.x);
                    tenv.bind(&cons_case.xs);
                    let consk = translate_stmt(arena, *cons_case.body, tenv);
                    tenv.unbind();
                    tenv.unbind();
                    arena.alloc(MComputation::Match { list: var0, nilk, consk })
                }
            };
            tenv.unbind();
            let comp = translate_expr(arena, expr, tenv);
            arena.alloc(MComputation::Bind { comp, cont })
        }
        Stmt::Expr(e) => translate_expr(arena, e, tenv),
    }
}

fn translate_expr<'a>(arena: &'a Bump, expr: Expr, tenv: &mut TEnv) -> &'a MComputation<'a> {
    match expr {
        Expr::Zero => {
            let zero = arena.alloc(MValue::Nat(0));
            arena.alloc(MComputation::Return(zero))
        }
        Expr::Succ(body) => {
            let comp = translate_expr(arena, *body, tenv);
            let var0 = arena.alloc(MValue::Var(0));
            let succ = arena.alloc(MValue::Succ(var0));
            let ret = arena.alloc(MComputation::Return(succ));
            arena.alloc(MComputation::Bind { comp, cont: ret })
        }
        Expr::Nil => {
            let nil = arena.alloc(MValue::Nil);
            arena.alloc(MComputation::Return(nil))
        }
        Expr::Cons(x, xs) => {
            let comp_head = translate_expr(arena, *x, tenv);
            tenv.bind("_");
            let comp_tail = translate_expr(arena, *xs, tenv);
            tenv.unbind();
            let var1 = arena.alloc(MValue::Var(1));
            let var0 = arena.alloc(MValue::Var(0));
            let cons = arena.alloc(MValue::Cons(var1, var0));
            let ret = arena.alloc(MComputation::Return(cons));
            let inner = arena.alloc(MComputation::Bind { comp: comp_tail, cont: ret });
            arena.alloc(MComputation::Bind { comp: comp_head, cont: inner })
        }
        Expr::Lambda(arg, body) => match arg {
            Arg::Ident(var) => {
                tenv.bind(&var);
                let body = translate_stmt(arena, *body, tenv);
                tenv.unbind();
                let lam = arena.alloc(MComputation::Lambda { body });
                let thunk = arena.alloc(MValue::Thunk(lam));
                arena.alloc(MComputation::Return(thunk))
            }
            // Destructuring a pair needs the component types to annotate the
            // fresh logic variables (the machine has no product eliminator, so
            // projection goes through Exists/Equate). A lambda carries no type
            // annotation, and the type checker rejects every lambda use (lambdas
            // synthesize no type), so this path is unreachable for well-typed
            // programs. We refuse to fabricate types here.
            Arg::Pair(..) => panic!(
                "cannot translate a pair-pattern lambda argument: no type \
                 annotation is available to type the destructured components"
            ),
        },
        Expr::App(op, arg) => {
            let comp_op = translate_expr(arena, *op, tenv);
            tenv.bind("_");
            let comp_arg = translate_expr(arena, *arg, tenv);
            tenv.unbind();
            let var1 = arena.alloc(MValue::Var(1));
            let var0 = arena.alloc(MValue::Var(0));
            let force = arena.alloc(MComputation::Force(var1));
            let app = arena.alloc(MComputation::App { op: force, arg: var0 });
            let inner = arena.alloc(MComputation::Bind { comp: comp_arg, cont: app });
            arena.alloc(MComputation::Bind { comp: comp_op, cont: inner })
        }
        Expr::BExpr(bexpr) => translate_bexpr(arena, bexpr, tenv),
        Expr::List(elems) => translate_list(arena, &elems, tenv),
        Expr::Ident(s) => {
            let var = arena.alloc(MValue::Var(tenv.find(&s)));
            if tenv.is_nullary(&s) {
                let ret = arena.alloc(MComputation::Return(var));
                let var0 = arena.alloc(MValue::Var(0));
                let force = arena.alloc(MComputation::Force(var0));
                arena.alloc(MComputation::Bind { comp: ret, cont: force })
            } else {
                arena.alloc(MComputation::Return(var))
            }
        }
        Expr::Nat(n) => translate_nat(arena, n),
        Expr::Bool(b) => {
            let unit = arena.alloc(MValue::Unit);
            let val = if b {
                arena.alloc(MValue::Inl(unit))
            } else {
                arena.alloc(MValue::Inr(unit))
            };
            arena.alloc(MComputation::Return(val))
        }
        Expr::Pair(lhs, rhs) => translate_pair(arena, *lhs, *rhs, tenv),
        Expr::Stmt(s) => translate_stmt(arena, *s, tenv),
    }
}

/// Returns a computation that produces the `Bool` value `b`
/// (`Sum(Unit, Unit)`, `Inl` = true, `Inr` = false).
fn return_bool<'a>(arena: &'a Bump, b: bool) -> &'a MComputation<'a> {
    let unit = arena.alloc(MValue::Unit);
    let val = if b { arena.alloc(MValue::Inl(unit)) } else { arena.alloc(MValue::Inr(unit)) };
    arena.alloc(MComputation::Return(val))
}

/// Builds the closed, curried recursive equality function on `Nat`,
/// returned as a thunk. Forcing it yields `λa. return (thunk (λb. a == b))`,
/// where `a == b` evaluates to the `Bool` representation of their equality.
fn nat_eq_thunk<'a>(arena: &'a Bump) -> &'a MValue<'a> {
    let var = |i| -> &'a MValue<'a> { arena.alloc(MValue::Var(i)) };
    let ifz = |num, zk, sk| -> &'a MComputation<'a> {
        arena.alloc(MComputation::Ifz { num, zk, sk })
    };

    // Innermost comparison; environment is [b = 0, a = 1, self = 2].

    // a = 0: equal iff b = 0.
    let azero = ifz(var(0), return_bool(arena, true), return_bool(arena, false));

    // a = succ a' (env [a' = 0, b = 1, a = 2, self = 3]):
    //   b = 0   -> false
    //   b = b'  -> force self applied to a' then b'
    let recurse = {
        // env [a' = 0, b = 1, a = 2, self = 3]; ifz on b binds b' giving
        // env [b' = 0, a' = 1, b = 2, a = 3, self = 4].
        let apply_a = arena.alloc(MComputation::App {
            op: arena.alloc(MComputation::Force(var(4))),
            arg: var(1), // a'
        });
        // First application returns a thunk bound at 0; b' shifts to 1.
        let apply_b = arena.alloc(MComputation::App {
            op: arena.alloc(MComputation::Force(var(0))),
            arg: var(1), // b'
        });
        arena.alloc(MComputation::Bind { comp: apply_a, cont: apply_b })
    };
    let asucc = ifz(var(1), return_bool(arena, false), recurse);

    let compare = ifz(var(1), azero, asucc);
    let lam_b = arena.alloc(MComputation::Lambda { body: compare });
    let ret_lam_b = arena.alloc(MComputation::Return(arena.alloc(MValue::Thunk(lam_b))));
    let lam_a = arena.alloc(MComputation::Lambda { body: ret_lam_b });
    let rec = arena.alloc(MComputation::Rec { body: lam_a });
    arena.alloc(MValue::Thunk(rec))
}

/// Applies the curried `Nat` equality function (a thunk) to two argument
/// computations, yielding a computation that returns their equality `Bool`.
fn nat_eq_comp<'a>(arena: &'a Bump, lhs: Expr, rhs: Expr, tenv: &mut TEnv) -> &'a MComputation<'a> {
    let lhs_comp = translate_expr(arena, lhs, tenv);
    tenv.bind("_");
    let rhs_comp = translate_expr(arena, rhs, tenv);
    tenv.unbind();
    // Environment at the application: [b = 0, a = 1].
    let eq = nat_eq_thunk(arena);
    let apply_a = arena.alloc(MComputation::App {
        op: arena.alloc(MComputation::Force(eq)),
        arg: arena.alloc(MValue::Var(1)),
    });
    // The first application returns a thunk, bound at 0; b shifts to 1.
    let apply_b = arena.alloc(MComputation::App {
        op: arena.alloc(MComputation::Force(arena.alloc(MValue::Var(0)))),
        arg: arena.alloc(MValue::Var(1)),
    });
    let recurse = arena.alloc(MComputation::Bind { comp: apply_a, cont: apply_b });
    let inner = arena.alloc(MComputation::Bind { comp: rhs_comp, cont: recurse });
    arena.alloc(MComputation::Bind { comp: lhs_comp, cont: inner })
}

/// Negates a computation producing a `Bool` by swapping `Inl`/`Inr`.
fn negate_comp<'a>(arena: &'a Bump, comp: &'a MComputation<'a>) -> &'a MComputation<'a> {
    let case = arena.alloc(MComputation::Case {
        sum: arena.alloc(MValue::Var(0)),
        inlk: return_bool(arena, false),
        inrk: return_bool(arena, true),
    });
    arena.alloc(MComputation::Bind { comp, cont: case })
}

/// Constant-folds a `Bool`-valued expression when it is fully literal.
fn const_bool(expr: &Expr) -> Option<bool> {
    match expr {
        Expr::Bool(b) => Some(*b),
        Expr::Stmt(s) => match &**s {
            Stmt::Expr(e) => const_bool(e),
            _ => None,
        },
        Expr::BExpr(b) => match b {
            BExpr::Eq(a, b) => Some(const_eq(a, b)?),
            BExpr::NEq(a, b) => Some(!const_eq(a, b)?),
            BExpr::And(a, b) => Some(const_bool(a)? && const_bool(b)?),
            BExpr::Or(a, b) => Some(const_bool(a)? || const_bool(b)?),
            BExpr::Not(e) => Some(!const_bool(e)?),
        },
        _ => None,
    }
}

/// Constant-folds equality of two operands when both are fully literal,
/// covering both `Nat` and `Bool` operands.
fn const_eq(a: &Expr, b: &Expr) -> Option<bool> {
    if let (Some(x), Some(y)) = (const_nat(a), const_nat(b)) {
        return Some(x == y);
    }
    Some(const_bool(a)? == const_bool(b)?)
}

/// Constant-folds a `Nat`-valued expression when it is fully literal.
fn const_nat(expr: &Expr) -> Option<u64> {
    match expr {
        Expr::Zero => Some(0),
        Expr::Nat(n) => Some(*n as u64),
        Expr::Succ(e) => Some(const_nat(e)? + 1),
        Expr::Stmt(s) => match &**s {
            Stmt::Expr(e) => const_nat(e),
            _ => None,
        },
        _ => None,
    }
}

fn translate_bexpr<'a>(arena: &'a Bump, bexpr: BExpr, tenv: &mut TEnv) -> &'a MComputation<'a> {
    if let Some(b) = const_bool(&Expr::BExpr(bexpr.clone())) {
        return return_bool(arena, b);
    }
    match bexpr {
        BExpr::Eq(lhs, rhs) => nat_eq_comp(arena, *lhs, *rhs, tenv),
        BExpr::NEq(lhs, rhs) => negate_comp(arena, nat_eq_comp(arena, *lhs, *rhs, tenv)),
        BExpr::And(lhs, rhs) => translate_connective(arena, *lhs, *rhs, true, tenv),
        BExpr::Or(lhs, rhs) => translate_connective(arena, *lhs, *rhs, false, tenv),
        BExpr::Not(e) => {
            let comp = translate_expr(arena, *e, tenv);
            negate_comp(arena, comp)
        }
    }
}

/// Lowers `&&` (when `and`) or `||` by casing on the lowered left `Bool`.
/// For `&&`: true (`Inl`) evaluates the right operand, false (`Inr`) is false.
/// For `||`: true short-circuits to true, false evaluates the right operand.
/// The left operand binds at index 0, then the `Case` payload binds at index 0,
/// so the right operand is translated under two extra binders.
fn translate_connective<'a>(arena: &'a Bump, lhs: Expr, rhs: Expr, and: bool, tenv: &mut TEnv) -> &'a MComputation<'a> {
    let lhs_comp = translate_expr(arena, lhs, tenv);
    tenv.bind("_");
    tenv.bind("_");
    let rhs_comp = translate_expr(arena, rhs, tenv);
    tenv.unbind();
    tenv.unbind();
    let (inlk, inrk) = if and {
        (rhs_comp, return_bool(arena, false))
    } else {
        (return_bool(arena, true), rhs_comp)
    };
    let case = arena.alloc(MComputation::Case {
        sum: arena.alloc(MValue::Var(0)),
        inlk,
        inrk,
    });
    arena.alloc(MComputation::Bind { comp: lhs_comp, cont: case })
}

fn translate_list<'a>(arena: &'a Bump, elems: &[Expr], tenv: &mut TEnv) -> &'a MComputation<'a> {
    match elems {
        [] => {
            let nil = arena.alloc(MValue::Nil);
            arena.alloc(MComputation::Return(nil))
        }
        [head, tail @ ..] => {
            let chead = translate_expr(arena, head.clone(), tenv);
            tenv.bind("_");
            let ctail = translate_list(arena, tail, tenv);
            tenv.unbind();
            let var1 = arena.alloc(MValue::Var(1));
            let var0 = arena.alloc(MValue::Var(0));
            let cons = arena.alloc(MValue::Cons(var1, var0));
            let ret = arena.alloc(MComputation::Return(cons));
            let inner = arena.alloc(MComputation::Bind { comp: ctail, cont: ret });
            arena.alloc(MComputation::Bind { comp: chead, cont: inner })
        }
    }
}

fn translate_nat<'a>(arena: &'a Bump, n: usize) -> &'a MComputation<'a> {
    let val = arena.alloc(MValue::Nat(n as u64));
    arena.alloc(MComputation::Return(val))
}

fn translate_pair<'a>(arena: &'a Bump, fst: Expr, snd: Expr, tenv: &mut TEnv) -> &'a MComputation<'a> {
    let fst_comp = translate_expr(arena, fst, tenv);
    tenv.bind("_");
    let snd_comp = translate_expr(arena, snd, tenv);
    tenv.unbind();
    let var1 = arena.alloc(MValue::Var(1));
    let var0 = arena.alloc(MValue::Var(0));
    let pair = arena.alloc(MValue::Pair(var1, var0));
    let ret = arena.alloc(MComputation::Return(pair));
    let inner = arena.alloc(MComputation::Bind { comp: snd_comp, cont: ret });
    arena.alloc(MComputation::Bind { comp: fst_comp, cont: inner })
}
