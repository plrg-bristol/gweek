use std::collections::{HashMap, HashSet, VecDeque};

use bumpalo::Bump;

use crate::machine::value_type::ValueType;
use crate::parser::{arg::Arg, bexpr::BExpr, cases::CasesType, decl::Decl, expr::Expr, stmt::Stmt, r#type::Type};

use super::mterms::{MComputation, MValue};

struct TEnv {
    env: Vec<String>,
}

impl TEnv {
    fn new() -> TEnv {
        TEnv { env: vec![] }
    }

    fn find(&self, v: &str) -> usize {
        self.env
            .iter()
            .rev()
            .position(|x| x == v)
            .unwrap_or_else(|| panic!("Variable {} not found in environment", v))
    }

    fn bind(&mut self, v: &str) {
        self.env.push(v.to_owned())
    }

    fn unbind(&mut self) {
        self.env.pop();
    }
}

pub fn translate<'a>(arena: &'a Bump, ast: Vec<Decl>) -> (&'a MComputation<'a>, Vec<&'a MValue<'a>>) {
    let ast = reorder_decls(ast);

    let mut env = Vec::new();
    let mut tenv = TEnv::new();
    let mut main = None;

    for decl in ast {
        match decl {
            Decl::FuncType { .. } => (),
            Decl::Func { name, args, body } => {
                let result = translate_func(arena, &name, args, body, &mut tenv);
                tenv.bind(&name);
                env.push(result);
            }
            Decl::Stmt(stmt) => {
                main = Some(translate_stmt(arena, stmt, &mut tenv));
            }
        }
    }

    (main.expect("empty program"), env)
}

// --- Declaration reordering (topological sort) ---

fn reorder_decls(ast: Vec<Decl>) -> Vec<Decl> {
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

fn translate_func<'a>(arena: &'a Bump, name: &str, args: Vec<Arg>, body: Stmt, tenv: &mut TEnv) -> &'a MValue<'a> {
    tenv.bind(name);

    let mut vars: Vec<String> = args
        .iter()
        .map(|arg| match arg {
            Arg::Ident(var) => var.clone(),
            _ => todo!(),
        })
        .collect();

    for v in &vars {
        tenv.bind(v);
    }
    let mbody = translate_stmt(arena, body, tenv);
    for _ in &vars {
        tenv.unbind();
    }
    tenv.unbind();

    if vars.is_empty() {
        let rec = arena.alloc(MComputation::Rec { body: mbody });
        arena.alloc(MValue::Thunk(rec))
    } else {
        let mut c: &MComputation = arena.alloc(MComputation::Lambda { body: mbody });
        while vars.len() > 1 {
            let thunk = arena.alloc(MValue::Thunk(c));
            let ret = arena.alloc(MComputation::Return(thunk));
            c = arena.alloc(MComputation::Lambda { body: ret });
            vars.pop();
        }
        let rec = arena.alloc(MComputation::Rec { body: c });
        arena.alloc(MValue::Thunk(rec))
    }
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
            Arg::Pair(..) => todo!(),
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
            arena.alloc(MComputation::Return(var))
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

fn translate_bexpr<'a>(_arena: &'a Bump, _bexpr: BExpr, _tenv: &TEnv) -> &'a MComputation<'a> {
    todo!("boolean expressions not yet implemented")
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
