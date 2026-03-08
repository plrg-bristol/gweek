use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::machine::value_type::ValueType;
use crate::parser::{arg::Arg, bexpr::BExpr, cases::CasesType, decl::Decl, expr::Expr, stm::Stm, r#type::Type};

use super::mterms::{MComputation, MValue};
use super::{Env, VClosure};

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

pub fn translate(ast: Vec<Decl>) -> (MComputation, Env) {
    let ast = reorder_decls(ast);

    let mut env = Env::empty();
    let mut tenv = TEnv::new();
    let mut main = None;

    for decl in ast {
        match decl {
            Decl::FuncType { .. } => (),
            Decl::Func { name, args, body } => {
                let result: Rc<MValue> = translate_func(&name, args, body, &mut tenv).into();
                tenv.bind(&name);
                env = env.extend_val(result, env.clone());
            }
            Decl::Stm(stm) => {
                main = Some(translate_stm(stm, &mut tenv));
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
            Decl::Stm(_) => {
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
        let refs = collect_refs_stm(body, &func_names);
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

fn collect_refs_stm(stm: &Stm, names: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::new();
    walk_stm(stm, names, &mut refs);
    refs
}

fn walk_stm(stm: &Stm, names: &HashSet<String>, refs: &mut HashSet<String>) {
    match stm {
        Stm::Expr(e) => walk_expr(e, names, refs),
        Stm::Let { val, body, .. } => {
            walk_stm(val, names, refs);
            walk_stm(body, names, refs);
        }
        Stm::Fail => (),
        Stm::Exists { body, .. } => walk_stm(body, names, refs),
        Stm::Equate { lhs, rhs, body } => {
            walk_expr(lhs, names, refs);
            walk_expr(rhs, names, refs);
            walk_stm(body, names, refs);
        }
        Stm::Choice(exprs) => {
            for e in exprs {
                walk_expr(e, names, refs);
            }
        }
        Stm::Case { expr, cases } => {
            walk_expr(expr, names, refs);
            if let Some(nc) = &cases.nat_case {
                if let Some(zk) = &nc.zk {
                    walk_stm(zk, names, refs);
                }
                if let Some(sk) = &nc.sk {
                    walk_stm(&sk.body, names, refs);
                }
            }
            if let Some(lc) = &cases.list_case {
                if let Some(nk) = &lc.nilk {
                    walk_stm(nk, names, refs);
                }
                if let Some(ck) = &lc.consk {
                    walk_stm(&ck.body, names, refs);
                }
            }
        }
        Stm::If { cond, then, r#else } => {
            walk_stm(cond, names, refs);
            walk_stm(then, names, refs);
            walk_stm(r#else, names, refs);
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
        Expr::Lambda(_, body) => walk_stm(body, names, refs),
        Expr::List(es) => {
            for e in es {
                walk_expr(e, names, refs);
            }
        }
        Expr::BExpr(b) => walk_bexpr(b, names, refs),
        Expr::Stm(s) => walk_stm(s, names, refs),
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

fn translate_func(name: &str, args: Vec<Arg>, body: Stm, tenv: &mut TEnv) -> MValue {
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
    let mbody = translate_stm(body, tenv);
    for _ in &vars {
        tenv.unbind();
    }
    tenv.unbind();

    if vars.is_empty() {
        MValue::Thunk(MComputation::Rec { body: mbody.into() }.into())
    } else {
        let mut c: MComputation = MComputation::Lambda { body: mbody.into() };
        while vars.len() > 1 {
            c = MComputation::Lambda {
                body: MComputation::Return(MValue::Thunk(c.into()).into()).into(),
            };
            vars.pop();
        }
        MValue::Thunk(MComputation::Rec { body: c.into() }.into())
    }
}

fn translate_vtype(ptype: Type) -> ValueType {
    match ptype {
        Type::Arrow(_, _) => panic!("don't translate thunks"),
        Type::Ident(s) if s == "Nat" => ValueType::Nat,
        Type::Ident(_) => todo!(),
        Type::List(t) => ValueType::List(Box::new(translate_vtype(*t))),
        Type::Product(t1, t2) => {
            ValueType::Product(Box::new(translate_vtype(*t1)), Box::new(translate_vtype(*t2)))
        }
        Type::Any => panic!("cannot translate unresolved type"),
    }
}

fn translate_stm(stm: Stm, tenv: &mut TEnv) -> MComputation {
    match stm {
        Stm::If { cond, .. } => MComputation::Bind {
            comp: translate_stm(*cond, tenv).into(),
            cont: todo!("need sums to complete this"),
        },
        Stm::Let { var, val, body } => {
            let comp = translate_stm(*val, tenv).into();
            tenv.bind(&var);
            let cont = translate_stm(*body, tenv).into();
            tenv.unbind();
            MComputation::Bind { comp, cont }
        }
        Stm::Exists { var, r#type, body } => {
            tenv.bind(&var);
            let body = translate_stm(*body, tenv).into();
            tenv.unbind();
            MComputation::Exists {
                ptype: translate_vtype(r#type),
                body,
            }
        }
        Stm::Equate { lhs, rhs, body } => {
            let lhs_comp = translate_expr(lhs, tenv).into();
            tenv.bind("_");
            let rhs_comp = translate_expr(rhs, tenv).into();
            tenv.bind("_");
            let body_comp = translate_stm(*body, tenv).into();
            tenv.unbind();
            tenv.unbind();
            MComputation::Bind {
                comp: lhs_comp,
                cont: MComputation::Bind {
                    comp: rhs_comp,
                    cont: MComputation::Equate {
                        lhs: MValue::Var(0).into(),
                        rhs: MValue::Var(1).into(),
                        body: body_comp,
                    }
                    .into(),
                }
                .into(),
            }
        }
        Stm::Fail => MComputation::Choice(vec![]),
        Stm::Choice(exprs) => MComputation::Choice(
            exprs
                .into_iter()
                .map(|e| translate_expr(e, tenv).into())
                .collect(),
        ),
        Stm::Case { expr, cases } => {
            tenv.bind("_");
            let cont = match cases.r#type.unwrap() {
                CasesType::Nat => {
                    let nat_case = cases.nat_case.unwrap();
                    let zk = translate_stm(*nat_case.zk.unwrap(), tenv).into();
                    let succ_case = nat_case.sk.unwrap();
                    tenv.bind(&succ_case.var);
                    let sk = translate_stm(*succ_case.body, tenv).into();
                    tenv.unbind();
                    MComputation::Ifz {
                        num: MValue::Var(0).into(),
                        zk,
                        sk,
                    }
                }
                CasesType::List => {
                    let list_case = cases.list_case.unwrap();
                    let nilk = translate_stm(*list_case.nilk.unwrap(), tenv).into();
                    let cons_case = list_case.consk.unwrap();
                    tenv.bind(&cons_case.x);
                    tenv.bind(&cons_case.xs);
                    let consk = translate_stm(*cons_case.body, tenv).into();
                    tenv.unbind();
                    tenv.unbind();
                    MComputation::Match {
                        list: MValue::Var(0).into(),
                        nilk,
                        consk,
                    }
                }
            }
            .into();
            tenv.unbind();
            MComputation::Bind {
                comp: translate_expr(expr, tenv).into(),
                cont,
            }
        }
        Stm::Expr(e) => translate_expr(e, tenv),
    }
}

fn translate_expr(expr: Expr, tenv: &mut TEnv) -> MComputation {
    match expr {
        Expr::Zero => MComputation::Return(MValue::Zero.into()),
        Expr::Succ(body) => MComputation::Bind {
            comp: translate_expr(*body, tenv).into(),
            cont: MComputation::Return(MValue::Succ(MValue::Var(0).into()).into()).into(),
        },
        Expr::Nil => MComputation::Return(MValue::Nil.into()),
        Expr::Cons(x, xs) => {
            let comp_head = translate_expr(*x, tenv).into();
            tenv.bind("_");
            let comp_tail = translate_expr(*xs, tenv).into();
            tenv.unbind();
            MComputation::Bind {
                comp: comp_head,
                cont: MComputation::Bind {
                    comp: comp_tail,
                    cont: MComputation::Return(
                        MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into()).into(),
                    )
                    .into(),
                }
                .into(),
            }
        }
        Expr::Lambda(arg, body) => match arg {
            Arg::Ident(var) => {
                tenv.bind(&var);
                let body = translate_stm(*body, tenv);
                tenv.unbind();
                MComputation::Return(
                    MValue::Thunk(MComputation::Lambda { body: body.into() }.into()).into(),
                )
            }
            Arg::Pair(..) => todo!(),
        },
        Expr::App(op, arg) => {
            let comp_op = translate_expr(*op, tenv).into();
            tenv.bind("_");
            let comp_arg = translate_expr(*arg, tenv).into();
            tenv.unbind();
            MComputation::Bind {
                comp: comp_op,
                cont: MComputation::Bind {
                    comp: comp_arg,
                    cont: MComputation::App {
                        op: MComputation::Force(MValue::Var(1).into()).into(),
                        arg: MValue::Var(0).into(),
                    }
                    .into(),
                }
                .into(),
            }
        }
        Expr::BExpr(bexpr) => translate_bexpr(bexpr, tenv),
        Expr::List(elems) => translate_list(&elems, tenv),
        Expr::Ident(s) => MComputation::Return(MValue::Var(tenv.find(&s)).into()),
        Expr::Nat(n) => translate_nat(n),
        Expr::Bool(_) => todo!("no bools yet"),
        Expr::Pair(lhs, rhs) => translate_pair(*lhs, *rhs, tenv),
        Expr::Stm(s) => translate_stm(*s, tenv),
    }
}

fn translate_bexpr(_bexpr: BExpr, _tenv: &TEnv) -> MComputation {
    todo!("boolean expressions not yet implemented")
}

fn translate_list(elems: &[Expr], tenv: &mut TEnv) -> MComputation {
    match elems {
        [] => MComputation::Return(MValue::Nil.into()),
        [head, tail @ ..] => {
            let chead = translate_expr(head.clone(), tenv);
            tenv.bind("_");
            let ctail = translate_list(tail, tenv);
            tenv.unbind();
            MComputation::Bind {
                comp: chead.into(),
                cont: MComputation::Bind {
                    comp: ctail.into(),
                    cont: MComputation::Return(
                        MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into()).into(),
                    )
                    .into(),
                }
                .into(),
            }
        }
    }
}

fn translate_nat(n: usize) -> MComputation {
    let mut val: Rc<MValue> = MValue::Zero.into();
    for _ in 0..n {
        val = MValue::Succ(val).into();
    }
    MComputation::Return(val)
}

fn translate_pair(fst: Expr, snd: Expr, tenv: &mut TEnv) -> MComputation {
    let fst_comp = translate_expr(fst, tenv).into();
    tenv.bind("_");
    let snd_comp = translate_expr(snd, tenv).into();
    tenv.unbind();
    MComputation::Bind {
        comp: fst_comp,
        cont: MComputation::Bind {
            comp: snd_comp,
            cont: MComputation::Return(
                MValue::Pair(MValue::Var(1).into(), MValue::Var(0).into()).into(),
            )
            .into(),
        }
        .into(),
    }
}
