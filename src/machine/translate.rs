use std::{collections::HashMap, rc::Rc};
use crate::{machine::value_type::ValueType, parser::{arg::{self, Arg}, bexpr::BExpr, cases::CasesType, decl::Decl, expr::Expr, stm::Stm, r#type::Type}};
use super::{mterms::{MComputation, MValue}, Env, VClosure};

type Idx = usize;
struct TEnv { env : Vec<String> } 

impl TEnv {
    fn new() -> TEnv { TEnv { env: vec![] } }
    fn find(&self, v : &String) -> usize {
        self.env.iter().rev().position(|x| x == v).expect(&("Variable ".to_owned() + v + " not found in environment"))
    }
    fn bind(&mut self, v : &String) {
        self.env.push(v.clone())
    }
    fn unbind(&mut self) {
        self.env.pop();
    }
    fn to_string(&self) -> String {
        "[ ".to_owned() + &self.env.join(" ") + " ]"
    }
}

pub fn translate(ast: Vec<Decl>) -> (MComputation, Rc<Env>) {

    let ast = reorder_decls(ast);

    let mut env = Env::empty();
    let mut tenv = TEnv::new();
    let mut main = None;

    ast.into_iter()
        .for_each(|decl| match decl {
            Decl::FuncType { name: _, r#type: _ } => (),
            Decl::Func { name, args, body } => {
                let result : Rc<MValue> = translate_func(&name, args, body, &mut tenv).into();
                tenv.bind(&name);
                env = env.extend_val(result.clone(), env.clone())
            },
            Decl::Stm(stm) => {
                let stmt = translate_stm(stm, &mut tenv);
                main = Some(stmt)
            }
        });
    (main.expect("empty program"), env)
}

fn reorder_decls(ast: Vec<Decl>) -> Vec<Decl> {
    use std::collections::HashSet;

    // Collect all declared function names
    let func_names: HashSet<String> = ast.iter().filter_map(|d| match d {
        Decl::Func { name, .. } => Some(name.clone()),
        _ => None,
    }).collect();

    // Separate declarations into func groups (type sig + body) and statements
    let mut func_decls: Vec<(String, Vec<Decl>)> = Vec::new();
    let mut stms: Vec<Decl> = Vec::new();
    let mut pending_type: Option<Decl> = None;

    for decl in ast {
        match &decl {
            Decl::FuncType { .. } => {
                pending_type = Some(decl);
            }
            Decl::Func { name, body, .. } => {
                let mut group = Vec::new();
                if let Some(t) = pending_type.take() { group.push(t); }
                let deps = collect_refs_stm(body, &func_names);
                let nm = name.clone();
                group.push(decl);
                func_decls.push((nm, group));
            }
            Decl::Stm(_) => {
                if let Some(t) = pending_type.take() { stms.push(t); }
                stms.push(decl);
            }
        }
    }

    // Build name→index map
    let name_to_idx: HashMap<String, usize> = func_decls.iter().enumerate()
        .map(|(i, (name, _))| (name.clone(), i))
        .collect();

    // Build dependency graph and topologically sort
    let n = func_decls.len();
    let mut deps: Vec<HashSet<usize>> = Vec::with_capacity(n);
    for (name, group) in &func_decls {
        let body = group.iter().find_map(|d| match d {
            Decl::Func { body, .. } => Some(body),
            _ => None,
        }).unwrap();
        let refs = collect_refs_stm(body, &func_names);
        let dep_indices: HashSet<usize> = refs.iter()
            .filter(|r| *r != name) // exclude self-recursion
            .filter_map(|r| name_to_idx.get(r).copied())
            .collect();
        deps.push(dep_indices);
    }

    // Kahn's algorithm
    let mut in_degree: Vec<usize> = vec![0; n];
    for d in &deps {
        for &j in d {
            in_degree[j] += 0; // j is depended ON, not the one with the in-edge
        }
    }
    // Actually: deps[i] = set of indices that i depends on
    // Edge: i → j means "i depends on j", so j must come before i
    // In-degree: number of things that must come before i = deps[i].len()... no
    // Let's think of it as: edge j → i means j must come before i
    // In-degree of i = number of j such that i depends on j = deps[i].len()
    // No wait, in Kahn's we need the reverse: "successors" of j = all i that depend on j

    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut in_deg: Vec<usize> = vec![0; n];
    for i in 0..n {
        for &j in &deps[i] {
            successors[j].push(i);
            in_deg[i] += 1;
        }
    }

    let mut queue: std::collections::VecDeque<usize> = (0..n).filter(|&i| in_deg[i] == 0).collect();
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
        // Cycle — just use original order (self-recursion is fine, mutual recursion won't work)
        order = (0..n).collect();
    }

    // Rebuild declaration list in sorted order
    let mut result: Vec<Decl> = Vec::new();
    // Convert func_decls to indexable, consuming the groups
    let mut func_groups: Vec<Option<Vec<Decl>>> = func_decls.into_iter().map(|(_, g)| Some(g)).collect();
    for idx in order {
        if let Some(group) = func_groups[idx].take() {
            result.extend(group);
        }
    }
    result.extend(stms);
    result
}

fn collect_refs_stm(stm: &Stm, names: &std::collections::HashSet<String>) -> std::collections::HashSet<String> {
    let mut refs = std::collections::HashSet::new();
    walk_stm(stm, names, &mut refs);
    refs
}

fn walk_stm(stm: &Stm, names: &std::collections::HashSet<String>, refs: &mut std::collections::HashSet<String>) {
    match stm {
        Stm::Expr(e) => walk_expr(e, names, refs),
        Stm::Let { val, body, .. } => { walk_stm(val, names, refs); walk_stm(body, names, refs); }
        Stm::Exists { body, .. } => walk_stm(body, names, refs),
        Stm::Equate { lhs, rhs, body } => { walk_expr(lhs, names, refs); walk_expr(rhs, names, refs); walk_stm(body, names, refs); }
        Stm::Choice(exprs) => { for e in exprs { walk_expr(e, names, refs); } }
        Stm::Case { expr, cases } => {
            walk_expr(expr, names, refs);
            if let Some(nc) = &cases.nat_case {
                if let Some(zk) = &nc.zk { walk_stm(zk, names, refs); }
                if let Some(sk) = &nc.sk { walk_stm(&sk.body, names, refs); }
            }
            if let Some(lc) = &cases.list_case {
                if let Some(nk) = &lc.nilk { walk_stm(nk, names, refs); }
                if let Some(ck) = &lc.consk { walk_stm(&ck.body, names, refs); }
            }
        }
        Stm::If { cond, then, r#else } => { walk_stm(cond, names, refs); walk_stm(then, names, refs); walk_stm(r#else, names, refs); }
    }
}

fn walk_expr(expr: &Expr, names: &std::collections::HashSet<String>, refs: &mut std::collections::HashSet<String>) {
    match expr {
        Expr::Ident(s) => { if names.contains(s) { refs.insert(s.clone()); } }
        Expr::App(a, b) => { walk_expr(a, names, refs); walk_expr(b, names, refs); }
        Expr::Cons(a, b) => { walk_expr(a, names, refs); walk_expr(b, names, refs); }
        Expr::Pair(a, b) => { walk_expr(a, names, refs); walk_expr(b, names, refs); }
        Expr::Succ(e) => walk_expr(e, names, refs),
        Expr::Lambda(_, body) => walk_stm(body, names, refs),
        Expr::List(es) => { for e in es { walk_expr(e, names, refs); } }
        Expr::BExpr(b) => walk_bexpr(b, names, refs),
        Expr::Stm(s) => walk_stm(s, names, refs),
        _ => {}
    }
}

fn walk_bexpr(bexpr: &BExpr, names: &std::collections::HashSet<String>, refs: &mut std::collections::HashSet<String>) {
    match bexpr {
        BExpr::Eq(a, b) | BExpr::NEq(a, b) | BExpr::And(a, b) | BExpr::Or(a, b) => {
            walk_expr(a, names, refs); walk_expr(b, names, refs);
        }
        BExpr::Not(e) => walk_expr(e, names, refs),
    }
}

fn translate_func(name : &String, args: Vec<Arg>, body: Stm, env : &mut TEnv) -> MValue {
    
    env.bind(name);

    let mut vars : Vec<String> = args.iter().map(|arg| match arg {
        Arg::Ident(var) => var.clone(),
        _ => todo!()
    }).collect();
    
    let arg_no = vars.len();
    
    vars.iter().for_each(|s| env.bind(s));
    let mbody = translate_stm(body, env);
    vars.iter().for_each(|s| env.unbind());
    
    env.unbind();
    
    if arg_no > 0 {
        let mut c : MComputation = MComputation::Lambda { body : mbody.into()}.into();
        while vars.len() > 1 {
            c = MComputation::Lambda { body : MComputation::Return(MValue::Thunk(c.into()).into()).into() }.into();
            vars.pop();
        }
        MValue::Thunk(MComputation::Rec { body: c.into() }.into())
    }
    else {
        MValue::Thunk(MComputation::Rec { body: mbody.into() }.into())
    }
}

fn translate_vtype(ptype : Type) -> ValueType { 
    match ptype {
        Type::Arrow(_, _) => panic!("don't translate thunks"),
        Type::Ident(s) => 
            if s == "Nat" { ValueType::Nat } else { todo!() },
        Type::List(t) => ValueType::List(Box::new(translate_vtype(*t))),
        Type::Product(t1, t2) => ValueType::Product(Box::new(translate_vtype(*t1)), Box::new(translate_vtype(*t2)))
    }
}

fn translate_stm(stm: Stm, env : &mut TEnv) -> MComputation {
    match stm {
        Stm::If { cond, then, r#else } => MComputation::Bind {
            comp : translate_stm(*cond, env).into(),
            cont : todo!() // need sums to complete this
        },
        Stm::Let { var, val, body } => {
            let comp = translate_stm(*val, env).into();
            env.bind(&var);
            let cont = translate_stm(*body, env).into();
            env.unbind();
            MComputation::Bind { comp, cont }
        },
        Stm::Exists { var, r#type, body } => {
            env.bind(&var);
            let body: Rc<MComputation> = translate_stm(*body, env).into();
            env.unbind();
            let ptype = translate_vtype(r#type);
            MComputation::Exists { ptype, body: body }
        },
        Stm::Equate { lhs, rhs, body } => {
            let lhs_comp = translate_expr(lhs, env).into();
            env.bind(&"_foo".to_string());
            let rhs_comp = translate_expr(rhs, env).into();
            env.bind(&"_foo2".to_string());
            let body_comp = translate_stm(*body, env).into();
            env.unbind();
            env.unbind();
            MComputation::Bind {
                comp: lhs_comp,
                cont : MComputation::Bind {
                    comp: rhs_comp,
                    cont: MComputation::Equate {
                        lhs : MValue::Var(0).into(),
                        rhs : MValue::Var(1).into(),
                        body : body_comp
                    }.into()
                }.into()
            }.into()
        },
        Stm::Choice(exprs) => MComputation::Choice(
            exprs.into_iter()
                .map(|e| translate_expr(e, env).into()).collect()
        ),
        Stm::Case { expr, cases } => {
            env.bind(&"_foo".to_string());
            let cont = match cases.r#type.unwrap() {
                CasesType::Nat => {
                    let nat_case = cases.nat_case.unwrap();
                    let zk = translate_stm(*nat_case.zk.unwrap(), env).into();
                    let succ_case = nat_case.sk.unwrap();
                    env.bind(&succ_case.var);
                    let sk = translate_stm(*succ_case.body, env).into();
                    env.unbind();
                    MComputation::Ifz { num: MValue::Var(0).into(), zk, sk }
                },
                CasesType::List => {
                    let list_case = cases.list_case.unwrap();
                    let nilk = translate_stm(*list_case.nilk.unwrap(), env).into();
                    let cons_case = list_case.consk.unwrap();
                    env.bind(&cons_case.x);
                    env.bind(&cons_case.xs);
                    let consk = translate_stm(*cons_case.body, env).into();
                    env.unbind();
                    env.unbind();
                    MComputation::Match { list: MValue::Var(0).into(), nilk, consk }
                }
            }.into();
            env.unbind();

            MComputation::Bind {
                comp: translate_expr(expr, env).into(),
                cont
            }
        },
        Stm::Expr(e) => translate_expr(e, env)
    }
}

fn translate_expr(expr: Expr, env : &mut TEnv) -> MComputation {
    match expr {
        Expr::Zero => MComputation::Return(MValue::Zero.into()),
        Expr::Succ(body) => {
            MComputation::Bind { 
                comp: translate_expr(*body, env).into(),
                cont: MComputation::Return(MValue::Succ(MValue::Var(0).into()).into()).into()
            }
        },
        Expr::Nil => MComputation::Return(MValue::Nil.into()),
        Expr::Cons(x, xs) => {
            let comp_head = translate_expr(*x, env).into();
            env.bind(&"_foo".to_string());
            let comp_tail = translate_expr(*xs, env).into();
            env.unbind();
            MComputation::Bind { 
                comp: comp_head,
                cont: MComputation::Bind { 
                    comp: comp_tail,
                    cont: MComputation::Return(MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into()).into()).into(),
                }.into()
            }
        },
        Expr::Lambda(arg, body) => {
            match arg {
                arg::Arg::Ident(var) => {
                    env.bind(&var);
                    let body = translate_stm(*body, env);
                    env.unbind();

                    MComputation::Return(MValue::Thunk(MComputation::Lambda { body: body.into() }.into()).into())
                },
                arg::Arg::Pair(arg, arg1) => todo!(),
            }
        },
        Expr::App(op, arg) => {
            let comp_op = translate_expr(*op, env).into();
            
            env.bind(&"_foo".to_string());
            let comp_arg = translate_expr(*arg, env).into();
            env.unbind();
            
            MComputation::Bind {
                comp : comp_op,
                cont : MComputation::Bind {
                    comp : comp_arg,
                    cont : MComputation::App { 
                        op: MComputation::Force(MValue::Var(1).into()).into(),
                        arg: MValue::Var(0).into()
                    }.into()
                }.into()
            }
        },
        Expr::BExpr(bexpr) => translate_bexpr(bexpr, env),
        Expr::List(mut elems) => translate_list(elems, env),
        Expr::Ident(s) => MComputation::Return(MValue::Var(env.find(&s)).into()),
        Expr::Nat(n) => translate_nat(n),
        Expr::Bool(b) => todo!("no bools yet"),
        Expr::Pair(lhs, rhs) => translate_pair(*lhs, *rhs, env),
        Expr::Stm(s) => translate_stm(*s, env)
    }
}

fn translate_bexpr(bexpr: BExpr, env : &TEnv) -> MComputation {
    match bexpr {
        BExpr::Eq(lhs, rhs) => todo!(),
        BExpr::NEq(lhs, rhs) => todo!(),
        BExpr::And(lhs, rhs) => todo!(),
        BExpr::Or(lhs, rhs) => todo!(),
        BExpr::Not(e) => todo!()
    }
}

fn translate_list(elems: Vec<Expr>, env : &mut TEnv) -> MComputation {
    match elems.as_slice() {
        [] => MComputation::Return(MValue::Nil.into()),
        [head , tail@ ..] => {
            let chead = translate_expr(head.clone(), env);
            env.bind(&"_foo".to_string());
            let ctail = translate_list(tail.to_vec(), env);
            env.unbind();
            MComputation::Bind {
                comp: chead.into(), 
                cont: MComputation::Bind { 
                    comp: ctail.into(),
                    cont: MComputation::Return(MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into()).into()).into() }.into()
            }
        }
    }
}

fn translate_nat(n: usize) -> MComputation {
    let mut nat_val = MValue::Zero.into();
    for i in (0..n) {
        nat_val = MValue::Succ(nat_val).into();
    }
    MComputation::Return(nat_val.into())
}

fn translate_pair(fst: Expr, snd: Expr, env : &mut TEnv) -> MComputation {
    let fst_comp = translate_expr(fst, env).into();
    env.bind(&"_foo".to_string());
    let snd_comp = translate_expr(snd, env).into();
    env.unbind();
    MComputation::Bind { 
        comp: fst_comp,
        cont: MComputation::Bind {
            comp : snd_comp,
            cont : MComputation::Return(MValue::Pair(MValue::Var(1).into(), MValue::Var(0).into()).into()).into()
        }.into()
    }.into()
}