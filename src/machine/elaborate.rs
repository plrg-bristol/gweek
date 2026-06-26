//! # Elaboration: surface syntax to CBPV
//!
//! Elaboration translates the type-checked surface AST into the machine's CBPV term language
//! ([`mterms`](super::mterms)), replacing names by de Bruijn indices — and keeping those indices
//! aligned, across every intermediate `Bind` it introduces, is the elaborator's whole correctness
//! burden. [`elaborate`] returns the main computation together with the top-level function values.
//! Functions are grouped into strongly-connected components by Tarjan's algorithm and ordered by
//! dependency; a genuinely mutually-recursive group collapses to a single selector-dispatched
//! fixpoint.

use std::collections::{HashMap, HashSet};

use crate::machine::value_type::ValueType;
use crate::parser::ast::{Arg, BExpr, CasesType, Decl, Expr, Type};

use super::heap::{CompId, Heap};
use super::mterms::{MComputation, MValue};
use super::NodeId;

struct TEnv {
    env: Vec<String>,
    /// Names of nullary functions (thunks that need forcing at use sites).
    nullary: HashSet<String>,
    /// Members of mutually-recursive groups: name -> (bundle slot name,
    /// selector index). Such a name is not an environment slot of its own;
    /// it is obtained by applying the group's selector function to its index.
    members: HashMap<String, (String, usize)>,
}

impl TEnv {
    fn new() -> TEnv {
        TEnv {
            env: vec![],
            nullary: HashSet::new(),
            members: HashMap::new(),
        }
    }

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

pub fn elaborate(heap: &mut Heap, ast: Vec<Decl>) -> (CompId, Vec<NodeId>) {
    let sigs: HashMap<String, Type> = ast
        .iter()
        .filter_map(|d| match d {
            Decl::FuncType { name, r#type } => Some((name.clone(), r#type.clone())),
            _ => None,
        })
        .collect();

    let (groups, stmts) = order_functions(ast);

    let mut env = Vec::new();
    let mut tenv = TEnv::new();
    let mut main = None;

    for group in groups {
        if group.len() == 1 {
            let Func { name, args, body } = group.into_iter().next().unwrap();
            let nullary = args.is_empty();
            let arg_types = arg_types(sigs.get(&name), args.len());
            let result = elaborate_func(heap, &name, args, &arg_types, body, &mut tenv);
            if nullary {
                tenv.bind_nullary(&name);
            } else {
                tenv.bind(&name);
            }
            env.push(result);
        } else {
            let result = elaborate_group(heap, group, &sigs, &mut tenv);
            env.push(result);
        }
    }

    for decl in stmts {
        if let Decl::Expr(expr) = decl {
            main = Some(elaborate_expr(heap, expr, &mut tenv));
        }
    }

    (main.expect("empty program"), env)
}

/// A top-level function definition, paired with its (already collected) name.
struct Func {
    name: String,
    args: Vec<Arg>,
    body: Expr,
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

// --- Dependency analysis and SCC ordering ---

/// Splits the program into mutually-recursive function groups (the strongly
/// connected components of the call graph) in dependency-first topological
/// order, followed by the trailing statements (with their type signatures).
/// Each group is the set of functions that must be defined together; a group
/// of size > 1 is genuinely mutually recursive.
fn order_functions(ast: Vec<Decl>) -> (Vec<Vec<Func>>, Vec<Decl>) {
    let mut funcs: Vec<Func> = Vec::new();
    let mut stmts: Vec<Decl> = Vec::new();
    let mut pending_type: Option<Decl> = None;

    for decl in ast {
        match decl {
            Decl::FuncType { .. } => pending_type = Some(decl),
            Decl::Func { name, args, body } => {
                pending_type = None;
                funcs.push(Func { name, args, body });
            }
            Decl::Expr(_) => {
                if let Some(t) = pending_type.take() {
                    stmts.push(t);
                }
                stmts.push(decl);
            }
        }
    }

    let func_names: HashSet<String> = funcs.iter().map(|f| f.name.clone()).collect();
    let name_to_idx: HashMap<String, usize> = funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.clone(), i))
        .collect();

    // Edge i -> j when function i references function j (i depends on j).
    let n = funcs.len();
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, f) in funcs.iter().enumerate() {
        for r in collect_refs_expr(&f.body, &func_names) {
            if let Some(&j) = name_to_idx.get(&r) {
                if j != i {
                    deps[i].push(j);
                }
            }
        }
    }

    // Tarjan's SCC algorithm. Components are produced in reverse topological
    // order of the condensation (a component is finished after every component
    // it depends on), so the result is already dependency-first.
    let sccs = tarjan_scc(&deps);

    let mut slots: Vec<Option<Func>> = funcs.into_iter().map(Some).collect();
    let groups: Vec<Vec<Func>> = sccs
        .into_iter()
        .map(|comp| comp.into_iter().map(|i| slots[i].take().unwrap()).collect())
        .collect();

    (groups, stmts)
}

/// Tarjan's strongly-connected-components algorithm. Returns the SCCs in
/// reverse topological order of the condensation; within each SCC, nodes are
/// in source order.
fn tarjan_scc(deps: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = deps.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    // Iterative DFS to avoid stack overflow on large programs.
    // Frame: (node, position in deps[node] to resume from).
    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, pi)) = work.last() {
            if pi == 0 {
                index[v] = next_index;
                low[v] = next_index;
                next_index += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if pi < deps[v].len() {
                let w = deps[v][pi];
                work.last_mut().unwrap().1 += 1;
                if index[w] == usize::MAX {
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                if low[v] == index[v] {
                    let mut comp = Vec::new();
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    comp.reverse();
                    sccs.push(comp);
                }
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    low[parent] = low[parent].min(low[v]);
                }
            }
        }
    }

    sccs
}

// --- AST walkers for dependency collection ---

fn collect_refs_expr(expr: &Expr, names: &HashSet<String>) -> HashSet<String> {
    let mut refs = HashSet::new();
    walk_expr(expr, names, &mut refs);
    refs
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
        Expr::Lambda(_, body) => walk_expr(body, names, refs),
        Expr::List(es) => {
            for e in es {
                walk_expr(e, names, refs);
            }
        }
        Expr::BExpr(b) => walk_bexpr(b, names, refs),
        Expr::Let { val, body, .. } => {
            walk_expr(val, names, refs);
            walk_expr(body, names, refs);
        }
        Expr::LetNeed { val, body, .. } => {
            walk_expr(val, names, refs);
            walk_expr(body, names, refs);
        }
        Expr::Exists { body, .. } => walk_expr(body, names, refs),
        Expr::Equate { lhs, rhs, body } => {
            walk_expr(lhs, names, refs);
            walk_expr(rhs, names, refs);
            walk_expr(body, names, refs);
        }
        Expr::Choice(exprs) => {
            for e in exprs {
                walk_expr(e, names, refs);
            }
        }
        Expr::Case { expr, cases } => {
            walk_expr(expr, names, refs);
            if let Some(nc) = &cases.nat_case {
                if let Some(zk) = &nc.zk {
                    walk_expr(zk, names, refs);
                }
                if let Some(sk) = &nc.sk {
                    walk_expr(&sk.body, names, refs);
                }
            }
            if let Some(lc) = &cases.list_case {
                if let Some(nk) = &lc.nilk {
                    walk_expr(nk, names, refs);
                }
                if let Some(ck) = &lc.consk {
                    walk_expr(&ck.body, names, refs);
                }
            }
        }
        Expr::If { cond, then, r#else } => {
            walk_expr(cond, names, refs);
            walk_expr(then, names, refs);
            walk_expr(r#else, names, refs);
        }
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

// --- Elaboration ---

fn elaborate_func(
    heap: &mut Heap,
    name: &str,
    args: Vec<Arg>,
    arg_types: &[Option<Type>],
    body: Expr,
    tenv: &mut TEnv,
) -> NodeId {
    tenv.bind(name);
    let comp = if args.is_empty() {
        elaborate_expr(heap, body, tenv)
    } else {
        build_args(heap, &args, arg_types, &body, tenv)
    };
    tenv.unbind();
    let rec = heap.alloc_comp(MComputation::Rec { body: comp });
    heap.alloc_imm_val(MValue::Thunk(rec))
}

/// Elaborates a mutually-recursive group of functions to a single fixpoint.
///
/// The machine's `Rec` binds one self-reference, so a per-function `Rec`
/// cannot tie a mutual knot. Instead the whole group becomes one bundle:
///
///   bundle = thunk (rec self. λsel. ifz sel { thunk f0 } { thunk f1 } ...)
///
/// Forcing the bundle and applying it to selector `i` returns the thunk of
/// member `i`. Every reference to a group member -- inside a sibling, inside
/// the member itself, or from an outside caller -- goes through this selector
/// (see the `Expr::Ident` elaboration), so the recursion is genuinely mutual:
/// each body reaches its siblings through the shared `self`.
///
/// Inside the selector lambda the environment is `[sel, self, ..outer..]`; the
/// `ifz` chain binds one predecessor per step, so in branch `i` the bundle
/// (`self`) sits at de Bruijn index `i + 1`. Each member body is elaborated
/// with `tenv` set up to match exactly that layout.
fn elaborate_group(
    heap: &mut Heap,
    group: Vec<Func>,
    sigs: &HashMap<String, Type>,
    tenv: &mut TEnv,
) -> NodeId {
    let bundle = format!("$group${}", group[0].name);

    for (i, f) in group.iter().enumerate() {
        tenv.members.insert(f.name.clone(), (bundle.clone(), i));
    }

    let mut thunks: Vec<NodeId> = Vec::with_capacity(group.len());
    for (i, f) in group.iter().enumerate() {
        // Model the captured environment of branch `i`: the bundle (`self`)
        // sits below `sel` and the `i` predecessors bound by the `ifz` chain.
        tenv.bind(&bundle);
        for _ in 0..=i {
            tenv.bind("_");
        }
        let arg_types = arg_types(sigs.get(&f.name), f.args.len());
        let comp = if f.args.is_empty() {
            elaborate_expr(heap, f.body.clone(), tenv)
        } else {
            build_args(heap, &f.args, &arg_types, &f.body, tenv)
        };
        for _ in 0..=i {
            tenv.unbind();
        }
        tenv.unbind();
        thunks.push(heap.alloc_imm_val(MValue::Thunk(comp)));
    }

    // Dispatch: ifz sel { return thunk0 } { _. ifz pred { return thunk1 } ... }.
    // The scrutinee is always the most recently bound variable (sel, then each
    // predecessor), i.e. de Bruijn index 0.
    let mut dispatch = heap.alloc_comp(MComputation::Return(thunks[group.len() - 1]));
    for thunk in thunks[..group.len() - 1].iter().rev() {
        let zk = heap.alloc_comp(MComputation::Return(*thunk));
        let num = heap.alloc_imm_val(MValue::Var(0));
        dispatch = heap.alloc_comp(MComputation::Ifz {
            num,
            zk,
            sk: dispatch,
        });
    }

    let lam = heap.alloc_comp(MComputation::Lambda { body: dispatch });
    let rec = heap.alloc_comp(MComputation::Rec { body: lam });

    tenv.bind(&bundle);

    heap.alloc_imm_val(MValue::Thunk(rec))
}

/// Builds the curried lambda chain for the remaining `args`, binding each
/// argument pattern and emitting the function `body` once all are consumed.
/// Returns the body of the lambda for the first remaining argument.
fn build_args(
    heap: &mut Heap,
    args: &[Arg],
    arg_types: &[Option<Type>],
    body: &Expr,
    tenv: &mut TEnv,
) -> CompId {
    match args {
        [] => elaborate_expr(heap, body.clone(), tenv),
        [arg, rest @ ..] => {
            let rest_types = &arg_types[1..];
            let lam_body = match arg {
                Arg::Ident(var) => {
                    tenv.bind(var);
                    let inner = curry(heap, rest, rest_types, body, tenv);
                    tenv.unbind();
                    inner
                }
                Arg::Pair(..) => {
                    let ty = arg_types[0]
                        .as_ref()
                        .expect("pair argument needs a declared product type");
                    tenv.bind("_");
                    let body_comp = bind_pattern(heap, arg, ty, 0, tenv, &mut |heap, tenv| {
                        curry(heap, rest, rest_types, body, tenv)
                    });
                    tenv.unbind();
                    body_comp
                }
            };
            heap.alloc_comp(MComputation::Lambda { body: lam_body })
        }
    }
}

/// Wraps the lambda chain for `rest` so that, when more arguments remain, the
/// inner chain is returned as a thunk (CBPV currying).
fn curry(
    heap: &mut Heap,
    rest: &[Arg],
    rest_types: &[Option<Type>],
    body: &Expr,
    tenv: &mut TEnv,
) -> CompId {
    if rest.is_empty() {
        build_args(heap, rest, rest_types, body, tenv)
    } else {
        let inner = build_args(heap, rest, rest_types, body, tenv);
        let thunk = heap.alloc_imm_val(MValue::Thunk(inner));
        heap.alloc_comp(MComputation::Return(thunk))
    }
}

/// Collects the leaf variable names of a pattern together with their value
/// types, in left-to-right order, validating the pattern against the type.
fn collect_leaves(pattern: &Arg, ty: &Type, out: &mut Vec<(String, ValueType)>) {
    match pattern {
        Arg::Ident(name) => out.push((name.clone(), elaborate_vtype(ty.clone()))),
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
fn rebuild_pattern(heap: &mut Heap, pattern: &Arg, m: usize, next: &mut usize) -> NodeId {
    match pattern {
        Arg::Ident(_) => {
            let idx = (m - 1) - *next;
            *next += 1;
            heap.alloc_imm_val(MValue::Var(idx))
        }
        Arg::Pair(a, b) => {
            let av = rebuild_pattern(heap, a, m, next);
            let bv = rebuild_pattern(heap, b, m, next);
            heap.alloc_imm_val(MValue::Pair(av, bv))
        }
    }
}

/// Destructures the pair value at de Bruijn index `pair_idx` against `pattern`.
/// Introduces one fresh logic variable per leaf, unifies the reconstructed
/// pattern with the pair, then runs the continuation `k` with the leaves bound.
fn bind_pattern(
    heap: &mut Heap,
    pattern: &Arg,
    ty: &Type,
    pair_idx: usize,
    tenv: &mut TEnv,
    k: &mut dyn FnMut(&mut Heap, &mut TEnv) -> CompId,
) -> CompId {
    let mut leaves = Vec::new();
    collect_leaves(pattern, ty, &mut leaves);
    let m = leaves.len();

    for (name, _) in &leaves {
        tenv.bind(name);
    }
    let body = k(heap, tenv);
    for _ in &leaves {
        tenv.unbind();
    }

    let mut next = 0;
    let lhs = rebuild_pattern(heap, pattern, m, &mut next);
    let rhs = heap.alloc_imm_val(MValue::Var(pair_idx + m));
    let mut comp = heap.alloc_comp(MComputation::Equate { lhs, rhs, body });
    for (_, vty) in leaves.into_iter().rev() {
        comp = heap.alloc_comp(MComputation::Exists {
            ptype: vty,
            body: comp,
        });
    }
    comp
}

fn elaborate_vtype(ptype: Type) -> ValueType {
    match ptype {
        Type::Arrow(_, _) => panic!("don't elaborate thunks"),
        Type::Ident(s) if s == "Nat" => ValueType::Nat,
        Type::Ident(s) if s == "Bool" => {
            ValueType::Sum(Box::new(ValueType::Unit), Box::new(ValueType::Unit))
        }
        Type::Ident(s) => panic!("cannot elaborate type {}", s),
        Type::List(t) => ValueType::List(Box::new(elaborate_vtype(*t))),
        Type::Product(t1, t2) => ValueType::Product(
            Box::new(elaborate_vtype(*t1)),
            Box::new(elaborate_vtype(*t2)),
        ),
        Type::Any => panic!("cannot elaborate unresolved type"),
    }
}

fn elaborate_expr(heap: &mut Heap, expr: Expr, tenv: &mut TEnv) -> CompId {
    match expr {
        Expr::If { cond, then, r#else } => {
            let comp = elaborate_expr(heap, *cond, tenv);
            tenv.bind("_");
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            // Inl = true → then branch (bind unit, discard it)
            tenv.bind("_");
            let then_comp = elaborate_expr(heap, *then, tenv);
            tenv.unbind();
            // Inr = false → else branch (bind unit, discard it)
            tenv.bind("_");
            let else_comp = elaborate_expr(heap, *r#else, tenv);
            tenv.unbind();
            let case = heap.alloc_comp(MComputation::Case {
                sum: var0,
                inlk: then_comp,
                inrk: else_comp,
            });
            tenv.unbind();
            heap.alloc_comp(MComputation::Bind { comp, cont: case })
        }
        Expr::Let { var, val, body } => {
            let comp = elaborate_expr(heap, *val, tenv);
            tenv.bind(&var);
            let cont = elaborate_expr(heap, *body, tenv);
            tenv.unbind();
            heap.alloc_comp(MComputation::Bind { comp, cont })
        }
        Expr::LetNeed { var, val, body } => {
            let comp = elaborate_expr(heap, *val, tenv);
            tenv.bind(&var);
            let cont = elaborate_expr(heap, *body, tenv);
            tenv.unbind();
            heap.alloc_comp(MComputation::Need { comp, cont })
        }
        Expr::Exists { var, r#type, body } => {
            tenv.bind(&var);
            let body = elaborate_expr(heap, *body, tenv);
            tenv.unbind();
            heap.alloc_comp(MComputation::Exists {
                ptype: elaborate_vtype(r#type),
                body,
            })
        }
        Expr::Equate { lhs, rhs, body } => {
            let lhs_comp = elaborate_expr(heap, *lhs, tenv);
            tenv.bind("_");
            let rhs_comp = elaborate_expr(heap, *rhs, tenv);
            tenv.bind("_");
            let body_comp = elaborate_expr(heap, *body, tenv);
            tenv.unbind();
            tenv.unbind();
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let var1 = heap.alloc_imm_val(MValue::Var(1));
            let equate = heap.alloc_comp(MComputation::Equate {
                lhs: var0,
                rhs: var1,
                body: body_comp,
            });
            let inner_bind = heap.alloc_comp(MComputation::Bind {
                comp: rhs_comp,
                cont: equate,
            });
            heap.alloc_comp(MComputation::Bind {
                comp: lhs_comp,
                cont: inner_bind,
            })
        }
        Expr::Fail => heap.alloc_comp(MComputation::Choice(Vec::new().into_boxed_slice())),
        Expr::Choice(exprs) => {
            let choices: Vec<CompId> = exprs
                .into_iter()
                .map(|e| elaborate_expr(heap, e, tenv))
                .collect();
            heap.alloc_comp(MComputation::Choice(choices.into_boxed_slice()))
        }
        Expr::Case { expr, cases } => {
            tenv.bind("_");
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let cont = match cases.r#type.unwrap() {
                CasesType::Nat => {
                    let nat_case = cases.nat_case.unwrap();
                    let zk = elaborate_expr(heap, *nat_case.zk.unwrap(), tenv);
                    let succ_case = nat_case.sk.unwrap();
                    tenv.bind(&succ_case.var);
                    let sk = elaborate_expr(heap, *succ_case.body, tenv);
                    tenv.unbind();
                    heap.alloc_comp(MComputation::Ifz { num: var0, zk, sk })
                }
                CasesType::List => {
                    let list_case = cases.list_case.unwrap();
                    let nilk = elaborate_expr(heap, *list_case.nilk.unwrap(), tenv);
                    let cons_case = list_case.consk.unwrap();
                    tenv.bind(&cons_case.x);
                    tenv.bind(&cons_case.xs);
                    let consk = elaborate_expr(heap, *cons_case.body, tenv);
                    tenv.unbind();
                    tenv.unbind();
                    heap.alloc_comp(MComputation::Match {
                        list: var0,
                        nilk,
                        consk,
                    })
                }
            };
            tenv.unbind();
            let comp = elaborate_expr(heap, *expr, tenv);
            heap.alloc_comp(MComputation::Bind { comp, cont })
        }
        Expr::Zero => {
            let zero = heap.alloc_imm_val(MValue::Nat(0));
            heap.alloc_comp(MComputation::Return(zero))
        }
        Expr::Succ(body) => {
            let comp = elaborate_expr(heap, *body, tenv);
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let succ = heap.alloc_imm_val(MValue::Succ(var0));
            let ret = heap.alloc_comp(MComputation::Return(succ));
            heap.alloc_comp(MComputation::Bind { comp, cont: ret })
        }
        Expr::Nil => {
            let nil = heap.alloc_imm_val(MValue::Nil);
            heap.alloc_comp(MComputation::Return(nil))
        }
        Expr::Cons(x, xs) => {
            let comp_head = elaborate_expr(heap, *x, tenv);
            tenv.bind("_");
            let comp_tail = elaborate_expr(heap, *xs, tenv);
            tenv.unbind();
            let var1 = heap.alloc_imm_val(MValue::Var(1));
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let cons = heap.alloc_imm_val(MValue::Cons(var1, var0));
            let ret = heap.alloc_comp(MComputation::Return(cons));
            let inner = heap.alloc_comp(MComputation::Bind {
                comp: comp_tail,
                cont: ret,
            });
            heap.alloc_comp(MComputation::Bind {
                comp: comp_head,
                cont: inner,
            })
        }
        Expr::Lambda(arg, body) => match arg {
            Arg::Ident(var) => {
                tenv.bind(&var);
                let body = elaborate_expr(heap, *body, tenv);
                tenv.unbind();
                let lam = heap.alloc_comp(MComputation::Lambda { body });
                let thunk = heap.alloc_imm_val(MValue::Thunk(lam));
                heap.alloc_comp(MComputation::Return(thunk))
            }
            // Destructuring a pair needs the component types to annotate the
            // fresh logic variables (the machine has no product eliminator, so
            // projection goes through Exists/Equate). A lambda carries no type
            // annotation, and the type checker rejects every lambda use (lambdas
            // synthesize no type), so this path is unreachable for well-typed
            // programs. We refuse to fabricate types here.
            Arg::Pair(..) => panic!(
                "cannot elaborate a pair-pattern lambda argument: no type \
                 annotation is available to type the destructured components"
            ),
        },
        Expr::App(op, arg) => {
            let comp_op = elaborate_expr(heap, *op, tenv);
            tenv.bind("_");
            let comp_arg = elaborate_expr(heap, *arg, tenv);
            tenv.unbind();
            let var1 = heap.alloc_imm_val(MValue::Var(1));
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let force = heap.alloc_comp(MComputation::Force(var1));
            let app = heap.alloc_comp(MComputation::App {
                op: force,
                arg: var0,
            });
            let inner = heap.alloc_comp(MComputation::Bind {
                comp: comp_arg,
                cont: app,
            });
            heap.alloc_comp(MComputation::Bind {
                comp: comp_op,
                cont: inner,
            })
        }
        Expr::BExpr(bexpr) => elaborate_bexpr(heap, bexpr, tenv),
        Expr::List(elems) => elaborate_list(heap, &elems, tenv),
        Expr::Ident(s) => {
            // A member of a mutually-recursive group is obtained by applying
            // the group's selector function to the member's index, which
            // returns the member's thunk.
            let comp = if let Some((bundle, sel)) = tenv.members.get(&s).cloned() {
                let bundle_var = heap.alloc_imm_val(MValue::Var(tenv.find(&bundle)));
                let force = heap.alloc_comp(MComputation::Force(bundle_var));
                let selector = heap.alloc_imm_val(MValue::Nat(sel as u64));
                heap.alloc_comp(MComputation::App {
                    op: force,
                    arg: selector,
                })
            } else {
                let var = heap.alloc_imm_val(MValue::Var(tenv.find(&s)));
                heap.alloc_comp(MComputation::Return(var))
            };
            if tenv.is_nullary(&s) {
                let var0 = heap.alloc_imm_val(MValue::Var(0));
                let force = heap.alloc_comp(MComputation::Force(var0));
                heap.alloc_comp(MComputation::Bind { comp, cont: force })
            } else {
                comp
            }
        }
        Expr::Nat(n) => elaborate_nat(heap, n),
        Expr::Bool(b) => {
            let unit = heap.alloc_imm_val(MValue::Unit);
            let val = if b {
                heap.alloc_imm_val(MValue::Inl(unit))
            } else {
                heap.alloc_imm_val(MValue::Inr(unit))
            };
            heap.alloc_comp(MComputation::Return(val))
        }
        Expr::Pair(lhs, rhs) => elaborate_pair(heap, *lhs, *rhs, tenv),
    }
}

/// Returns a computation that produces the `Bool` value `b`
/// (`Sum(Unit, Unit)`, `Inl` = true, `Inr` = false).
fn return_bool(heap: &mut Heap, b: bool) -> CompId {
    let unit = heap.alloc_imm_val(MValue::Unit);
    let val = if b {
        heap.alloc_imm_val(MValue::Inl(unit))
    } else {
        heap.alloc_imm_val(MValue::Inr(unit))
    };
    heap.alloc_comp(MComputation::Return(val))
}

/// Builds the closed, curried recursive equality function on `Nat`,
/// returned as a thunk. Forcing it yields `λa. return (thunk (λb. a == b))`,
/// where `a == b` evaluates to the `Bool` representation of their equality.
fn nat_eq_thunk(heap: &mut Heap) -> NodeId {
    // Innermost comparison; environment is [b = 0, a = 1, self = 2].

    // a = 0: equal iff b = 0.
    let azero = {
        let b = heap.alloc_imm_val(MValue::Var(0));
        let zk = return_bool(heap, true);
        let sk = return_bool(heap, false);
        heap.alloc_comp(MComputation::Ifz { num: b, zk, sk })
    };

    // a = succ a' (env [a' = 0, b = 1, a = 2, self = 3]):
    //   b = 0   -> false
    //   b = b'  -> force self applied to a' then b'
    let recurse = {
        // env [a' = 0, b = 1, a = 2, self = 3]; ifz on b binds b' giving
        // env [b' = 0, a' = 1, b = 2, a = 3, self = 4].
        let self_var = heap.alloc_imm_val(MValue::Var(4));
        let force_self = heap.alloc_comp(MComputation::Force(self_var));
        let a_pred = heap.alloc_imm_val(MValue::Var(1)); // a'
        let apply_a = heap.alloc_comp(MComputation::App {
            op: force_self,
            arg: a_pred,
        });
        // First application returns a thunk bound at 0; b' shifts to 1.
        let thunk_var = heap.alloc_imm_val(MValue::Var(0));
        let force_thunk = heap.alloc_comp(MComputation::Force(thunk_var));
        let b_pred = heap.alloc_imm_val(MValue::Var(1)); // b'
        let apply_b = heap.alloc_comp(MComputation::App {
            op: force_thunk,
            arg: b_pred,
        });
        heap.alloc_comp(MComputation::Bind {
            comp: apply_a,
            cont: apply_b,
        })
    };
    let asucc = {
        let b = heap.alloc_imm_val(MValue::Var(1));
        let zk = return_bool(heap, false);
        heap.alloc_comp(MComputation::Ifz {
            num: b,
            zk,
            sk: recurse,
        })
    };

    let compare = {
        let a = heap.alloc_imm_val(MValue::Var(1));
        heap.alloc_comp(MComputation::Ifz {
            num: a,
            zk: azero,
            sk: asucc,
        })
    };
    let lam_b = heap.alloc_comp(MComputation::Lambda { body: compare });
    let thunk_b = heap.alloc_imm_val(MValue::Thunk(lam_b));
    let ret_lam_b = heap.alloc_comp(MComputation::Return(thunk_b));
    let lam_a = heap.alloc_comp(MComputation::Lambda { body: ret_lam_b });
    let rec = heap.alloc_comp(MComputation::Rec { body: lam_a });
    heap.alloc_imm_val(MValue::Thunk(rec))
}

/// Applies the curried `Nat` equality function (a thunk) to two argument
/// computations, yielding a computation that returns their equality `Bool`.
fn nat_eq_comp(heap: &mut Heap, lhs: Expr, rhs: Expr, tenv: &mut TEnv) -> CompId {
    let lhs_comp = elaborate_expr(heap, lhs, tenv);
    tenv.bind("_");
    let rhs_comp = elaborate_expr(heap, rhs, tenv);
    tenv.unbind();
    // Environment at the application: [b = 0, a = 1].
    let eq = nat_eq_thunk(heap);
    let force_eq = heap.alloc_comp(MComputation::Force(eq));
    let a = heap.alloc_imm_val(MValue::Var(1));
    let apply_a = heap.alloc_comp(MComputation::App {
        op: force_eq,
        arg: a,
    });
    // The first application returns a thunk, bound at 0; b shifts to 1.
    let thunk_var = heap.alloc_imm_val(MValue::Var(0));
    let force_thunk = heap.alloc_comp(MComputation::Force(thunk_var));
    let b = heap.alloc_imm_val(MValue::Var(1));
    let apply_b = heap.alloc_comp(MComputation::App {
        op: force_thunk,
        arg: b,
    });
    let recurse = heap.alloc_comp(MComputation::Bind {
        comp: apply_a,
        cont: apply_b,
    });
    let inner = heap.alloc_comp(MComputation::Bind {
        comp: rhs_comp,
        cont: recurse,
    });
    heap.alloc_comp(MComputation::Bind {
        comp: lhs_comp,
        cont: inner,
    })
}

/// Negates a computation producing a `Bool` by swapping `Inl`/`Inr`.
fn negate_comp(heap: &mut Heap, comp: CompId) -> CompId {
    let var0 = heap.alloc_imm_val(MValue::Var(0));
    let inlk = return_bool(heap, false);
    let inrk = return_bool(heap, true);
    let case = heap.alloc_comp(MComputation::Case {
        sum: var0,
        inlk,
        inrk,
    });
    heap.alloc_comp(MComputation::Bind { comp, cont: case })
}

/// Constant-folds a `Bool`-valued expression when it is fully literal.
fn const_bool(expr: &Expr) -> Option<bool> {
    match expr {
        Expr::Bool(b) => Some(*b),
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

/// Constant-folds equality of two fully-literal `Nat` operands (`==`/`!=` are
/// Nat-only; the type checker rejects other operand types).
fn const_eq(a: &Expr, b: &Expr) -> Option<bool> {
    Some(const_nat(a)? == const_nat(b)?)
}

/// Constant-folds a `Nat`-valued expression when it is fully literal.
fn const_nat(expr: &Expr) -> Option<u64> {
    match expr {
        Expr::Zero => Some(0),
        Expr::Nat(n) => Some(*n as u64),
        Expr::Succ(e) => Some(const_nat(e)? + 1),
        _ => None,
    }
}

fn elaborate_bexpr(heap: &mut Heap, bexpr: BExpr, tenv: &mut TEnv) -> CompId {
    if let Some(b) = const_bool(&Expr::BExpr(bexpr.clone())) {
        return return_bool(heap, b);
    }
    match bexpr {
        BExpr::Eq(lhs, rhs) => nat_eq_comp(heap, *lhs, *rhs, tenv),
        BExpr::NEq(lhs, rhs) => {
            let comp = nat_eq_comp(heap, *lhs, *rhs, tenv);
            negate_comp(heap, comp)
        }
        BExpr::And(lhs, rhs) => elaborate_connective(heap, *lhs, *rhs, true, tenv),
        BExpr::Or(lhs, rhs) => elaborate_connective(heap, *lhs, *rhs, false, tenv),
        BExpr::Not(e) => {
            let comp = elaborate_expr(heap, *e, tenv);
            negate_comp(heap, comp)
        }
    }
}

/// Elaborates `&&` (when `and`) or `||` by casing on the elaborated left `Bool`.
/// For `&&`: true (`Inl`) evaluates the right operand, false (`Inr`) is false.
/// For `||`: true short-circuits to true, false evaluates the right operand.
/// The left operand binds at index 0, then the `Case` payload binds at index 0,
/// so the right operand is elaborated under two extra binders.
fn elaborate_connective(
    heap: &mut Heap,
    lhs: Expr,
    rhs: Expr,
    and: bool,
    tenv: &mut TEnv,
) -> CompId {
    let lhs_comp = elaborate_expr(heap, lhs, tenv);
    tenv.bind("_");
    tenv.bind("_");
    let rhs_comp = elaborate_expr(heap, rhs, tenv);
    tenv.unbind();
    tenv.unbind();
    let (inlk, inrk) = if and {
        let f = return_bool(heap, false);
        (rhs_comp, f)
    } else {
        let t = return_bool(heap, true);
        (t, rhs_comp)
    };
    let var0 = heap.alloc_imm_val(MValue::Var(0));
    let case = heap.alloc_comp(MComputation::Case {
        sum: var0,
        inlk,
        inrk,
    });
    heap.alloc_comp(MComputation::Bind {
        comp: lhs_comp,
        cont: case,
    })
}

fn elaborate_list(heap: &mut Heap, elems: &[Expr], tenv: &mut TEnv) -> CompId {
    match elems {
        [] => {
            let nil = heap.alloc_imm_val(MValue::Nil);
            heap.alloc_comp(MComputation::Return(nil))
        }
        [head, tail @ ..] => {
            let chead = elaborate_expr(heap, head.clone(), tenv);
            tenv.bind("_");
            let ctail = elaborate_list(heap, tail, tenv);
            tenv.unbind();
            let var1 = heap.alloc_imm_val(MValue::Var(1));
            let var0 = heap.alloc_imm_val(MValue::Var(0));
            let cons = heap.alloc_imm_val(MValue::Cons(var1, var0));
            let ret = heap.alloc_comp(MComputation::Return(cons));
            let inner = heap.alloc_comp(MComputation::Bind {
                comp: ctail,
                cont: ret,
            });
            heap.alloc_comp(MComputation::Bind {
                comp: chead,
                cont: inner,
            })
        }
    }
}

fn elaborate_nat(heap: &mut Heap, n: usize) -> CompId {
    let val = heap.alloc_imm_val(MValue::Nat(n as u64));
    heap.alloc_comp(MComputation::Return(val))
}

fn elaborate_pair(heap: &mut Heap, fst: Expr, snd: Expr, tenv: &mut TEnv) -> CompId {
    let fst_comp = elaborate_expr(heap, fst, tenv);
    tenv.bind("_");
    let snd_comp = elaborate_expr(heap, snd, tenv);
    tenv.unbind();
    let var1 = heap.alloc_imm_val(MValue::Var(1));
    let var0 = heap.alloc_imm_val(MValue::Var(0));
    let pair = heap.alloc_imm_val(MValue::Pair(var1, var0));
    let ret = heap.alloc_comp(MComputation::Return(pair));
    let inner = heap.alloc_comp(MComputation::Bind {
        comp: snd_comp,
        cont: ret,
    });
    heap.alloc_comp(MComputation::Bind {
        comp: fst_comp,
        cont: inner,
    })
}
