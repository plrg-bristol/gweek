use std::collections::HashMap;
use std::fmt;

use crate::parser::{
    arg::Arg,
    bexpr::BExpr,
    cases::{Cases, CasesType},
    decl::Decl,
    expr::Expr,
    r#type::Type,
    stmt::Stmt,
};

#[derive(Debug)]
pub struct TypeError {
    pub msg: String,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

type TResult<T = Type> = Result<T, TypeError>;

fn err(msg: impl Into<String>) -> TypeError {
    TypeError { msg: msg.into() }
}

struct Ctx {
    vars: Vec<(String, Type)>,
    funcs: HashMap<String, Type>,
}

impl Ctx {
    fn new() -> Self {
        Ctx {
            vars: Vec::new(),
            funcs: HashMap::new(),
        }
    }

    fn lookup(&self, name: &str) -> TResult {
        // Local variables shadow, search from the end
        for (n, ty) in self.vars.iter().rev() {
            if n == name {
                return Ok(ty.clone());
            }
        }
        self.funcs
            .get(name)
            .cloned()
            .ok_or_else(|| err(format!("unbound variable '{name}'")))
    }

    fn bind(&mut self, name: &str, ty: Type) {
        self.vars.push((name.to_owned(), ty));
    }

    fn unbind(&mut self) {
        self.vars.pop();
    }

    fn bind_arg(&mut self, arg: &Arg, ty: &Type) -> TResult<()> {
        match (arg, ty) {
            (Arg::Ident(name), ty) => {
                self.bind(name, ty.clone());
                Ok(())
            }
            (Arg::Pair(a, b), Type::Product(ta, tb)) => {
                self.bind_arg(a, ta)?;
                self.bind_arg(b, tb)?;
                Ok(())
            }
            (Arg::Pair(..), ty) => Err(err(format!(
                "pattern match on pair but expected type {ty}"
            ))),
        }
    }

    fn unbind_arg(&mut self, arg: &Arg) {
        match arg {
            Arg::Ident(_) => {
                self.unbind();
            }
            Arg::Pair(a, b) => {
                self.unbind_arg(b);
                self.unbind_arg(a);
            }
        }
    }
}

fn unify(expected: &Type, actual: &Type) -> TResult<()> {
    match (expected, actual) {
        (Type::Any, _) | (_, Type::Any) => Ok(()),
        (Type::Ident(a), Type::Ident(b)) if a == b => Ok(()),
        (Type::List(a), Type::List(b)) => unify(a, b),
        (Type::Product(a1, b1), Type::Product(a2, b2)) => {
            unify(a1, a2)?;
            unify(b1, b2)
        }
        (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) => {
            unify(a1, a2)?;
            unify(b1, b2)
        }
        _ => Err(err(format!("type mismatch: expected {expected}, got {actual}"))),
    }
}

// Peel off the argument types from a function type: A -> B -> C gives ([A, B], C)
fn peel_arrows(ty: &Type, n: usize) -> TResult<(Vec<Type>, Type)> {
    if n == 0 {
        return Ok((Vec::new(), ty.clone()));
    }
    match ty {
        Type::Arrow(a, b) => {
            let (mut args, ret) = peel_arrows(b, n - 1)?;
            args.insert(0, *a.clone());
            Ok((args, ret))
        }
        _ => Err(err(format!(
            "expected function type with {n} more argument(s), got {ty}"
        ))),
    }
}

pub fn type_check(ast: &[Decl]) -> Result<(), Vec<TypeError>> {
    let mut ctx = Ctx::new();
    let mut errors = Vec::new();

    // First pass: collect all function type signatures
    for decl in ast {
        if let Decl::FuncType { name, r#type } = decl {
            ctx.funcs.insert(name.clone(), r#type.clone());
        }
    }

    // Second pass: check function bodies and bare statements
    for decl in ast {
        match decl {
            Decl::FuncType { .. } => {}
            Decl::Func { name, args, body } => {
                if let Some(declared) = ctx.funcs.get(name).cloned() {
                    if let Err(e) = check_func(&mut ctx, name, args, body, &declared) {
                        errors.push(e);
                    }
                }
                // If no type signature, skip checking (untyped function)
            }
            Decl::Stmt(stmt) => {
                if let Err(e) = synth_stmt(&mut ctx, stmt) {
                    errors.push(e);
                }
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn check_func(ctx: &mut Ctx, name: &str, args: &[Arg], body: &Stmt, ty: &Type) -> TResult<()> {
    let (arg_types, ret_type) = peel_arrows(ty, args.len())?;

    // Bind the function itself (for recursion)
    ctx.bind(name, ty.clone());

    // Bind the arguments
    for (arg, aty) in args.iter().zip(&arg_types) {
        ctx.bind_arg(arg, aty)?;
    }

    let body_type = synth_stmt(ctx, body)?;
    unify(&ret_type, &body_type).map_err(|e| {
        err(format!("in function '{name}': {e}"))
    })?;

    // Unbind arguments (in reverse order)
    for arg in args.iter().rev() {
        ctx.unbind_arg(arg);
    }
    // Unbind the function itself
    ctx.unbind();

    Ok(())
}

fn synth_stmt(ctx: &mut Ctx, stmt: &Stmt) -> TResult {
    match stmt {
        Stmt::Expr(e) => synth_expr(ctx, e),

        Stmt::Let { var, val, body } => {
            let val_type = synth_stmt(ctx, val)?;
            ctx.bind(var, val_type);
            let body_type = synth_stmt(ctx, body)?;
            ctx.unbind();
            Ok(body_type)
        }

        Stmt::Exists { var, r#type, body } => {
            let vtype = resolve_type(r#type)?;
            ctx.bind(var, vtype);
            let body_type = synth_stmt(ctx, body)?;
            ctx.unbind();
            Ok(body_type)
        }

        Stmt::Equate { lhs, rhs, body } => {
            let lt = synth_expr(ctx, lhs)?;
            let rt = synth_expr(ctx, rhs)?;
            unify(&lt, &rt).map_err(|e| err(format!("in equate: {e}")))?;
            synth_stmt(ctx, body)
        }

        Stmt::Fail => Ok(Type::Any),

        Stmt::Choice(exprs) => {
            let mut ty = None;
            for e in exprs {
                let t = synth_expr(ctx, e)?;
                if let Some(prev) = &ty {
                    unify(prev, &t).map_err(|e| err(format!("in choice: {e}")))?;
                } else {
                    ty = Some(t);
                }
            }
            ty.ok_or_else(|| err("empty choice"))
        }

        Stmt::Case { expr, cases } => synth_case(ctx, expr, cases),

        Stmt::If { cond, then, r#else } => {
            let ct = synth_stmt(ctx, cond)?;
            unify(&Type::Ident("Bool".to_string()), &ct)
                .map_err(|e| err(format!("if condition: {e}")))?;
            let tt = synth_stmt(ctx, then)?;
            let et = synth_stmt(ctx, r#else)?;
            unify(&tt, &et).map_err(|e| err(format!("if branches: {e}")))?;
            Ok(tt)
        }
    }
}

fn synth_case(ctx: &mut Ctx, scrutinee: &Expr, cases: &Cases) -> TResult {
    let scrut_type = synth_expr(ctx, scrutinee)?;

    match cases.r#type.as_ref() {
        Some(CasesType::Nat) => {
            unify(&Type::Ident("Nat".to_string()), &scrut_type)
                .map_err(|e| err(format!("case scrutinee: {e}")))?;

            let nat_case = cases.nat_case.as_ref()
                .ok_or_else(|| err("nat case missing branches"))?;

            let mut result_type: Option<Type> = None;

            if let Some(zk) = &nat_case.zk {
                let t = synth_stmt(ctx, zk)?;
                result_type = Some(t);
            }

            if let Some(sk) = &nat_case.sk {
                ctx.bind(&sk.var, Type::Ident("Nat".to_string()));
                let t = synth_stmt(ctx, &sk.body)?;
                ctx.unbind();
                if let Some(prev) = &result_type {
                    unify(prev, &t).map_err(|e| err(format!("case branches: {e}")))?;
                } else {
                    result_type = Some(t);
                }
            }

            result_type.ok_or_else(|| err("case with no branches"))
        }

        Some(CasesType::List) => {
            let elem_type = match &scrut_type {
                Type::List(t) => *t.clone(),
                _ => return Err(err(format!(
                    "list case on non-list type {scrut_type}"
                ))),
            };

            let list_case = cases.list_case.as_ref()
                .ok_or_else(|| err("list case missing branches"))?;

            let mut result_type: Option<Type> = None;

            if let Some(nilk) = &list_case.nilk {
                let t = synth_stmt(ctx, nilk)?;
                result_type = Some(t);
            }

            if let Some(consk) = &list_case.consk {
                ctx.bind(&consk.x, elem_type);
                ctx.bind(&consk.xs, scrut_type.clone());
                let t = synth_stmt(ctx, &consk.body)?;
                ctx.unbind();
                ctx.unbind();
                if let Some(prev) = &result_type {
                    unify(prev, &t).map_err(|e| err(format!("case branches: {e}")))?;
                } else {
                    result_type = Some(t);
                }
            }

            result_type.ok_or_else(|| err("case with no branches"))
        }

        None => Err(err("case with no pattern type")),
    }
}

fn synth_expr(ctx: &mut Ctx, expr: &Expr) -> TResult {
    match expr {
        Expr::Zero => Ok(Type::Ident("Nat".to_string())),

        Expr::Nat(_) => Ok(Type::Ident("Nat".to_string())),

        Expr::Succ(e) => {
            let t = synth_expr(ctx, e)?;
            unify(&Type::Ident("Nat".to_string()), &t)?;
            Ok(Type::Ident("Nat".to_string()))
        }

        Expr::Nil => Ok(Type::List(Box::new(Type::Any))),

        Expr::Bool(_) => Ok(Type::Ident("Bool".to_string())),

        Expr::Ident(name) => ctx.lookup(name),

        Expr::Cons(head, tail) => {
            let ht = synth_expr(ctx, head)?;
            let tt = synth_expr(ctx, tail)?;
            let expected_list = Type::List(Box::new(ht.clone()));
            unify(&expected_list, &tt).map_err(|e| err(format!("in cons: {e}")))?;
            Ok(expected_list)
        }

        Expr::List(elems) => {
            if elems.is_empty() {
                return Ok(Type::List(Box::new(Type::Any)));
            }
            let first_type = synth_expr(ctx, &elems[0])?;
            for e in &elems[1..] {
                let t = synth_expr(ctx, e)?;
                unify(&first_type, &t).map_err(|e| err(format!("in list literal: {e}")))?;
            }
            Ok(Type::List(Box::new(first_type)))
        }

        Expr::Pair(a, b) => {
            let at = synth_expr(ctx, a)?;
            let bt = synth_expr(ctx, b)?;
            Ok(Type::Product(Box::new(at), Box::new(bt)))
        }

        Expr::App(func, arg) => {
            let ft = synth_expr(ctx, func)?;
            match ft {
                Type::Arrow(param, ret) => {
                    let at = synth_expr(ctx, arg)?;
                    unify(&param, &at).map_err(|e| {
                        err(format!("in application: {e}"))
                    })?;
                    Ok(*ret)
                }
                _ => Err(err(format!("applying non-function type {ft}"))),
            }
        }

        Expr::Lambda(arg, body) => {
            Err(err("cannot infer type of lambda; needs a type annotation"))
        }

        Expr::BExpr(bexpr) => synth_bexpr(ctx, bexpr),

        Expr::Stmt(stmt) => synth_stmt(ctx, stmt),
    }
}

fn check_expr(ctx: &mut Ctx, expr: &Expr, expected: &Type) -> TResult<()> {
    match (expr, expected) {
        (Expr::Nil, Type::List(_)) => Ok(()),

        (Expr::Lambda(arg, body), Type::Arrow(param, ret)) => {
            ctx.bind_arg(arg, param)?;
            let ret_type = resolve_return_type(ret)?;
            let body_type = synth_stmt(ctx, body)?;
            ctx.unbind_arg(arg);
            unify(&ret_type, &body_type).map_err(|e| err(format!("in lambda body: {e}")))
        }

        _ => {
            let actual = synth_expr(ctx, expr)?;
            unify(expected, &actual)
        }
    }
}

fn synth_bexpr(ctx: &mut Ctx, bexpr: &BExpr) -> TResult {
    match bexpr {
        BExpr::Eq(a, b) | BExpr::NEq(a, b) => {
            let at = synth_expr(ctx, a)?;
            let bt = synth_expr(ctx, b)?;
            unify(&at, &bt).map_err(|e| err(format!("in comparison: {e}")))?;
            Ok(Type::Ident("Bool".to_string()))
        }
        BExpr::And(a, b) | BExpr::Or(a, b) => {
            let at = synth_expr(ctx, a)?;
            unify(&Type::Ident("Bool".to_string()), &at)?;
            let bt = synth_expr(ctx, b)?;
            unify(&Type::Ident("Bool".to_string()), &bt)?;
            Ok(Type::Ident("Bool".to_string()))
        }
        BExpr::Not(e) => {
            let t = synth_expr(ctx, e)?;
            unify(&Type::Ident("Bool".to_string()), &t)?;
            Ok(Type::Ident("Bool".to_string()))
        }
    }
}

fn resolve_type(ty: &Type) -> TResult {
    match ty {
        Type::Any => Ok(Type::Any),
        Type::Ident(s) => match s.as_str() {
            "Nat" | "Int" | "Bool" => Ok(ty.clone()),
            _ => Err(err(format!("unknown type '{s}'"))),
        },
        Type::List(t) => {
            let inner = resolve_type(t)?;
            Ok(Type::List(Box::new(inner)))
        }
        Type::Product(a, b) => {
            let a = resolve_type(a)?;
            let b = resolve_type(b)?;
            Ok(Type::Product(Box::new(a), Box::new(b)))
        }
        Type::Arrow(a, b) => {
            let a = resolve_type(a)?;
            let b = resolve_type(b)?;
            Ok(Type::Arrow(Box::new(a), Box::new(b)))
        }
    }
}

// For lambda checking: the return type of a function type
// A -> B means the lambda body should produce B
fn resolve_return_type(ty: &Type) -> TResult {
    Ok(ty.clone())
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Ident(s) => write!(f, "{s}"),
            Type::List(t) => write!(f, "[{t}]"),
            Type::Product(a, b) => write!(f, "{a} * {b}"),
            Type::Arrow(a, b) => {
                match **a {
                    Type::Arrow(..) => write!(f, "({a}) -> {b}"),
                    _ => write!(f, "{a} -> {b}"),
                }
            }
            Type::Any => write!(f, "_"),
        }
    }
}
