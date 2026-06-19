//! # The type checker
//!
//! A two-pass bidirectional type checker with Hindley–Milner-style instantiation. [`type_check`]
//! gathers the function signatures first — so the functions may refer to one another — then checks
//! each body, accumulating every [`TypeError`] rather than halting at the first. Unification is
//! Robinson's, over a substitution whose metavariables are encoded as `Type::Ident("?<id>")`, a
//! name the lexer can never produce; polymorphism is real instantiation, each use of a global
//! signature receiving fresh metavariables. The checker is also a gatekeeper — it rejects exactly
//! the programs that would otherwise reach an unreachable `panic!` downstream (unknown types,
//! non-`Nat` equality, pair-pattern lambda arguments).

use std::collections::HashMap;
use std::fmt;

use crate::parser::ast::{Arg, BExpr, Cases, CasesType, Decl, Expr, Type};

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
    // Substitution for unification metavariables, indexed by metavar id.
    // A metavar is represented as Type::Ident("?<id>"), a name the lexer can
    // never produce, so it cannot clash with a user-written type variable.
    subst: Vec<Option<Type>>,
}

// A signature type variable is a lowercase-initial Ident (e.g. `a`), as opposed
// to a concrete type (`Nat`, `Bool`) which is uppercase-initial.
fn is_type_var(s: &str) -> bool {
    s.chars().next().is_some_and(char::is_lowercase)
}

// Parse the metavar id out of a "?<id>" name, if this is a metavar Ident.
fn as_meta(s: &str) -> Option<usize> {
    s.strip_prefix('?').and_then(|n| n.parse().ok())
}

// A pair argument is destructured during elaboration through typed logic variables,
// which needs a concrete value type for each component (no type variables,
// functions, or wildcards). This mirrors what `elaborate::elaborate_vtype` can
// elaborate, so the checker rejects the unsupported cases instead of letting them
// panic in the elaborator.
fn is_concrete_value_type(ty: &Type) -> bool {
    match ty {
        Type::Ident(s) => s == "Nat" || s == "Bool",
        Type::List(t) => is_concrete_value_type(t),
        Type::Product(a, b) => is_concrete_value_type(a) && is_concrete_value_type(b),
        Type::Arrow(..) | Type::Any => false,
    }
}

impl Ctx {
    fn new() -> Self {
        Ctx {
            vars: Vec::new(),
            funcs: HashMap::new(),
            subst: Vec::new(),
        }
    }

    fn fresh_meta(&mut self) -> Type {
        let id = self.subst.len();
        self.subst.push(None);
        Type::Ident(format!("?{id}"))
    }

    // Instantiate a (possibly polymorphic) signature: replace each distinct
    // signature type variable with a fresh metavar, consistently within this
    // one instantiation, so e.g. `a -> a` becomes `?0 -> ?0`.
    fn instantiate(&mut self, ty: &Type) -> Type {
        let mut mapping = HashMap::new();
        self.instantiate_with(ty, &mut mapping)
    }

    fn instantiate_with(&mut self, ty: &Type, mapping: &mut HashMap<String, Type>) -> Type {
        match ty {
            Type::Ident(s) if is_type_var(s) => mapping
                .entry(s.clone())
                .or_insert_with(|| self.fresh_meta())
                .clone(),
            Type::Ident(_) | Type::Any => ty.clone(),
            Type::List(t) => Type::List(Box::new(self.instantiate_with(t, mapping))),
            Type::Product(a, b) => Type::Product(
                Box::new(self.instantiate_with(a, mapping)),
                Box::new(self.instantiate_with(b, mapping)),
            ),
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.instantiate_with(a, mapping)),
                Box::new(self.instantiate_with(b, mapping)),
            ),
        }
    }

    fn lookup(&mut self, name: &str) -> TResult {
        // Local variables shadow, search from the end. Local bindings are
        // monomorphic, so they are returned as-is.
        for (n, ty) in self.vars.iter().rev() {
            if n == name {
                return Ok(ty.clone());
            }
        }
        // Top-level functions are the only generalized bindings: instantiate
        // their signature with fresh metavars at every use site.
        match self.funcs.get(name).cloned() {
            Some(ty) => Ok(self.instantiate(&ty)),
            None => Err(err(format!("unbound variable '{name}'"))),
        }
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
            (Arg::Pair(a, b), ty @ Type::Product(ta, tb)) => {
                if !is_concrete_value_type(ty) {
                    return Err(err(format!(
                        "pair-pattern arguments need concrete component types, got {ty}"
                    )));
                }
                self.bind_arg(a, ta)?;
                self.bind_arg(b, tb)?;
                Ok(())
            }
            (Arg::Pair(..), ty) => {
                Err(err(format!("pattern match on pair but expected type {ty}")))
            }
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

    // Follow the substitution to the head of `ty`: if it is a bound metavar,
    // chase the chain; otherwise return `ty` unchanged.
    fn resolve(&self, ty: &Type) -> Type {
        if let Type::Ident(s) = ty {
            if let Some(id) = as_meta(s) {
                if let Some(bound) = &self.subst[id] {
                    return self.resolve(bound);
                }
            }
        }
        ty.clone()
    }

    // Does metavar `id` occur in `ty` (following the substitution)?
    fn occurs(&self, id: usize, ty: &Type) -> bool {
        match ty {
            Type::Ident(s) => match as_meta(s) {
                Some(other) => {
                    other == id
                        || self.subst[other]
                            .as_ref()
                            .is_some_and(|t| self.occurs(id, t))
                }
                None => false,
            },
            Type::List(t) => self.occurs(id, t),
            Type::Product(a, b) | Type::Arrow(a, b) => self.occurs(id, a) || self.occurs(id, b),
            Type::Any => false,
        }
    }

    // Bind metavar `id` to `ty` (already resolved at the head), with an occurs
    // check to reject infinite types.
    fn bind_meta(&mut self, id: usize, ty: &Type) -> TResult<()> {
        if let Type::Ident(s) = ty {
            if as_meta(s) == Some(id) {
                return Ok(());
            }
        }
        if self.occurs(id, ty) {
            return Err(err(format!(
                "cannot construct infinite type: ?{id} occurs in {ty}"
            )));
        }
        self.subst[id] = Some(ty.clone());
        Ok(())
    }

    fn unify(&mut self, expected: &Type, actual: &Type) -> TResult<()> {
        let e = self.resolve(expected);
        let a = self.resolve(actual);
        match (&e, &a) {
            (Type::Any, _) | (_, Type::Any) => Ok(()),
            (Type::Ident(es), Type::Ident(a_)) if es == a_ => Ok(()),
            (Type::Ident(es), _) if as_meta(es).is_some() => {
                self.bind_meta(as_meta(es).unwrap(), &a)
            }
            (_, Type::Ident(a_)) if as_meta(a_).is_some() => {
                self.bind_meta(as_meta(a_).unwrap(), &e)
            }
            (Type::List(l1), Type::List(l2)) => self.unify(l1, l2),
            (Type::Product(a1, b1), Type::Product(a2, b2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)
            }
            (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)
            }
            _ => Err(err(format!("type mismatch: expected {e}, got {a}"))),
        }
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
            Decl::Expr(expr) => {
                if let Err(e) = synth_expr(&mut ctx, expr) {
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

fn check_func(ctx: &mut Ctx, name: &str, args: &[Arg], body: &Expr, ty: &Type) -> TResult<()> {
    let (arg_types, ret_type) = peel_arrows(ty, args.len())?;

    // Bind the function itself (for recursion)
    ctx.bind(name, ty.clone());

    // Bind the arguments
    for (arg, aty) in args.iter().zip(&arg_types) {
        ctx.bind_arg(arg, aty)?;
    }

    let body_type = synth_expr(ctx, body)?;
    ctx.unify(&ret_type, &body_type)
        .map_err(|e| err(format!("in function '{name}': {e}")))?;

    // Unbind arguments (in reverse order)
    for arg in args.iter().rev() {
        ctx.unbind_arg(arg);
    }
    // Unbind the function itself
    ctx.unbind();

    Ok(())
}

fn synth_case(ctx: &mut Ctx, scrutinee: &Expr, cases: &Cases) -> TResult {
    let scrut_type = synth_expr(ctx, scrutinee)?;

    match cases.r#type.as_ref() {
        Some(CasesType::Nat) => {
            ctx.unify(&Type::Ident("Nat".to_string()), &scrut_type)
                .map_err(|e| err(format!("case scrutinee: {e}")))?;

            let nat_case = cases
                .nat_case
                .as_ref()
                .ok_or_else(|| err("nat case missing branches"))?;

            let mut result_type: Option<Type> = None;

            if let Some(zk) = &nat_case.zk {
                let t = synth_expr(ctx, zk)?;
                result_type = Some(t);
            }

            if let Some(sk) = &nat_case.sk {
                ctx.bind(&sk.var, Type::Ident("Nat".to_string()));
                let t = synth_expr(ctx, &sk.body)?;
                ctx.unbind();
                if let Some(prev) = &result_type {
                    ctx.unify(prev, &t)
                        .map_err(|e| err(format!("case branches: {e}")))?;
                } else {
                    result_type = Some(t);
                }
            }

            result_type.ok_or_else(|| err("case with no branches"))
        }

        Some(CasesType::List) => {
            let elem_type = match &scrut_type {
                Type::List(t) => *t.clone(),
                _ => return Err(err(format!("list case on non-list type {scrut_type}"))),
            };

            let list_case = cases
                .list_case
                .as_ref()
                .ok_or_else(|| err("list case missing branches"))?;

            let mut result_type: Option<Type> = None;

            if let Some(nilk) = &list_case.nilk {
                let t = synth_expr(ctx, nilk)?;
                result_type = Some(t);
            }

            if let Some(consk) = &list_case.consk {
                ctx.bind(&consk.x, elem_type);
                ctx.bind(&consk.xs, scrut_type.clone());
                let t = synth_expr(ctx, &consk.body)?;
                ctx.unbind();
                ctx.unbind();
                if let Some(prev) = &result_type {
                    ctx.unify(prev, &t)
                        .map_err(|e| err(format!("case branches: {e}")))?;
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
            ctx.unify(&Type::Ident("Nat".to_string()), &t)?;
            Ok(Type::Ident("Nat".to_string()))
        }

        Expr::Nil => Ok(Type::List(Box::new(Type::Any))),

        Expr::Bool(_) => Ok(Type::Ident("Bool".to_string())),

        Expr::Ident(name) => ctx.lookup(name),

        Expr::Cons(head, tail) => {
            let ht = synth_expr(ctx, head)?;
            let tt = synth_expr(ctx, tail)?;
            let expected_list = Type::List(Box::new(ht.clone()));
            ctx.unify(&expected_list, &tt)
                .map_err(|e| err(format!("in cons: {e}")))?;
            Ok(expected_list)
        }

        Expr::List(elems) => {
            if elems.is_empty() {
                return Ok(Type::List(Box::new(Type::Any)));
            }
            let first_type = synth_expr(ctx, &elems[0])?;
            for e in &elems[1..] {
                let t = synth_expr(ctx, e)?;
                ctx.unify(&first_type, &t)
                    .map_err(|e| err(format!("in list literal: {e}")))?;
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
            match ctx.resolve(&ft) {
                Type::Arrow(param, ret) => {
                    check_expr(ctx, arg, &param)
                        .map_err(|e| err(format!("in application: {e}")))?;
                    Ok(*ret)
                }
                ft => Err(err(format!("applying non-function type {ft}"))),
            }
        }

        Expr::Lambda(..) => Err(err("cannot infer type of lambda; needs a type annotation")),

        Expr::BExpr(bexpr) => synth_bexpr(ctx, bexpr),

        Expr::Let { var, val, body } => {
            let val_type = synth_expr(ctx, val)?;
            ctx.bind(var, val_type);
            let body_type = synth_expr(ctx, body)?;
            ctx.unbind();
            Ok(body_type)
        }

        Expr::Exists { var, r#type, body } => {
            let vtype = resolve_type(r#type)?;
            ctx.bind(var, vtype);
            let body_type = synth_expr(ctx, body)?;
            ctx.unbind();
            Ok(body_type)
        }

        Expr::Equate { lhs, rhs, body } => {
            let lt = synth_expr(ctx, lhs)?;
            let rt = synth_expr(ctx, rhs)?;
            ctx.unify(&lt, &rt)
                .map_err(|e| err(format!("in equate: {e}")))?;
            synth_expr(ctx, body)
        }

        Expr::Fail => Ok(Type::Any),

        Expr::Choice(exprs) => {
            let mut ty = None;
            for e in exprs {
                let t = synth_expr(ctx, e)?;
                if let Some(prev) = &ty {
                    ctx.unify(prev, &t)
                        .map_err(|e| err(format!("in choice: {e}")))?;
                } else {
                    ty = Some(t);
                }
            }
            ty.ok_or_else(|| err("empty choice"))
        }

        Expr::Case { expr, cases } => synth_case(ctx, expr, cases),

        Expr::If { cond, then, r#else } => {
            let ct = synth_expr(ctx, cond)?;
            ctx.unify(&Type::Ident("Bool".to_string()), &ct)
                .map_err(|e| err(format!("if condition: {e}")))?;
            let tt = synth_expr(ctx, then)?;
            let et = synth_expr(ctx, r#else)?;
            ctx.unify(&tt, &et)
                .map_err(|e| err(format!("if branches: {e}")))?;
            Ok(tt)
        }
    }
}

fn check_expr(ctx: &mut Ctx, expr: &Expr, expected: &Type) -> TResult<()> {
    match (expr, expected) {
        (Expr::Nil, Type::List(_)) => Ok(()),

        (Expr::Lambda(arg, body), Type::Arrow(param, ret)) => {
            // A lambda carries no type annotation, so elaboration cannot type
            // the components of a destructured pair argument. Reject it here
            // (named arguments and projection work); functions, which have a
            // declared signature, do support pair arguments.
            if matches!(arg, Arg::Pair(..)) {
                return Err(err(
                    "pair-pattern lambda arguments are not supported; bind a name and project",
                ));
            }
            ctx.bind_arg(arg, param)?;
            let result =
                check_expr(ctx, body, ret).map_err(|e| err(format!("in lambda body: {e}")));
            ctx.unbind_arg(arg);
            result
        }

        _ => {
            let actual = synth_expr(ctx, expr)?;
            ctx.unify(expected, &actual)
        }
    }
}

fn synth_bexpr(ctx: &mut Ctx, bexpr: &BExpr) -> TResult {
    match bexpr {
        BExpr::Eq(a, b) | BExpr::NEq(a, b) => {
            // `==`/`!=` are Nat equality (elaborated through `Ifz`); both operands
            // must be Nat. Comparing other types has no elaboration and is rejected
            // here rather than panicking in the machine.
            let nat = Type::Ident("Nat".to_string());
            let at = synth_expr(ctx, a)?;
            let bt = synth_expr(ctx, b)?;
            ctx.unify(&nat, &at)
                .map_err(|e| err(format!("in comparison: {e}")))?;
            ctx.unify(&nat, &bt)
                .map_err(|e| err(format!("in comparison: {e}")))?;
            Ok(Type::Ident("Bool".to_string()))
        }
        BExpr::And(a, b) | BExpr::Or(a, b) => {
            let at = synth_expr(ctx, a)?;
            ctx.unify(&Type::Ident("Bool".to_string()), &at)?;
            let bt = synth_expr(ctx, b)?;
            ctx.unify(&Type::Ident("Bool".to_string()), &bt)?;
            Ok(Type::Ident("Bool".to_string()))
        }
        BExpr::Not(e) => {
            let t = synth_expr(ctx, e)?;
            ctx.unify(&Type::Ident("Bool".to_string()), &t)?;
            Ok(Type::Ident("Bool".to_string()))
        }
    }
}

fn resolve_type(ty: &Type) -> TResult {
    match ty {
        Type::Any => Ok(Type::Any),
        Type::Ident(s) => match s.as_str() {
            "Nat" | "Bool" => Ok(ty.clone()),
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Ident(s) => write!(f, "{s}"),
            Type::List(t) => write!(f, "[{t}]"),
            Type::Product(a, b) => write!(f, "{a} * {b}"),
            Type::Arrow(a, b) => match **a {
                Type::Arrow(..) => write!(f, "({a}) -> {b}"),
                _ => write!(f, "{a} -> {b}"),
            },
            Type::Any => write!(f, "_"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn check(src: &str) -> Result<(), Vec<TypeError>> {
        let ast = parse(src).expect("source should parse");
        type_check(&ast)
    }

    // B4: a polymorphic signature can be instantiated at a concrete type.
    #[test]
    fn poly_id_applied_at_nat() {
        assert!(check("id :: a -> a\nid x = x.\n\nid 5.\n").is_ok());
    }

    #[test]
    fn poly_id_applied_at_list() {
        assert!(check("id :: a -> a\nid x = x.\n\nid [1,2,3].\n").is_ok());
    }

    // B4: distinct rigid type variables must stay distinct (this is real
    // instantiation, not treating type variables as wildcards).
    #[test]
    fn rigid_type_vars_are_not_wildcards() {
        assert!(check("bad :: a -> b\nbad x = x.\n\nbad 5.\n").is_err());
    }

    // B5: a lambda argument is checked against the known parameter type.
    #[test]
    fn lambda_argument_is_checked() {
        assert!(check("app :: (Nat -> Nat) -> Nat\napp f = f 1.\n\napp (\\x. S x).\n").is_ok());
    }

    #[test]
    fn ill_typed_lambda_argument_rejected() {
        assert!(check("app :: (Nat -> Nat) -> Nat\napp f = f 1.\n\napp (\\x. [x]).\n").is_err());
    }

    // B11: `Int` is not part of the type alphabet (was accepted, then panicked).
    #[test]
    fn int_is_a_type_error() {
        assert!(check("exists n :: Int. n.\n").is_err());
    }

    // A4: conditions that used to type-check and then panic in the machine /
    // elaborator are now clean type errors.
    #[test]
    fn bool_equality_is_a_type_error() {
        // `==`/`!=` are Nat-only; comparing Bools would panic with "Ifz on ..".
        assert!(check("true == false.\n").is_err());
    }

    #[test]
    fn pair_pattern_lambda_is_a_type_error() {
        let src = "app :: ((Nat * Nat) -> Nat) -> Nat\napp g = g (1,2).\n\napp (\\(x,y). x).\n";
        assert!(check(src).is_err());
    }

    #[test]
    fn polymorphic_pair_argument_is_a_type_error() {
        // Pair components need concrete value types to be destructured.
        assert!(check("fst :: (a * b) -> a\nfst (x,y) = x.\n\nfst (1,2).\n").is_err());
    }
}
