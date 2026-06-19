//! Expressions: data and application. An [`Expr`] covers the data constructors (`Z`/`S`, `[]`/
//! cons, pairs, list literals, booleans, numbers), identifiers, application, lambdas, boolean
//! expressions ([`BExpr`]), and a parenthesised statement.

use super::{arg::Arg, bexpr::BExpr, stmt::Stmt};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Zero,
    Succ(Box<Expr>),
    Nil,
    Cons(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    BExpr(BExpr),
    List(Vec<Expr>),
    Lambda(Arg, Box<Stmt>),
    Ident(String),
    Nat(usize),
    Bool(bool),
    Pair(Box<Expr>, Box<Expr>),
    Stmt(Box<Stmt>),
}

impl Expr {
    pub fn strip_parentheses(self) -> Expr {
        let mut e = self;
        while let Expr::Stmt(stmt) = e {
            match *stmt {
                Stmt::Expr(expr) => e = expr,
                other => {
                    e = Expr::Stmt(Box::new(other));
                    break;
                }
            }
        }

        e
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Regression: a parenthesised non-`Stmt::Expr` (e.g. `(let x = 0 in x)` used
    // as a case pattern) reaches the catch-all arm. It must return the wrapper
    // unchanged, not rewrap the same value and loop forever.
    #[test]
    fn strip_parentheses_terminates_on_non_expr_stmt() {
        let inner = Stmt::Let {
            var: "x".to_string(),
            val: Box::new(Stmt::Expr(Expr::Zero)),
            body: Box::new(Stmt::Expr(Expr::Ident("x".to_string()))),
        };
        let wrapped = Expr::Stmt(Box::new(inner.clone()));
        assert_eq!(wrapped.strip_parentheses(), Expr::Stmt(Box::new(inner)));
    }

    // Nested `((e))` wrappers are stripped down to the inner expression.
    #[test]
    fn strip_parentheses_unwraps_nested_expr_stmts() {
        let nested = Expr::Stmt(Box::new(Stmt::Expr(Expr::Stmt(Box::new(Stmt::Expr(
            Expr::Nat(5),
        ))))));
        assert_eq!(nested.strip_parentheses(), Expr::Nat(5));
    }
}
