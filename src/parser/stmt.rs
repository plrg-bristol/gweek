use crate::parser::cases::Cases;

use super::{expr::Expr, r#type::Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    If {
        cond: Box<Stmt>,
        then: Box<Stmt>,
        r#else: Box<Stmt>
    },
    Let {
        var: String,
        val: Box<Stmt>,
        body: Box<Stmt>
    },
    Exists {
        var: String,
        r#type: Type,
        body: Box<Stmt>
    },
    Equate {
        lhs: Expr,
        rhs: Expr,
        body: Box<Stmt>
    },
    Choice(Vec<Expr>),
    Case {
        expr: Expr,
        cases: Cases
    },
    Fail,
    Expr(Expr)
}
