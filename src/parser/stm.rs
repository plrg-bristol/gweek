use crate::parser::cases::Cases;

use super::{expr::Expr, r#type::Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stm {
    If {
        cond: Box<Stm>,
        then: Box<Stm>,
        r#else: Box<Stm>
    },
    Let {
        var: String,
        val: Box<Stm>,
        body: Box<Stm>
    },
    Exists {
        var: String,
        r#type: Type,
        body: Box<Stm>
    },
    Equate {
        lhs: Expr,
        rhs: Expr,
        body: Box<Stm>
    },
    Choice(Vec<Expr>),
    Case {
        expr: Expr,
        cases: Cases
    },
    Fail,
    Expr(Expr)
}
