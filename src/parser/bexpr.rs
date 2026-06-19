//! Boolean expressions: the comparison and connective operators `==`, `!=`, `&&`, `||`, `!`.

use super::expr::Expr;

// Boolean expressions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BExpr {
    Eq(Box<Expr>, Box<Expr>),
    NEq(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
}
