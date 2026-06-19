//! # The parser frontend
//!
//! The frontend turns source text into the surface AST, by way of
//! [chumsky](https://github.com/zesterer/chumsky) combinators. [`parse()`] is the sole public entry
//! point; the AST node families live in the sibling modules — [`Decl`](decl::Decl),
//! [`Stmt`](stmt::Stmt), [`Expr`](expr::Expr), [`BExpr`](bexpr::BExpr), `Type`, [`Arg`](arg::Arg),
//! [`Cases`](cases::Cases). Comments are stripped first, the reserved words protected, and
//! precedence is layered from prefix, through postfix, to the statement forms.

pub mod arg;
pub mod bexpr;
pub mod cases;
pub mod decl;
pub mod expr;
mod parse;
pub mod stmt;
pub mod r#type;

pub use parse::parse;
