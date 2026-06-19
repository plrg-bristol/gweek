//! # The parser frontend
//!
//! The frontend turns source text into the surface AST, by way of
//! [chumsky](https://github.com/zesterer/chumsky) combinators. [`parse()`] is the sole public entry
//! point; the AST node families all live in [`ast`] — [`Decl`](ast::Decl), [`Stmt`](ast::Stmt),
//! [`Expr`](ast::Expr), [`BExpr`](ast::BExpr), [`Type`](ast::Type), [`Arg`](ast::Arg),
//! [`Cases`](ast::Cases). Comments are stripped first, the reserved words protected, and
//! precedence is layered from prefix, through postfix, to the statement forms.

pub mod ast;
mod parse;

pub use parse::parse;
