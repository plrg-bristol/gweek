//! # The parser frontend
//!
//! Turns source text into the surface AST with [chumsky](https://github.com/zesterer/chumsky)
//! combinators. [`parse()`] is the only public entry point; the grammar lives in the private
//! `parse` module, while the AST node families are defined in the sibling modules re-exported
//! here:
//!
//! - [`Decl`](decl::Decl) — a top-level declaration: type signature, function, or bare statement.
//! - [`Stmt`](stmt::Stmt) — control and constraints: `if` / `let` / `exists` / `=:=` / `<>` /
//!   `case` / `fail`.
//! - [`Expr`](expr::Expr) — data and application; [`BExpr`](bexpr::BExpr) — boolean operators.
//! - `Type` — surface types; [`Arg`](arg::Arg) — function/lambda argument
//!   patterns; [`Cases`](cases::Cases) — the accumulator a `case` arm-list folds into.
//!
//! Comments (`-- …`) are stripped first, reserved words are protected, and the grammar layers
//! operator precedence: prefix `S` / `\` / `!`, then postfix cons `:` / boolean ops /
//! application, then the statement forms.

pub mod arg;
pub mod cases;
pub mod decl;
pub mod r#type;
pub mod stmt;
pub mod expr;
pub mod bexpr;
mod parse;

pub use parse::parse;
