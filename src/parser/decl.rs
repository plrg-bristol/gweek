//! Top-level declarations. A [`Decl`] is a type signature (`name :: type`), a function
//! definition (`name arg* = body`), or a bare statement to be run.

use super::{arg::Arg, r#type::Type, stmt::*};

// Functions
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    FuncType {
        name: String,
        r#type: Type,
    },
    Func {
        name: String,
        args: Vec<Arg>,
        body: Stmt,
    },
    Stmt(Stmt),
}
