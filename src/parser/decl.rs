use super::{arg::Arg, stmt::*, r#type::Type};

// Functions
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    FuncType {
        name: String,
        r#type: Type
    },
    Func {
        name: String,
        args: Vec<Arg>,
        body: Stmt
    },
    Stmt(Stmt)
}