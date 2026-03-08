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
    Stmt(Box<Stmt>)
}

impl Expr {
    pub fn strip_parentheses(self) -> Expr {
        let mut e = self;
        loop {
            match e {
                Expr::Stmt(stmt) => match *stmt {
                    Stmt::Expr(expr) => e = expr,
                    stmt => e = Expr::Stmt(Box::new(stmt))
                },
                _ => break
            }
        }

        e
    }
}