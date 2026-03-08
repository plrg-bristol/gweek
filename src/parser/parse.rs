use chumsky::prelude::*;

use crate::parser::{
    arg::Arg,
    bexpr::BExpr,
    cases::{Cases, CasesType},
    decl::Decl,
    expr::Expr,
    stmt::Stmt,
    r#type::Type,
};

pub fn parse(src: &str) -> Result<Vec<Decl>, Vec<Simple<char>>> {
    program().parse(src)
}

fn keyword<'a>(kw: &'a str) -> impl Parser<char, (), Error = Simple<char>> + Clone + 'a {
    text::keyword(kw).padded()
}

fn sym<'a>(s: &'a str) -> impl Parser<char, (), Error = Simple<char>> + Clone + 'a {
    just(s).padded().ignored()
}

fn ident() -> impl Parser<char, String, Error = Simple<char>> + Clone {
    text::ident().padded().try_map(|s: String, span| {
        match s.as_str() {
            "if" | "then" | "else" | "let" | "in" | "exists" | "case" | "of"
            | "true" | "false" | "fail" => Err(Simple::custom(span, format!("{s} is a keyword"))),
            _ => Ok(s),
        }
    })
}

fn number() -> impl Parser<char, usize, Error = Simple<char>> + Clone {
    text::int(10)
        .padded()
        .map(|s: String| s.parse().unwrap())
}

fn boolean() -> impl Parser<char, bool, Error = Simple<char>> + Clone {
    keyword("true").to(true)
        .or(keyword("false").to(false))
}

fn type_parser() -> impl Parser<char, Type, Error = Simple<char>> + Clone {
    recursive(|ty| {
        let primary_type = choice((
            ty.clone()
                .delimited_by(just('[').padded(), just(']').padded())
                .map(|t| Type::List(Box::new(t))),
            ty.clone()
                .delimited_by(just('(').padded(), just(')').padded()),
            ident().map(Type::Ident),
        ));

        primary_type.clone().then(
            choice((
                sym("->").to("->"),
                just('*').padded().ignored().to("*"),
            ))
            .then(ty)
            .or_not()
        ).map(|(lhs, rest)| {
            match rest {
                Some(("->", rhs)) => Type::Arrow(Box::new(lhs), Box::new(rhs)),
                Some(("*", rhs)) => Type::Product(Box::new(lhs), Box::new(rhs)),
                _ => lhs,
            }
        })
    })
}

fn argument() -> impl Parser<char, Arg, Error = Simple<char>> + Clone {
    recursive(|arg| {
        let arg_pair = arg.clone()
            .then_ignore(just(',').padded())
            .then(arg)
            .delimited_by(just('(').padded(), just(')').padded())
            .map(|(a, b)| Arg::Pair(Box::new(a), Box::new(b)));

        choice((
            arg_pair,
            ident().map(Arg::Ident),
        ))
    })
}

fn program() -> impl Parser<char, Vec<Decl>, Error = Simple<char>> {
    declaration().repeated().then_ignore(end())
}

fn declaration() -> impl Parser<char, Decl, Error = Simple<char>> {
    let func_type = ident()
        .then_ignore(sym("::"))
        .then(type_parser())
        .map(|(name, ty)| Decl::FuncType { name, r#type: ty });

    let func = ident()
        .then(argument().repeated())
        .then_ignore(just('=').padded())
        .then(statement_parser())
        .then_ignore(just('.').padded())
        .map(|((name, args), body)| Decl::Func { name, args, body });

    let bare_stmt = statement_parser()
        .then_ignore(just('.').padded())
        .map(Decl::Stmt);

    choice((
        func_type,
        func,
        bare_stmt,
    ))
}

fn statement_parser() -> impl Parser<char, Stmt, Error = Simple<char>> + Clone {
    recursive(|stmt| {
        let expr = expression(stmt.clone());

        let if_ = keyword("if")
            .ignore_then(stmt.clone())
            .then_ignore(keyword("then"))
            .then(stmt.clone())
            .then_ignore(keyword("else"))
            .then(stmt.clone())
            .map(|((cond, then), else_)| Stmt::If {
                cond: Box::new(cond),
                then: Box::new(then),
                r#else: Box::new(else_),
            });

        let let_ = keyword("let")
            .ignore_then(ident())
            .then_ignore(just('=').padded())
            .then(stmt.clone())
            .then_ignore(keyword("in"))
            .then(stmt.clone())
            .map(|((var, val), body)| Stmt::Let {
                var,
                val: Box::new(val),
                body: Box::new(body),
            });

        let exists = keyword("exists")
            .ignore_then(ident())
            .then_ignore(sym("::"))
            .then(type_parser())
            .then_ignore(just('.').padded())
            .then(stmt.clone())
            .map(|((var, ty), body)| Stmt::Exists {
                var,
                r#type: ty,
                body: Box::new(body),
            });

        let case = keyword("case")
            .ignore_then(expr.clone())
            .then_ignore(keyword("of"))
            .then(cases_parser(expr.clone(), stmt.clone()))
            .map(|(e, cases)| Stmt::Case { expr: e, cases });

        let fail = keyword("fail").to(Stmt::Fail);

        let expr_stmt = expr.clone().then(
            choice((
                sym("=:=")
                    .ignore_then(expr.clone())
                    .then_ignore(just('.').padded())
                    .then(stmt)
                    .map(|(rhs, body): (Expr, Stmt)| -> Box<dyn FnOnce(Expr) -> Stmt> {
                        Box::new(move |lhs| Stmt::Equate {
                            lhs,
                            rhs,
                            body: Box::new(body),
                        })
                    }),
                sym("<>")
                    .ignore_then(expr.separated_by(sym("<>")))
                    .map(|rest: Vec<Expr>| -> Box<dyn FnOnce(Expr) -> Stmt> {
                        Box::new(move |first| {
                            let mut all = vec![first];
                            all.extend(rest);
                            Stmt::Choice(all)
                        })
                    }),
            ))
            .or_not()
        ).map(|(e, cont)| {
            match cont {
                Some(f) => f(e),
                None => Stmt::Expr(e),
            }
        });

        choice((
            if_,
            let_,
            exists,
            case,
            fail,
            expr_stmt,
        ))
    })
}

fn expression(
    stmt: impl Parser<char, Stmt, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    recursive(move |expr: Recursive<'_, char, Expr, Simple<char>>| {
        let primary = primary_expr(stmt.clone(), expr.clone());

        let lambda = just('\\').padded()
            .ignore_then(argument())
            .then_ignore(just('.').padded())
            .then(stmt.clone())
            .map(|(arg, body)| Expr::Lambda(arg, Box::new(body)));

        let not_expr = just('!').padded()
            .ignore_then(primary.clone())
            .map(|e| Expr::BExpr(BExpr::Not(Box::new(e))));

        let succ = text::keyword::<_, _, Simple<char>>("S")
            .padded()
            .ignore_then(expr.clone())
            .map(|e| Expr::Succ(Box::new(e)));

        let bexpr_op = choice((
            sym("==").to("=="),
            sym("!=").to("!="),
            sym("&&").to("&&"),
            sym("||").to("||"),
        ));

        let postfix = primary.clone().then(
            choice((
                just(':').padded()
                    .ignore_then(expr)
                    .map(|rhs| PostOp::Cons(rhs)),
                bexpr_op.then(primary.clone())
                    .map(|(op, rhs)| PostOp::BExpr(op, rhs)),
                primary.repeated().at_least(1)
                    .map(PostOp::App),
            ))
            .or_not()
        ).map(|(lhs, post)| {
            match post {
                Some(PostOp::Cons(rhs)) => Expr::Cons(Box::new(lhs), Box::new(rhs)),
                Some(PostOp::BExpr(op, rhs)) => {
                    let bexpr = match op {
                        "==" => BExpr::Eq(Box::new(lhs), Box::new(rhs)),
                        "!=" => BExpr::NEq(Box::new(lhs), Box::new(rhs)),
                        "&&" => BExpr::And(Box::new(lhs), Box::new(rhs)),
                        "||" => BExpr::Or(Box::new(lhs), Box::new(rhs)),
                        _ => unreachable!(),
                    };
                    Expr::BExpr(bexpr)
                },
                Some(PostOp::App(args)) => {
                    args.into_iter().fold(lhs, |acc, arg| {
                        Expr::App(Box::new(acc), Box::new(arg))
                    })
                },
                None => lhs,
            }
        });

        choice((
            lambda,
            not_expr,
            succ,
            postfix,
        ))
    })
}

enum PostOp {
    Cons(Expr),
    BExpr(&'static str, Expr),
    App(Vec<Expr>),
}

fn primary_expr(
    stmt: impl Parser<char, Stmt, Error = Simple<char>> + Clone + 'static,
    expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    let nat_zero = text::keyword::<_, _, Simple<char>>("Z")
        .padded()
        .to(Expr::Zero);

    let list_nil = just('[').padded()
        .then(just(']').padded())
        .to(Expr::Nil);

    let pair = expr.clone()
        .then_ignore(just(',').padded())
        .then(expr.clone())
        .delimited_by(just('(').padded(), just(')').padded())
        .map(|(a, b)| Expr::Pair(Box::new(a), Box::new(b)));

    let list = expr.clone()
        .separated_by(just(',').padded())
        .at_least(1)
        .delimited_by(just('[').padded(), just(']').padded())
        .map(Expr::List);

    let paren = stmt
        .delimited_by(just('(').padded(), just(')').padded())
        .map(|s| Expr::Stmt(Box::new(s)));

    choice((
        nat_zero,
        list_nil,
        pair,
        list,
        boolean().map(Expr::Bool),
        number().map(Expr::Nat),
        ident().map(Expr::Ident),
        paren,
    ))
}

fn cases_parser(
    expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
    stmt: impl Parser<char, Stmt, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Cases, Error = Simple<char>> + Clone {
    let single_case = expr.clone()
        .then_ignore(sym("->"))
        .then(stmt);

    single_case.clone()
        .separated_by(just('|').padded())
        .at_least(1)
        .map(|case_list| {
            let mut cases = Cases::new();
            for (pattern, body) in case_list {
                match pattern.strip_parentheses() {
                    Expr::Zero => {
                        cases.set_type_or_check(CasesType::Nat);
                        cases.set_nat_zero(body);
                    },
                    Expr::Succ(e) => {
                        let var = match *e {
                            Expr::Ident(s) => s,
                            _ => panic!("expected identifier in succ case"),
                        };
                        cases.set_type_or_check(CasesType::Nat);
                        cases.set_nat_succ(var, body);
                    },
                    Expr::Nil => {
                        cases.set_type_or_check(CasesType::List);
                        cases.set_list_nil(body);
                    },
                    Expr::Cons(e1, e2) => {
                        let x = match *e1 {
                            Expr::Ident(s) => s,
                            _ => panic!("expected identifier in cons case"),
                        };
                        let xs = match *e2 {
                            Expr::Ident(s) => s,
                            _ => panic!("expected identifier in cons case"),
                        };
                        cases.set_type_or_check(CasesType::List);
                        cases.set_list_cons(x, xs, body);
                    },
                    _ => panic!("bad case pattern"),
                }
            }
            cases
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test1() {
        let src = "const :: a -> b -> a
const x y = x.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::FuncType {
                    name: "const".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("a".to_string())),
                        Box::new(Type::Arrow(
                            Box::new(Type::Ident("b".to_string())),
                            Box::new(Type::Ident("a".to_string()))
                        ))
                    )
                },
                Decl::Func {
                    name: "const".to_string(),
                    args: vec![Arg::Ident("x".to_string()), Arg::Ident("y".to_string())],
                    body: Stmt::Expr(Expr::Ident("x".to_string()))
                }
            ]
        )
    }

    #[test]
    fn test2() {
        let src = "const :: a -> b -> a
const x y = x.

id :: a -> a
id x = x.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::FuncType {
                    name: "const".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("a".to_string())),
                        Box::new(Type::Arrow(
                            Box::new(Type::Ident("b".to_string())),
                            Box::new(Type::Ident("a".to_string()))
                        ))
                    )
                },
                Decl::Func {
                    name: "const".to_string(),
                    args: vec![Arg::Ident("x".to_string()), Arg::Ident("y".to_string())],
                    body: Stmt::Expr(Expr::Ident("x".to_string()))
                },
                Decl::FuncType {
                    name: "id".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("a".to_string())),
                        Box::new(Type::Ident("a".to_string()))
                    )
                },
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Stmt::Expr(Expr::Ident("x".to_string()))
                }
            ]
        )
    }

    #[test]
    fn test3() {
        let src = "fix :: (Nat -> Nat) -> Nat
fix f = exists n :: Nat. f n =:= n. n.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::FuncType {
                    name: "fix".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Arrow(
                            Box::new(Type::Ident("Nat".to_string())),
                            Box::new(Type::Ident("Nat".to_string()))
                        )),
                        Box::new(Type::Ident("Nat".to_string()))
                    )
                },
                Decl::Func {
                    name: "fix".to_string(),
                    args: vec![Arg::Ident("f".to_string())],
                    body: Stmt::Exists {
                        var: "n".to_string(),
                        r#type: Type::Ident("Nat".to_string()),
                        body: Box::new(Stmt::Equate {
                            lhs: Expr::App(
                                Box::new(Expr::Ident("f".to_string())),
                                Box::new(Expr::Ident("n".to_string()))
                            ),
                            rhs: Expr::Ident("n".to_string()),
                            body: Box::new(Stmt::Expr(Expr::Ident("n".to_string())))
                        })
                    }
                }
            ]
        )
    }

    #[test]
    fn test4() {
        let src = "exists n :: Nat. n =:= 52. n.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Stmt(Stmt::Exists {
                    var: "n".to_string(),
                    r#type: Type::Ident("Nat".to_string()),
                    body: Box::new(Stmt::Equate {
                        lhs: Expr::Ident("n".to_string()),
                        rhs: Expr::Nat(52),
                        body: Box::new(Stmt::Expr(Expr::Ident("n".to_string())))
                    })
                })
            ]
        )
    }

    #[test]
    fn test5() {
        let src: &str = "id :: Nat -> Nat
id x = exists n :: Nat. n =:= x. n.

id 5.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::FuncType { name: "id".to_string(), r#type: Type::Arrow(
                    Box::new(Type::Ident("Nat".to_string())),
                    Box::new(Type::Ident("Nat".to_string())))
                },
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Stmt::Exists {
                        var: "n".to_string(),
                        r#type: Type::Ident("Nat".to_string()),
                        body: Box::new(Stmt::Equate {
                            lhs: Expr::Ident("n".to_string()),
                            rhs: Expr::Ident("x".to_string()),
                            body: Box::new(Stmt::Expr(Expr::Ident("n".to_string())))
                        })
                    }
                },
                Decl::Stmt(Stmt::Expr(Expr::App(
                    Box::new(Expr::Ident("id".to_string())),
                    Box::new(Expr::Nat(5))
                )))
            ]
        )
    }

    #[test]
    fn test6() {
        let src = "id x = x.

id 5.

id :: a -> a";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Stmt::Expr(Expr::Ident("x".to_string()))
                },
                Decl::Stmt(Stmt::Expr(Expr::App(
                    Box::new(Expr::Ident("id".to_string())),
                    Box::new(Expr::Nat(5))
                ))),
                Decl::FuncType {
                    name: "id".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("a".to_string())),
                        Box::new(Type::Ident("a".to_string()))
                    )
                }
            ]
        );
    }

    #[test]
    fn test7() {
        let src = "id :: a -> a
id x = x.

1 <> id 2 <> 3.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::FuncType {
                    name: "id".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("a".to_string())),
                        Box::new(Type::Ident("a".to_string())))
                    },
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Stmt::Expr(Expr::Ident("x".to_string()))
                },
                Decl::Stmt(Stmt::Choice(vec![
                    Expr::Nat(1), Expr::App(Box::new(Expr::Ident("id".to_string())), Box::new(Expr::Nat(2))), Expr::Nat(3)
                ]))
            ]
        )
    }

    #[test]
    fn test10() {
        let src = "true.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Stmt(Stmt::Expr(Expr::Bool(true)))
            ]
        );
    }

    #[test]
    fn test11() {
        let src = "true == false.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Stmt(Stmt::Expr(Expr::BExpr(BExpr::Eq(
                    Box::new(Expr::Bool(true)),
                    Box::new(Expr::Bool(false))
                ))))
            ]
        );
    }

    #[test]
    fn test12() {
        let src = "if !(1 != 2) then 0 else 1.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Stmt(Stmt::If {
                    cond: Box::new(Stmt::Expr(Expr::BExpr(BExpr::Not(Box::new(
                        Expr::Stmt(Box::new(Stmt::Expr(Expr::BExpr(BExpr::NEq(
                            Box::new(Expr::Nat(1)),
                            Box::new(Expr::Nat(2))
                        )))))
                    ))))),
                    then: Box::new(Stmt::Expr(Expr::Nat(0))),
                    r#else: Box::new(Stmt::Expr(Expr::Nat(1)))
                })
            ]
        );
    }

    #[test]
    fn test13() {
        let src = "exists xs :: [Nat]. xs =:= [1,2,3]. xs.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![
                Decl::Stmt(Stmt::Exists {
                    var: "xs".to_string(),
                    r#type: Type::List(Box::new(Type::Ident("Nat".to_string()))),
                    body: Box::new(Stmt::Equate {
                        lhs: Expr::Ident("xs".to_string()),
                        rhs: Expr::List(vec![Expr::Nat(1), Expr::Nat(2), Expr::Nat(3)]),
                        body: Box::new(Stmt::Expr(Expr::Ident("xs".to_string())))
                    })
                })
            ]
        )
    }

    #[test]
    fn test16() {
        let src = "pair :: a -> b * a * b";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::FuncType {
                name: "pair".to_string(),
                r#type: Type::Arrow(
                    Box::new(Type::Ident("a".to_string())),
                    Box::new(Type::Product(
                        Box::new(Type::Ident("b".into())),
                        Box::new(Type::Product(
                            Box::new(Type::Ident("a".into())),
                            Box::new(Type::Ident("b".into()))
                        ))
                    ))
                )
            }]
        )
    }

    #[test]
    fn test17() {
        let src = "half :: [Nat] -> [Nat] * [Nat]";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::FuncType {
                name: "half".to_string(),
                r#type: Type::Arrow(
                    Box::new(Type::List(Box::new(Type::Ident("Nat".to_string())))),
                    Box::new(Type::Product(
                        Box::new(Type::List(Box::new(Type::Ident("Nat".to_string())))),
                        Box::new(Type::List(Box::new(Type::Ident("Nat".to_string()))))
                    ))
                )
            }]
        )
    }

    #[test]
    fn test19() {
        let src = "1 : 2 : [3,4].";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Stmt(Stmt::Expr(Expr::Cons(
                Box::new(Expr::Nat(1)),
                Box::new(Expr::Cons(
                    Box::new(Expr::Nat(2)),
                    Box::new(Expr::List(vec![
                        Expr::Nat(3), Expr::Nat(4)
                    ]))
                ))
            )))]
        )
    }

    #[test]
    fn test20() {
        let src = "true && (false || true).";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Stmt(Stmt::Expr(Expr::BExpr(BExpr::And(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Stmt(Box::new(Stmt::Expr(Expr::BExpr(BExpr::Or(
                    Box::new(Expr::Bool(false)),
                    Box::new(Expr::Bool(true))
                ))))))
            ))))]
        )
    }
}
