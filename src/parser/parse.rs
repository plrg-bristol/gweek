//! # The grammar
//!
//! The chumsky grammar behind [`parse`]. Having stripped the `--` comments, it is a stack of
//! `recursive` parsers — `program`, `declaration`, `expression`, `application`, `primary_expr` —
//! with `type_parser` binding `*` more tightly than `->`. The three expression tiers layer
//! precedence: the binding and control forms (`if`, `let`, `case`, …) sit outermost, application
//! and operators in the middle, atoms innermost. A case pattern that is neither `Nat`- nor
//! `List`-shaped becomes a recoverable parse error, never a panic.

use chumsky::prelude::*;

use crate::parser::ast::{Arg, BExpr, Cases, CasesType, Decl, Expr, Type};

pub fn parse(src: &str) -> Result<Vec<Decl>, Vec<Simple<char>>> {
    let src = strip_comments(src);
    program().parse(src)
}

fn strip_comments(src: &str) -> String {
    src.lines()
        .map(|line| match line.find("--") {
            Some(i) => &line[..i],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn keyword<'a>(kw: &'a str) -> impl Parser<char, (), Error = Simple<char>> + Clone + 'a {
    text::keyword(kw).padded()
}

fn sym<'a>(s: &'a str) -> impl Parser<char, (), Error = Simple<char>> + Clone + 'a {
    just(s).padded().ignored()
}

fn ident() -> impl Parser<char, String, Error = Simple<char>> + Clone {
    text::ident()
        .padded()
        .try_map(|s: String, span| match s.as_str() {
            "if" | "then" | "else" | "let" | "in" | "exists" | "case" | "of" | "true" | "false"
            | "fail" => Err(Simple::custom(span, format!("{s} is a keyword"))),
            _ => Ok(s),
        })
}

fn number() -> impl Parser<char, usize, Error = Simple<char>> + Clone {
    text::int(10).padded().map(|s: String| s.parse().unwrap())
}

fn boolean() -> impl Parser<char, bool, Error = Simple<char>> + Clone {
    keyword("true").to(true).or(keyword("false").to(false))
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

        let product = primary_type
            .clone()
            .separated_by(just('*').padded())
            .at_least(1)
            .map(|factors| {
                let mut iter = factors.into_iter().rev();
                let last = iter.next().unwrap();
                iter.fold(last, |acc, factor| {
                    Type::Product(Box::new(factor), Box::new(acc))
                })
            });

        product
            .clone()
            .then(sym("->").ignore_then(ty).or_not())
            .map(|(lhs, rhs)| match rhs {
                Some(rhs) => Type::Arrow(Box::new(lhs), Box::new(rhs)),
                None => lhs,
            })
    })
}

fn argument() -> impl Parser<char, Arg, Error = Simple<char>> + Clone {
    recursive(|arg| {
        let arg_pair = arg
            .clone()
            .then_ignore(just(',').padded())
            .then(arg)
            .delimited_by(just('(').padded(), just(')').padded())
            .map(|(a, b)| Arg::Pair(Box::new(a), Box::new(b)));

        choice((arg_pair, ident().map(Arg::Ident)))
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
        .then(expression())
        .then_ignore(just('.').padded())
        .map(|((name, args), body)| Decl::Func { name, args, body });

    let bare_expr = expression().then_ignore(just('.').padded()).map(Decl::Expr);

    choice((func_type, func, bare_expr))
}

fn expression() -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    recursive(|expr| {
        let app = application(expr.clone());

        let if_ = keyword("if")
            .ignore_then(expr.clone())
            .then_ignore(keyword("then"))
            .then(expr.clone())
            .then_ignore(keyword("else"))
            .then(expr.clone())
            .map(|((cond, then), else_)| Expr::If {
                cond: Box::new(cond),
                then: Box::new(then),
                r#else: Box::new(else_),
            });
        let let_ = keyword("let")
            .ignore_then(
                keyword("strict")
                    .ignore_then(ident().map(|var| (true, var)))
                    .or(ident().map(|var| (false, var))),
            )
            .then_ignore(just('=').padded())
            .then(expr.clone())
            .then_ignore(keyword("in"))
            .then(expr.clone())
            .map(|(((is_strict, var), val), body)| {
                if is_strict {
                    Expr::LetStrict {
                        var,
                        val: Box::new(val),
                        body: Box::new(body),
                    }
                } else {
                    Expr::Let {
                        var,
                        val: Box::new(val),
                        body: Box::new(body),
                    }
                }
            });
        let exists = keyword("exists")
            .ignore_then(ident())
            .then_ignore(sym("::"))
            .then(type_parser())
            .then_ignore(just('.').padded())
            .then(expr.clone())
            .map(|((var, ty), body)| Expr::Exists {
                var,
                r#type: ty,
                body: Box::new(body),
            });

        let case = keyword("case")
            .ignore_then(app.clone())
            .then_ignore(keyword("of"))
            .then(cases_parser(app.clone(), expr.clone()))
            .map(|(e, cases)| Expr::Case {
                expr: Box::new(e),
                cases,
            });

        let fail = keyword("fail").to(Expr::Fail);

        let app_expr = app
            .clone()
            .then(
                choice((
                    sym("=:=")
                        .ignore_then(app.clone())
                        .then_ignore(just('.').padded())
                        .then(expr)
                        .map(
                            |(rhs, body): (Expr, Expr)| -> Box<dyn FnOnce(Expr) -> Expr> {
                                Box::new(move |lhs| Expr::Equate {
                                    lhs: Box::new(lhs),
                                    rhs: Box::new(rhs),
                                    body: Box::new(body),
                                })
                            },
                        ),
                    sym("<>").ignore_then(app.separated_by(sym("<>"))).map(
                        |rest: Vec<Expr>| -> Box<dyn FnOnce(Expr) -> Expr> {
                            Box::new(move |first| {
                                let mut all = vec![first];
                                all.extend(rest);
                                Expr::Choice(all)
                            })
                        },
                    ),
                ))
                .or_not(),
            )
            .map(|(e, cont)| match cont {
                Some(f) => f(e),
                None => e,
            });

        choice((if_, let_, exists, case, fail, app_expr))
    })
}

fn application(
    expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    recursive(move |app: Recursive<'_, char, Expr, Simple<char>>| {
        let primary = primary_expr(expr.clone(), app.clone());

        let lambda = just('\\')
            .padded()
            .ignore_then(argument())
            .then_ignore(just('.').padded())
            .then(expr.clone())
            .map(|(arg, body)| Expr::Lambda(arg, Box::new(body)));

        let not_expr = just('!')
            .padded()
            .ignore_then(primary.clone())
            .map(|e| Expr::BExpr(BExpr::Not(Box::new(e))));

        let succ = text::keyword::<_, _, Simple<char>>("S")
            .padded()
            .ignore_then(app.clone())
            .map(|e| Expr::Succ(Box::new(e)));

        let bexpr_op = choice((
            sym("==").to("=="),
            sym("!=").to("!="),
            sym("&&").to("&&"),
            sym("||").to("||"),
        ));

        let postfix = primary
            .clone()
            .then(
                choice((
                    just(':').padded().ignore_then(app).map(PostOp::Cons),
                    bexpr_op
                        .then(primary.clone())
                        .map(|(op, rhs)| PostOp::BExpr(op, rhs)),
                    primary.repeated().at_least(1).map(PostOp::App),
                ))
                .or_not(),
            )
            .map(|(lhs, post)| match post {
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
                }
                Some(PostOp::App(args)) => args
                    .into_iter()
                    .fold(lhs, |acc, arg| Expr::App(Box::new(acc), Box::new(arg))),
                None => lhs,
            });

        choice((lambda, not_expr, succ, postfix))
    })
}

enum PostOp {
    Cons(Expr),
    BExpr(&'static str, Expr),
    App(Vec<Expr>),
}

fn primary_expr(
    expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
    app: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Expr, Error = Simple<char>> + Clone {
    let nat_zero = text::keyword::<_, _, Simple<char>>("Z")
        .padded()
        .to(Expr::Zero);

    let list_nil = just('[').padded().then(just(']').padded()).to(Expr::Nil);

    let pair = app
        .clone()
        .then_ignore(just(',').padded())
        .then(app.clone())
        .delimited_by(just('(').padded(), just(')').padded())
        .map(|(a, b)| Expr::Pair(Box::new(a), Box::new(b)));

    let list = app
        .separated_by(just(',').padded())
        .at_least(1)
        .delimited_by(just('[').padded(), just(']').padded())
        .map(Expr::List);

    let paren = expr.delimited_by(just('(').padded(), just(')').padded());

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
    app: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
    expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'static,
) -> impl Parser<char, Cases, Error = Simple<char>> + Clone {
    let single_case = app.then_ignore(sym("->")).then(expr);

    single_case
        .separated_by(just('|').padded())
        .at_least(1)
        .try_map(|case_list, span| {
            let mut cases = Cases::new();
            let custom = |m: &'static str| Simple::custom(span.clone(), m);
            for (pattern, body) in case_list {
                match pattern {
                    Expr::Zero | Expr::Nat(0) => {
                        cases.set_type_or_check(CasesType::Nat).map_err(custom)?;
                        cases.set_nat_zero(body).map_err(custom)?;
                    }
                    Expr::Succ(e) => {
                        let var = match *e {
                            Expr::Ident(s) => s,
                            _ => return Err(custom("expected identifier in succ case")),
                        };
                        cases.set_type_or_check(CasesType::Nat).map_err(custom)?;
                        cases.set_nat_succ(var, body).map_err(custom)?;
                    }
                    Expr::Nil => {
                        cases.set_type_or_check(CasesType::List).map_err(custom)?;
                        cases.set_list_nil(body).map_err(custom)?;
                    }
                    Expr::Cons(e1, e2) => {
                        let x = match *e1 {
                            Expr::Ident(s) => s,
                            _ => return Err(custom("expected identifier in cons case")),
                        };
                        let xs = match *e2 {
                            Expr::Ident(s) => s,
                            _ => return Err(custom("expected identifier in cons case")),
                        };
                        cases.set_type_or_check(CasesType::List).map_err(custom)?;
                        cases.set_list_cons(x, xs, body).map_err(custom)?;
                    }
                    _ => return Err(custom("unsupported case pattern")),
                }
            }
            Ok(cases)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast::{CasesNat, CasesNatSucc};

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
                    body: Expr::Ident("x".to_string())
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
                    body: Expr::Ident("x".to_string())
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
                    body: Expr::Ident("x".to_string())
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
                    body: Expr::Exists {
                        var: "n".to_string(),
                        r#type: Type::Ident("Nat".to_string()),
                        body: Box::new(Expr::Equate {
                            lhs: Box::new(Expr::App(
                                Box::new(Expr::Ident("f".to_string())),
                                Box::new(Expr::Ident("n".to_string()))
                            )),
                            rhs: Box::new(Expr::Ident("n".to_string())),
                            body: Box::new(Expr::Ident("n".to_string()))
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
            vec![Decl::Expr(Expr::Exists {
                var: "n".to_string(),
                r#type: Type::Ident("Nat".to_string()),
                body: Box::new(Expr::Equate {
                    lhs: Box::new(Expr::Ident("n".to_string())),
                    rhs: Box::new(Expr::Nat(52)),
                    body: Box::new(Expr::Ident("n".to_string()))
                })
            })]
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
                Decl::FuncType {
                    name: "id".to_string(),
                    r#type: Type::Arrow(
                        Box::new(Type::Ident("Nat".to_string())),
                        Box::new(Type::Ident("Nat".to_string()))
                    )
                },
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Expr::Exists {
                        var: "n".to_string(),
                        r#type: Type::Ident("Nat".to_string()),
                        body: Box::new(Expr::Equate {
                            lhs: Box::new(Expr::Ident("n".to_string())),
                            rhs: Box::new(Expr::Ident("x".to_string())),
                            body: Box::new(Expr::Ident("n".to_string()))
                        })
                    }
                },
                Decl::Expr(Expr::App(
                    Box::new(Expr::Ident("id".to_string())),
                    Box::new(Expr::Nat(5))
                ))
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
                    body: Expr::Ident("x".to_string())
                },
                Decl::Expr(Expr::App(
                    Box::new(Expr::Ident("id".to_string())),
                    Box::new(Expr::Nat(5))
                )),
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
                        Box::new(Type::Ident("a".to_string()))
                    )
                },
                Decl::Func {
                    name: "id".to_string(),
                    args: vec![Arg::Ident("x".to_string())],
                    body: Expr::Ident("x".to_string())
                },
                Decl::Expr(Expr::Choice(vec![
                    Expr::Nat(1),
                    Expr::App(
                        Box::new(Expr::Ident("id".to_string())),
                        Box::new(Expr::Nat(2))
                    ),
                    Expr::Nat(3)
                ]))
            ]
        )
    }

    #[test]
    fn test10() {
        let src = "true.";

        let ast = parse(src).unwrap();

        assert_eq!(ast, vec![Decl::Expr(Expr::Bool(true))]);
    }

    #[test]
    fn test11() {
        let src = "true == false.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Expr(Expr::BExpr(BExpr::Eq(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Bool(false))
            )))]
        );
    }

    #[test]
    fn test12() {
        let src = "if !(1 != 2) then 0 else 1.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Expr(Expr::If {
                cond: Box::new(Expr::BExpr(BExpr::Not(Box::new(Expr::BExpr(BExpr::NEq(
                    Box::new(Expr::Nat(1)),
                    Box::new(Expr::Nat(2))
                )))))),
                then: Box::new(Expr::Nat(0)),
                r#else: Box::new(Expr::Nat(1))
            })]
        );
    }

    #[test]
    fn test13() {
        let src = "exists xs :: [Nat]. xs =:= [1,2,3]. xs.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Expr(Expr::Exists {
                var: "xs".to_string(),
                r#type: Type::List(Box::new(Type::Ident("Nat".to_string()))),
                body: Box::new(Expr::Equate {
                    lhs: Box::new(Expr::Ident("xs".to_string())),
                    rhs: Box::new(Expr::List(vec![Expr::Nat(1), Expr::Nat(2), Expr::Nat(3)])),
                    body: Box::new(Expr::Ident("xs".to_string()))
                })
            })]
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
            vec![Decl::Expr(Expr::Cons(
                Box::new(Expr::Nat(1)),
                Box::new(Expr::Cons(
                    Box::new(Expr::Nat(2)),
                    Box::new(Expr::List(vec![Expr::Nat(3), Expr::Nat(4)]))
                ))
            ))]
        )
    }

    #[test]
    fn test20() {
        let src = "true && (false || true).";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Expr(Expr::BExpr(BExpr::And(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::BExpr(BExpr::Or(
                    Box::new(Expr::Bool(false)),
                    Box::new(Expr::Bool(true))
                )))
            )))]
        )
    }

    #[test]
    fn test21() {
        let src = "f :: Nat * Nat -> Nat";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::FuncType {
                name: "f".to_string(),
                r#type: Type::Arrow(
                    Box::new(Type::Product(
                        Box::new(Type::Ident("Nat".to_string())),
                        Box::new(Type::Ident("Nat".to_string()))
                    )),
                    Box::new(Type::Ident("Nat".to_string()))
                )
            }]
        )
    }

    #[test]
    fn test22() {
        let src = "case n of 0 -> n | S m -> m.";

        let ast = parse(src).unwrap();

        assert_eq!(
            ast,
            vec![Decl::Expr(Expr::Case {
                expr: Box::new(Expr::Ident("n".to_string())),
                cases: Cases {
                    r#type: Some(CasesType::Nat),
                    nat_case: Some(CasesNat {
                        zk: Some(Box::new(Expr::Ident("n".to_string()))),
                        sk: Some(CasesNatSucc {
                            var: "m".to_string(),
                            body: Box::new(Expr::Ident("m".to_string()))
                        })
                    }),
                    list_case: None
                }
            })]
        )
    }

    #[test]
    fn test23() {
        let src = "case p of (x, y) -> x.";

        assert!(parse(src).is_err());
    }

    // A4: malformed case sets are recoverable parse errors, not panics.
    #[test]
    fn duplicate_case_arm_is_a_parse_error() {
        assert!(parse("f :: Nat -> Nat\nf n = case n of Z -> 1 | Z -> 2.\n\nf 0.\n").is_err());
    }

    #[test]
    fn mixed_nat_and_list_case_is_a_parse_error() {
        assert!(parse("f :: Nat -> Nat\nf n = case n of Z -> 1 | [] -> 2.\n\nf 0.\n").is_err());
    }
}
