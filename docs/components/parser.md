---
title: parser/ — the chumsky frontend
tags: [component]
source: src/parser/parse.rs
commit: 6ec7c97
---

# `parser/`

Turns source text into the surface AST using [chumsky](https://github.com/zesterer/chumsky)
combinators. `parser::parse(src) -> Result<Vec<Decl>, Vec<Simple<char>>>` (`parse.rs:13`) is the
entry point; the grammar combinators live in `parse.rs`, while the AST node types are defined in
sibling files re-exported through `mod.rs` (`parse` itself is private; only `parse` is public).

## AST node families

Each family lives in its own module under `src/parser/`:

- `Decl` (`decl.rs:5`) — `FuncType { name, type }`, `Func { name, args, body }`, `Stmt`.
- `Stmt` (`stmt.rs:6`) — `If`, `Let`, `Exists`, `Equate`, `Choice`, `Case`, `Fail`, `Expr`.
- `Expr` (`expr.rs:4`) — `Zero`, `Succ`, `Nil`, `Cons`, `App`, `BExpr`, `List`, `Lambda`,
  `Ident`, `Nat`, `Bool`, `Pair`, `Stmt`.
- `Type` (`type.rs:2`) — `Arrow`, `Ident`, `List`, `Product`, `Any`.
- `BExpr` (`bexpr.rs:5`) — `Eq`, `NEq`, `And`, `Or`, `Not`.
- `Arg` (`arg.rs:3`) — `Ident`, `Pair` (function/lambda argument patterns).
- `Cases` (`cases.rs:4`) — the accumulator a `case` arm-list folds into.

## Pipeline of combinators

`parse` first calls `strip_comments` (`parse.rs:18`), which truncates each line at the first
`--`. The grammar is then a stack of `recursive` parsers:

- `program` (`:105`) — `declaration().repeated()` followed by `end()`.
- `declaration` (`:109`) — a `choice` of `func_type` (`name :: type`), `func`
  (`name arg* = stmt .`), and `bare_stmt` (`stmt .`).
- `statement_parser` (`:133`) — `if`, `let`, `exists`, `case`, `fail`, and the catch-all
  `expr_stmt` (`:181`). The latter parses an expression, then optionally a `=:=`/`<>`
  continuation (`:182-204`), folding into `Equate` or `Choice`; bare expressions become
  `Stmt::Expr`.
- `expression` (`:223`) — prefix forms `\` (lambda, `:229`), `!` (`BExpr::Not`, `:235`), and
  `S` (successor, `:239`); then `postfix` (`:251`) layers cons `:` (right-assoc, via
  `expr`), the binary boolean ops `== != && ||` (`:244-249`), and left-associative application
  (`primary.repeated().at_least(1)`, folded at `:275-279`).
- `primary_expr` (`:299`) — the atoms: `Z`, `[]`, pairs `(e, e)`, list literals `[e, …]`,
  booleans, numbers, identifiers, and a parenthesised statement `( stmt )` wrapped as
  `Expr::Stmt`.

Reserved words (`if then else let in exists case of true false fail`) are rejected by `ident`
(`:36-44`), so they cannot be used as variable names.

## Types

`type_parser` (`:57`) is a three-layer `recursive` grammar:

- `primary_type` (`:59`) — `[ t ]` lists, parenthesised types, and identifiers.
- `product` (`:68`) — `primary_type` separated by `*`, folded **right**-associatively
  (`:71-77`), so `A * B * C` is `Product(A, Product(B, C))`.
- the arrow layer (`:79-86`) — a product optionally followed by `-> ty`, building
  `Type::Arrow`.

Because the arrow layer sits *above* `product`, `*` binds tighter than `->`: `Nat * Nat -> Nat`
parses as `(Nat * Nat) -> Nat` (test `test21`, `:789-808`; was [[deep-review]] §B6, now fixed).

## Case patterns

`cases_parser` (`:339`) parses `pattern -> body` arms separated by `|`, then folds them into a
`Cases` with a `try_map` (`:350-387`). Each arm's pattern is normalised by
`Expr::strip_parentheses` (`expr.rs:21`) and matched structurally: `Z`/`0` and `S x` set the
`Nat` shape, `[]` and `x:xs` set the `List` shape. Anything else — a numeric literal other than
zero, a pair pattern, a complex expression — falls through to the catch-all and becomes a
recoverable parse **error** (`Simple::custom`, `:383`), never a panic ([[deep-review]] §B10,
§B12). The accumulator methods on `Cases` (`cases.rs:61-96`) also reject duplicate or
type-mixed arms ("duplicate zero case", "case mixes Nat and list patterns"). Tests: a pair
`case` pattern (`test23`, `:835`), a duplicate arm, and a mixed Nat/list `case` (`:842-851`)
all assert `is_err()`.

`strip_parentheses` (`expr.rs:21-34`) is a `while let` that unwraps nested `Expr::Stmt(Stmt::Expr(…))`
layers down to the inner expression. A parenthesised *non*-`Stmt::Expr` (e.g. `(let … in …)`
used as a pattern) hits the catch-all arm and returns the wrapper unchanged. Two regression
tests guard this (`expr.rs:44-62`): `strip_parentheses_terminates_on_non_expr_stmt` pins that
it terminates rather than rewrapping and looping forever, and
`strip_parentheses_unwraps_nested_expr_stmts` pins that `((e))` strips to `e`.

Related: [[pipeline]], [[type-checker]], [[translate]], [[grammar]], [[type-system]].
