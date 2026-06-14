---
title: Grammar
tags: [reference]
source: src/parser/parse.rs
commit: 6ec7c97
---

# Grammar

The surface syntax accepted by the [[parser]]. Each production below is grounded in a chumsky
combinator in `parse.rs`; the AST node types they build are listed in [[parser]]. Comments run
from `--` to end of line and are stripped before parsing (`strip_comments`, `parse.rs:18`).

## Declarations and statements

```
program     ::= declaration* EOF                          -- parse.rs:105
declaration ::= ident "::" type                           -- function signature (:109)
              | ident arg* "=" stmt "."                   -- function definition
              | stmt "."                                  -- bare (top-level query)

stmt        ::= "if" stmt "then" stmt "else" stmt         -- statement_parser, :133
              | "let" ident "=" stmt "in" stmt
              | "exists" ident "::" type "." stmt
              | "case" expr "of" cases
              | "fail"
              | expr "=:=" expr "." stmt                  -- unification constraint
              | expr ("<>" expr)+                          -- choice (nondeterminism)
              | expr                                       -- bare expression
```

The `=:=` and `<>` forms are an optional continuation on a leading expression (`:181-210`); an
expression with neither is just `Stmt::Expr`.

## Expressions

```
expr        ::= "\" arg "." stmt                          -- lambda (expression, :223)
              | "!" primary                                -- boolean negation
              | "S" expr                                   -- successor
              | postfix
postfix     ::= primary (":" expr)?                        -- cons, right-assoc (:251)
              | primary bop primary                        -- binary boolean op
              | primary primary+                           -- application, left-assoc
              | primary
bop         ::= "==" | "!=" | "&&" | "||"                  -- :244-249
primary     ::= "Z" | nat | "[]" | "[" expr ("," expr)* "]"  -- primary_expr, :299
              | "(" expr "," expr ")"                       -- pair
              | "true" | "false" | ident | "(" stmt ")"
```

Application binds loosest among the postfix forms; cons `:` is right-associative (it recurses
through the full `expr`). A parenthesised statement `( stmt )` is wrapped as `Expr::Stmt`, which
is how arbitrary statements nest inside expressions.

## Types

```
type        ::= product ("->" type)?                       -- arrow, right-assoc, loosest (:79)
product     ::= primary_type ("*" primary_type)*           -- product, right-assoc (:68)
primary_type ::= "[" type "]" | ident | "(" type ")"       -- :59
```

The arrow layer sits above the product layer, so `*` binds tighter than `->`:
`A * B -> C` parses as `(A * B) -> C` (test `test21`, `parse.rs:789-808`; was
[[deep-review]] §B6, now correct). Both `*` and `->` fold right-associatively
(`A * B * C` is `A * (B * C)`, test `test16`).

## Reserved words

`if then else let in exists case of true false fail` are rejected by `ident` (`:36-44`) and
cannot name variables.

## Case patterns

```
cases       ::= (pattern "->" stmt) ("|" (pattern "->" stmt))*   -- cases_parser, :339
pattern     ::= "Z" | "0"            -- nat zero
              | "S" ident            -- nat successor
              | "[]"                 -- list nil
              | ident ":" ident      -- list cons
```

`cases_parser` (`:339`) accepts only these four pattern shapes, sorted into a `Nat` or `List`
[[parser|`Cases`]] accumulator. Every other pattern — a numeric literal other than `Z`/`0`, a
pair `(x, y)`, a deeper expression — is a recoverable parse **error**, not a panic
([[deep-review]] §B10, §B12). Duplicate arms ("duplicate zero case") and mixing Nat with list
patterns ("case mixes Nat and list patterns") are likewise rejected (`cases.rs:61-96`). The
pattern is first normalised by `Expr::strip_parentheses` (`expr.rs:21`), whose termination on a
parenthesised non-expression statement is guarded by regression tests (`expr.rs:44-62`).

Related: [[parser]], [[type-system]], [[pipeline]].
