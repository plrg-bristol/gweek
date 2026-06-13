---
title: parser/ — the chumsky frontend
tags: [component, stub]
source: src/parser/parse.rs
updated: 7972077
---

# `parser/` *(stub — expand on demand)*

Turns source text into the surface AST using [chumsky](https://github.com/zesterer/chumsky)
combinators. `parser::parse(src) -> Result<Vec<Decl>, Vec<Simple<char>>>` is the entry point;
the grammar lives in `parse.rs` (781 lines), the AST node types in sibling files.

**AST node families** (each in its own file under `src/parser/`):

- `Decl` (`decl.rs`) — `FuncType`, `Func { name, args, body }`, `Stmt`.
- `Stmt` (`stmt.rs`) — `If`, `Let`, `Exists`, `Equate`, `Choice`, `Case`, `Fail`, `Expr`.
- `Expr` (`expr.rs`) — naturals, lists, `Bool`, `Ident`, `App`, `Lambda`, `Pair`, `BExpr`, `Stmt`.
- `Type` (`type.rs`) — `Arrow`, `Ident`, `List`, `Product`, `Any`.
- `BExpr` (`bexpr.rs`), `Arg` (`arg.rs`), `Cases` (`cases.rs`).

**Precedence layering** (`parse.rs:218-332`): prefix `S` / `\` / `!`, then postfix cons `:` /
boolean ops / left-assoc application, then the statement forms. Comments are stripped first
(`:18-26`); reserved words are protected (`:28-44`).

> **Known issues.** Type operators `*` and `->` share precedence ([[deep-review]] §B6,
> `parse.rs:57-83`); a numeric literal in a `case` pattern panics (`:377`, §B12); tuple
> `case` patterns panic the parser (§B10).

Related: [[pipeline]], [[type-checker]], [[translate]], [[grammar]], [[type-system]].
