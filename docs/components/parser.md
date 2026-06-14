---
title: parser/ — the chumsky frontend
tags: [component, stub]
source: src/parser/parse.rs
commit: d83302b
---

# `parser/` *(stub — expand on demand)*

Turns source text into the surface AST using [chumsky](https://github.com/zesterer/chumsky)
combinators. `parser::parse(src) -> Result<Vec<Decl>, Vec<Simple<char>>>` (`parse.rs:13`) is
the entry point; the grammar lives in `parse.rs`, the AST node types in sibling files.

**AST node families** (each in its own file under `src/parser/`):

- `Decl` (`decl.rs`) — `FuncType`, `Func { name, args, body }`, `Stmt`.
- `Stmt` (`stmt.rs`) — `If`, `Let`, `Exists`, `Equate`, `Choice`, `Case`, `Fail`, `Expr`.
- `Expr` (`expr.rs`) — naturals, lists, `Bool`, `Ident`, `App`, `Lambda`, `Pair`, `BExpr`, `Stmt`.
- `Type` (`type.rs`) — `Arrow`, `Ident`, `List`, `Product`, `Any`.
- `BExpr` (`bexpr.rs`), `Arg` (`arg.rs`), `Cases` (`cases.rs`).

**Precedence layering** (`parse.rs:223-336`): prefix `S` / `\` / `!`, then postfix cons `:` /
boolean ops / left-assoc application, then the statement forms (`statement_parser` `:133`).
Comments are stripped first (`strip_comments` `:18`); reserved words are protected.

**Findings now resolved** ([[deep-review]]):

- **B6** — the type grammar (`type_parser` `:57`) is layered: product `*` (`:68-77`) binds
  tighter than arrow `->` (`:79-86`, right-associative), so `A * B -> C` parses correctly.
- **B12/B10** — `cases_parser` (`:339`) validates patterns structurally (`:350-387`) and emits
  recoverable parse **errors** instead of panicking; numeric `case` patterns and tuple `case`
  patterns are clean errors now (`cases.rs` tracks per-arm structure).

Related: [[pipeline]], [[type-checker]], [[translate]], [[grammar]], [[type-system]].
