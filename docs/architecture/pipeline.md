---
title: The pipeline
tags: [architecture]
updated: 7972077
---

# The pipeline

A gweek program passes through five stages. The whole chain is wired together twice: once
for the CLI (`main.rs:88-117`) and once for the library/WASM entry (`lib.rs`, helper
`run_with` at `lib.rs:12-67`). Both call the same functions in the same order.

## 1. Parse — `parser/`

`parser::parse(src) -> Result<Vec<Decl>, Vec<Simple<char>>>` turns source text into a
**surface AST**. The parser is built from [chumsky](https://github.com/zesterer/chumsky)
combinators ([[parser]]). Comments (`-- …`) are stripped first (`parse.rs:18-26`); reserved
words are protected (`parse.rs:28-44`). The grammar layers operator precedence — prefix
`S`/`\`/`!`, then postfix cons `:` / boolean ops / application, then statement forms
(`if`/`let`/`exists`/`case`/`=:=`/`<>`).

The AST node families: `Decl` (type signature, function, or bare statement), `Stmt`
(control + constraints), `Expr` (data and application), `Type`, `BExpr`, `Arg`. See
[[parser]] for the full node catalogue.

## 2. Type-check — `type_check.rs`

`type_check::type_check(&ast) -> Result<(), Vec<TypeError>>` runs a **two-pass bidirectional**
checker ([[type-checker]], [[type-system]]). Pass 1 collects function signatures
(`type_check.rs:134-138`) so functions can refer to each other; pass 2 checks each body
against its signature and each bare statement (`:141-158`). On any error the CLI prints a
pretty `ariadne` report and exits (`main.rs:120-159`).

> **Known issue.** A few constructs type-check but cannot be lowered, so the failure surfaces
> later as a panic instead of a clean type error: boolean expressions / `if` ([[deep-review]] §B2),
> `Int` ([[deep-review]] §B11), pair patterns ([[deep-review]] §B10). The checker and the
> [[translate|translator]] disagree on the accepted alphabet.

## 3. Translate — `machine/translate.rs`

`translate(arena, ast) -> (&MComputation, Vec<&MValue>)` lowers the checked AST into a
[[cbpv|CBPV]] term plus the list of top-level function values ([[translate]]). Variables
become [[de-bruijn|de Bruijn indices]]; the surface CBV reading is made explicit as CBPV
sequencing (`Bind`/`Return`/`Force`/`Thunk`). Top-level functions are topologically sorted
by reference first (`translate.rs:94-189`) so each name is in scope before its uses.

## 4. Optimize (optional) — `machine/optimize.rs`

With `-o`, `optimize`/`optimize_val` run a peephole pass over the CBPV term ([[optimizer]]).
It is built on binder-aware term traversals (shift / subst / swap). The optimizer is
verified to preserve the solution multiset on every terminating example ([[deep-review]] §5).

## 5. Evaluate — `machine/eval.rs`

The chosen [[search-strategies|strategy]] (`--bfs` default, `--dfs`, `--iddfs`, `--fair`)
drives the abstract machine ([[eval]], [[step]]). Each strategy repeatedly runs a machine
to its next branch point (`step.rs:73`, `run_to_branch`), collects the resulting machine
states, records any that are `Done` as [[unify|solutions]], and schedules the rest. Output
is produced by [[vclosure|closing]] the final value to a ground term (`eval.rs:293`).

```
   parse ──▶ type_check ──▶ translate ──▶ [optimize] ──▶ eval
 parser/     type_check.rs   translate.rs   optimize.rs    eval.rs + step.rs
```

## Entry points

- **CLI** (`main.rs`): flag parsing (`main.rs:28-72`) builds a [[config|`Config`]],
  `config::init` stores it, then the pipeline runs and `eval` prints solutions. See [[cli]].
- **Library / WASM** (`lib.rs`): `run_gweek` streams solutions to a JS callback
  (`lib.rs:102`); `run_gweek_batch` returns them as one string (`lib.rs:130`). Both are
  `#[cfg(target_arch = "wasm32")]`. See [[main-and-lib]].
