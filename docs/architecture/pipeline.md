---
title: The pipeline
tags: [architecture]
commit: 6ec7c97
---

# The pipeline

A gweek program passes through five stages. The whole chain is wired together twice: once
for the CLI (`main.rs:88-117`) and once for the library/WASM entry (`lib.rs`, helper
`run_with` at `lib.rs:14-69`). Both call the same functions in the same order.

## 1. Parse — `parser/`

`parser::parse(src) -> Result<Vec<Decl>, Vec<Simple<char>>>` turns source text into a
**surface AST**. The parser is built from [chumsky](https://github.com/zesterer/chumsky)
combinators ([[parser]]). Comments (`-- …`) are stripped first; reserved words are protected.
The grammar layers operator precedence — prefix `S`/`\`/`!`, then postfix cons `:` / boolean
ops / application, then statement forms (`if`/`let`/`exists`/`case`/`=:=`/`<>`).

The AST node families: `Decl` (type signature, function, or bare statement), `Stmt`
(control + constraints), `Expr` (data and application), `Type`, `BExpr`, `Arg`. See
[[parser]] for the full node catalogue.

## 2. Type-check — `type_check.rs`

`type_check::type_check(&ast) -> Result<(), Vec<TypeError>>` runs a **two-pass bidirectional**
checker with HM-style instantiation ([[type-checker]], [[type-system]]). Pass 1 collects
function signatures (`type_check.rs:259-263`) so functions can refer to each other; pass 2
checks each body against its signature and each bare statement (`:266-282`). On any error the
CLI prints a pretty `ariadne` report and exits (`main.rs:120-159`). The checker now rejects
the constructs that used to slip through and panic in translation — `Int`, boolean
expressions, ill-typed lambda arguments ([[deep-review]] §B4–B6, §B11).

## 3. Translate — `machine/translate.rs`

`translate(arena, ast) -> (&MComputation, Vec<&MValue>)` lowers the checked AST into a
[[cbpv|CBPV]] term plus the list of top-level function values ([[translate]]). Variables
become [[de-bruijn|de Bruijn indices]]; the surface CBV reading is made explicit as CBPV
sequencing (`Bind`/`Return`/`Force`/`Thunk`). Top-level functions are grouped into
strongly-connected components (Tarjan, `translate.rs:140`) and ordered by dependency;
mutually-recursive groups are lowered to a single selector-dispatched fixpoint (§B3).

## 4. Optimize (optional) — `machine/optimize.rs`

With `-o`, `optimize`/`optimize_val` run a peephole pass over the CBPV term ([[optimizer]]),
built on a single generic binder-aware traversal (`map_comp`/`map_val`, §A1). The optimizer is
verified to preserve the solution multiset on every terminating example ([[deep-review]] §5).

## 5. Evaluate — `machine/eval.rs`

The chosen [[search-strategies|strategy]] (`--bfs` default, `--dfs`, `--iddfs`, `--fair`)
drives the abstract machine ([[eval]], [[step]]). Each strategy repeatedly runs a machine to
its next branch point (`step.rs:136`, `run_to_branch`), collects the resulting machine states,
records any that are solutions via `record_solution` (`eval.rs:133`), and schedules the rest.
Output is produced by [[vclosure|closing]] the final value to a `Closed` answer term
(`output`/`close`, `eval.rs:303`). The `--timeout` deadline is polled through one shared
`Clock` type (`step.rs:111`): both `run_to_branch` and the four scheduler loops in `eval`
construct a `Clock::new(deadline)` and tick it, so `Instant::now()` is read only once every
`POLL_INTERVAL` (1024) ticks rather than on every step. `Clock` lives in `step.rs` (moved
there so the single hot-loop idiom is not duplicated between the step loop and the schedulers).

```
   parse ──▶ type_check ──▶ translate ──▶ [optimize] ──▶ eval
 parser/     type_check.rs   translate.rs   optimize.rs    eval.rs + step.rs
```

## Entry points

- **CLI** (`main.rs`): flag parsing (`main.rs:27-72`) **constructs** a [[config|`Config`]]
  (`:79-86`) that is threaded explicitly through the pipeline (no thread-local — §A2), then
  `eval` prints solutions. See [[cli]].
- **Library / WASM** (`lib.rs`): `run_gweek` streams solutions to a JS callback
  (`lib.rs:104`); `run_gweek_batch` returns them as one string (`lib.rs:132`). Both are
  `#[cfg(target_arch = "wasm32")]`. See [[main-and-lib]].
