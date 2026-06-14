---
title: Wiki log
tags: [meta]
---

# Log

Append-only record of wiki activity. Each entry starts with `## [date] kind | summary`
so the log is greppable: `grep "^## \[" log.md | tail -5`.

## [2026-06-13] bootstrap | initial spine

Created the wiki against commit `7972077` (spine-first scope).

- Schema [[AGENTS]], home [[index]], this log.
- Architecture: [[overview]], [[pipeline]].
- Concepts: [[cbpv]], [[logic-variables]], [[unification]], [[nondeterminism]],
  [[de-bruijn]], [[type-system]]; folded existing `notes.md` → [[suspensions-and-forcing]]
  and `search-strategies.md` → [[search-strategies]].
- Full component pages: [[mterms]], [[step]], [[eval]], [[unify]], [[translate]].
- Stubs (one paragraph + `source:` + links): [[parser]], [[type-checker]], [[optimizer]],
  [[lvar]], [[union-find]], [[senv]], [[env]], [[vclosure]], [[value-type]], [[config]],
  [[main-and-lib]].
- Reference: [[cli]], [[examples]]; [[grammar]] stub.
- Moved the standing audit to [[deep-review]]. Noted **B1 is fixed** as of `0f34f45`
  (union-find now canonicalizes through `Root`).

Built on branch `docs/llm-wiki` in a worktree, because a refactor was in flight on `main`.
The component pages' `file:line` anchors are pinned to `7972077` and will need a **sync**
pass once that refactor lands.

## [2026-06-14] sync | re-pin to d83302b after the deep-review fixes landed

The in-flight refactor merged into `main` (21 commits) implemented **essentially the whole**
[[deep-review]]: every correctness bug **B1–B13**, architecture **A1/A2/A4/A5**, and cleanups
**C2–C7**. Re-read all 18 changed source modules and re-synced the wiki accordingly:

- Retired the "known issue" callouts that are now fixed; reframed them as "was §X, fixed":
  residual free variables now reported ([[logic-variables]], [[eval]] · B7); IDDFS counts by
  depth frontier, no string dedup ([[eval]], [[search-strategies]] · B8); `--timeout` honoured
  inside [[step|`run_to_branch`]] (B9); boolean exprs / mutual recursion / pair args lower
  ([[translate]] · B2/B3/B10); real polymorphism + lambda-arg checking + `Int` rejection
  ([[type-checker]], [[type-system]] · B4/B5/B11); `*`/`->` precedence and recoverable case
  patterns ([[parser]], [[grammar]] · B6/B12).
- Structural rewrites: thread-local `Config` gone, now threaded `&Config` ([[config]], [[eval]],
  [[step]], [[unify]] · A2); one generic optimizer traversal ([[optimizer]], [[de-bruijn]] · A1);
  `Ident` → `LVar`/`SuspId` ([[lvar]], [[senv]], [[union-find]] · A5); `close` returns
  `Closed`/`CyclicTerm`, depth-bounded ([[vclosure]] · B13).
- Fixed `file:line` anchors throughout and bumped every component/reference page's `commit:`
  to `d83302b` (renamed from `updated:`, which Quartz reserves as a date alias). Pure-concept
  pages carry no `source:` pin by design.
- **Still open** (documented, not fixed): [[deep-review]] §P2 (COW backtracking), §P3 (arena
  growth), §A3 (`MValue::Zero`). Verified `just wiki-build` still succeeds under bun.

## [2026-06-14] sync | re-pin to 6ec7c97 (Clock follow-up + clippy hygiene)

Two code commits landed after the last sync (`d83302b`): `bd17a3f` moved the deadline-polling
`Clock` out of [[eval]] into [[step]] (now `pub(super)`, used by both `run_to_branch` and the
four schedulers — the §C6 follow-up), and `6ec7c97` cleared the clippy backlog (deref removals,
nested-`if` → `&&`, a `Default` for `Cases`, and two new `Expr::strip_parentheses` regression
tests). Re-read every changed module and re-verified **every `file:line` anchor** across all
component, concept, architecture and reference pages — most had drifted purely from line shifts
(`step.rs` +≈19 from the new `Clock` struct, `eval.rs` −≈19, `unify.rs` −≈4).

- **Clock move** rewritten on [[step]], [[eval]], [[search-strategies]], [[pipeline]]: the
  poller is now one `Clock` type in `step.rs`, not a local `DEADLINE_POLL_INTERVAL` per loop.
- **De-stubbed** into full pages: [[optimizer]], [[parser]], [[type-checker]], [[grammar]],
  [[lvar]], [[union-find]], [[senv]], [[env]], [[vclosure]], and [[config]]; [[value-type]] kept
  concise (39-line module). [[index]] reorganised — the "stubs — expand on demand" bucket is
  gone; components now group as machine-core / frontend & types / runtime support / entry points.
- **Re-verified [[deep-review]].** Newly confirmed fixed since the last sync: **P1**
  (`[profile.release]` `lto`/`codegen-units` tuning is in `Cargo.toml`). Corrected a phantom —
  there is **no `Int` type** in the code; **B11**'s panic path is an unknown-type-identifier
  error in `translate_vtype` ([[translate]]). Still open: **P2** (COW backtracking), **P3**
  (arena growth), **A3** (`MValue::Zero`), and **C1** (the `step.rs` `Machine{…}` rebuild
  boilerplate, deliberately left inline — 29 sites remain). **P2** callouts kept on
  [[lvar]]/[[union-find]]/[[logic-variables]].
- Bumped every component/reference page's `commit:` to `6ec7c97`; pure-concept pages carry no
  pin. Fixed the LOC figure in [[index]] (~5,500 → ~6,400; `src/` is 6,397 lines).

Six architecture/reference pages were committed separately (`496bc1c`); the remaining pages plus
these meta updates land together. The in-flight uncommitted `parse.rs` clippy edit (a point-free
`.map(PostOp::Cons)`) is trivial and shifts no anchors.
