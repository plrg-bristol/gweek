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
