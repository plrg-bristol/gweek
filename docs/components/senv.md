---
title: senv.rs — suspension environment
tags: [component, stub]
source: src/machine/senv.rs
commit: d83302b
---

# `senv.rs` *(stub — expand on demand)*

`SuspEnv<'a>` (`senv.rs:8-11`) stores [[suspensions-and-forcing|suspensions]] — `let`-bound
computations that have not yet run. Each entry is a `Result<VClosure, CClosure>`: `Ok` once
forced to a value, `Err` while still a pending computation closure. A `next_pending` cursor
tracks the first unresolved entry. Suspensions are identified by the `SuspId` newtype
([[mterms|mod.rs]]`:23`), distinct from logic variables' `LVar` (the [[deep-review]] §A5 split).

**API:** `fresh(cclos) -> SuspId` (`:37`) registers a pending suspension; `lookup(ident)`
(`:44`) returns `Ok(vclos)` if forced or `Err(SuspAt)` if still pending; `set(ident, val, env)`
(`:54`) records a forced result; `next()` (`:58`) yields the next unresolved suspension, used
by [[step|`Return` on an empty stack]] to drain leftovers at the end of a run. `SuspAt`
(`:14-17`) pairs a `SuspId` with its computation closure — the descriptor a `Set` stack frame
acts on.

Related: [[suspensions-and-forcing]], [[step]], [[vclosure]], [[env]].
