---
title: senv.rs — suspension environment
tags: [component, stub]
source: src/machine/senv.rs
updated: 7972077
---

# `senv.rs` *(stub — expand on demand)*

`SuspEnv<'a>` (`senv.rs:8`) stores [[suspensions-and-forcing|suspensions]] — `let`-bound
computations that have not yet run. Each entry is a `Result<VClosure, CClosure>`: `Ok` once
forced to a value, `Err` while still a pending computation closure. A `next_pending` cursor
tracks the first unresolved entry.

**API:** `fresh(cclos) -> Ident` (`:37`) registers a pending suspension; `lookup(ident)`
(`:44`) returns `Ok(vclos)` if forced or `Err(SuspAt)` if still pending; `set(ident, val, env)`
(`:54`) records a forced result; `next()` (`:58`) yields the next unresolved suspension, used
by [[step|`Return` on an empty stack]] to drain leftovers at the end of a run. `SuspAt`
(`:14`) pairs an `Ident` with its computation closure — the descriptor a `Set` stack frame
acts on.

Related: [[suspensions-and-forcing]], [[step]], [[vclosure]], [[env]].
