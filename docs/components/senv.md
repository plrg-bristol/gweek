---
title: senv.rs — suspension environment
tags: [component]
source: src/machine/senv.rs
commit: 6ec7c97
---

# `senv.rs`

`SuspEnv<'a>` (`senv.rs:8-11`) stores [[suspensions-and-forcing|suspensions]] — `let`-bound
computations that have not yet run. It holds an `Rc<Vec<Result<VClosure, CClosure>>>` of entries
plus a `next_pending` cursor. Each entry is `Err(cclos)` while still a pending computation closure
and becomes `Ok(vclos)` once forced to a value. Suspensions are identified by the `SuspId` newtype
([[mterms|mod.rs]]`:23`), a `usize` wrapper distinct from logic variables' `LVar`
([[mterms|mod.rs]]`:21`) — the [[deep-review]] §A5 split.

The `Rc` gives the same copy-on-write backtracking as [[lvar]]: cloning a [[step|machine]] at a
[[nondeterminism|branch]] is cheap, and `Rc::make_mut` deep-copies the entry vector on the first
write of a shared clone (the §P2 cost, shared with the logic store).

## API

- `fresh(cclos) -> SuspId` (`:37-42`) appends a pending entry `Err(cclos)` and returns its
  `SuspId`. Called by [[step|`Bind`]] when a non-strict `let` freezes its right-hand side.
- `lookup(ident) -> Result<VClosure, SuspAt>` (`:44-52`) returns `Ok(vclos)` if the suspension has
  been forced, or `Err(SuspAt)` if it is still pending — the signal [[vclosure|`close_head`]]
  propagates with `?` to trigger a [[step|`reschedule`]].
- `set(ident, val, env)` (`:54-56`) records a forced result, overwriting the entry with
  `Ok(VClosure::mk_clos(val, env))`. Driven by the `Set` stack frame when the suspended
  computation finally returns.
- `next() -> Option<SuspAt>` (`:58-71`) advances `next_pending` past already-forced entries and
  yields the first still-pending suspension, or `None` if all are forced. Used by
  [[step|`Return` on an empty stack]] (`step.rs:155-172`) to drain leftover suspensions at the end
  of a run.

`SuspAt<'a>` (`:14-17`) pairs a `SuspId` with its `CClosure`; `comp()` and `env()` (`:19-27`)
project the computation and environment out of the closure. It is the descriptor a `Set` stack
frame acts on.

Related: [[suspensions-and-forcing]], [[step]], [[vclosure]], [[env]].
