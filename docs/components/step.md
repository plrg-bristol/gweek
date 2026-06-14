---
title: step.rs — the transition function
tags: [component, machine]
source: src/machine/step.rs
commit: 6ec7c97
---

# `step.rs`

The heart of the interpreter: one **machine state** and the **transition function** that
advances it. A [[search-strategies|scheduler]] in [[eval]] runs many of these.

## The `Machine` state (`step.rs:73-81`)

```rust
pub struct Machine<'a> {
    pub arena: &'a Bump,        // where everything is allocated
    pub cclos: CClosure<'a>,    // (computation, env) currently running — see [[cbpv]]
    pub stack: Stack<'a>,       // continuation frames
    pub lenv: LogicEnv<'a>,     // logic-variable bindings — see [[lvar]]
    pub senv: SuspEnv<'a>,      // suspensions — see [[senv]]
    pub done: bool,
}
```

The **stack** is a persistent arena-backed cons-list (`Stack`, `step.rs:52-55`), so
`Clone`/`Copy` is a single pointer copy — essential for cheap branching. Its frames
(`StkFrame`, `step.rs:35-39`):

- `Value(v)` — an argument waiting for a `Lambda` to consume (`App` pushes it).
- `To(cont)` — a continuation waiting for a `Return`ed value (strict `Bind`).
- `Set(SuspId, cont)` — "force this [[senv|suspension]], store the result at the `SuspId`, then
  resume `cont`." This frame is how forcing is threaded through the machine.

## `run_to_branch` (`step.rs:136-149`)

The scheduler never calls `step` directly; it calls `run_to_branch(cfg, deadline)`, which loops
`step` tight and returns a `RunResult` (`step.rs:20-25`): `Yield(StepResult)` at a **branch**
(`Choice`, logic-var split) or **completion**, or `TimedOut`. Running determinism in a tight
inner loop is the machine's main throughput lever.

> The deadline is polled **inside** this loop through a `Clock` (`step.rs:111-129`): the loop
> calls `clock.expired()` each iteration, but `Clock` only reads `Instant::now()` every
> `POLL_INTERVAL = 1024` ticks (`:117`, `:125-128`). A deterministic divergent loop
> (`loop n = loop (S n)`) therefore honours `--timeout` instead of spinning forever —
> [[deep-review]] §B9, fixed. `Clock` is `pub(super)` and shared: the same helper drives the
> scheduler loops in [[eval]] — its §C6 follow-up.

## `step` (`step.rs:151-623`)

`step(self, cfg: &Config)` matches on the head computation; the [[config|`Config`]] is threaded
explicitly (no thread-local — §A2). Each arm reads/closes some values, builds the successor
`Machine`, and returns `Step::{Continue, Done, Branch, Fail}` (`:27-32`).

**Sequencing.**
- `Return(v)` (`:155`): if the stack is empty, drain the next [[senv|suspension]] or finish
  (`Done`); otherwise pop a frame — `To` extends the env and runs the continuation, `Set`
  stores `v` into the suspension and resumes.
- `Bind { comp, cont }` (`:201`): if `comp` is already `Return(v)`, bind eagerly; else under
  `cfg.strict` push a `To` frame and run `comp`; else **suspend** `comp` and bind a `Susp` for
  the continuation — see [[suspensions-and-forcing]].
- `Force(v)` (`:239`): [[vclosure|head-close]] `v` to a `Thunk` and run it; a `Susp` triggers a
  reschedule (`:255`).

**Functions.** `App` (`:278`) pushes the argument as a `Value` frame and runs the operator;
`Lambda` (`:259`) pops that `Value` frame, binds it, and runs the body.

**Functional-logic.**
- `Choice` (`:290`) → [[nondeterminism|branch]]; empty choice is `Fail`. Clones `lenv`/`senv`
  for all but the last alternative.
- `Exists` (`:331`) allocates a fresh [[logic-variables|logic variable]] and binds it.
- `Equate` (`:345`) runs [[unify|unification]] (passing `cfg`); `Ok` continues into the body,
  a suspension reschedules, failure prunes.

**Eliminators** (`Ifz` `:362`, `Match` `:448`, `Case` `:527`). Each [[vclosure|head-closes]]
its scrutinee and then:
- on a concrete constructor, takes that branch, binding any payload into the env;
- on `Err(SuspAt)`, reschedules via `reschedule` to force the operand;
- on an **unbound logic variable**, emits `Step::Branch` guessing each constructor with fresh
  sub-variables (the [[nondeterminism|case-split]] mechanism; `Ifz` `:400-443`, `Match`
  `:476-521`, `Case` `:556-604`). `Match`/`Case` read the variable's element/branch types from
  `lenv.get_type`.

**Recursion.** `Rec { body }` (`:610`) thunks itself and binds that thunk at index 0, so the
body can call itself by `Force`-ing variable 0. This is how [[translate|translated functions]]
loop.

> **Cleanliness.** The copy-pasted suspension-reschedule block is now a single `reschedule`
> helper (`:87-105`), called from Force/Equate/Ifz/Match/Case ([[deep-review]] §C2, fixed). The
> per-arm `Machine { … }` rebuilds (§C1) largely remain inline. A handful of `panic!`/
> `unreachable!` sites remain (`:251`, `:272`, `:398`, `:474`, …) — these are now machine
> invariants unreachable for well-typed programs (the [[type-checker]] rejects the inputs that
> used to reach them), the remainder of [[deep-review]] §A4.

Related: [[cbpv]], [[eval]], [[vclosure]], [[unify]], [[senv]], [[lvar]], [[env]], [[config]].
