---
title: step.rs — the transition function
tags: [component, machine]
source: src/machine/step.rs
updated: 7972077
---

# `step.rs`

The heart of the interpreter: one **machine state** and the **transition function** that
advances it. A [[search-strategies|scheduler]] in [[eval]] runs many of these.

## The `Machine` state (`step.rs:60-68`)

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

The **stack** is a persistent arena-backed cons-list (`step.rs:42`), so `Clone`/`Copy` is a
single pointer copy — essential for cheap branching. Its frames (`StkFrame`, `step.rs:22`):

- `Value(v)` — an argument waiting for a `Lambda` to consume (`App` pushes it).
- `To(cont)` — a continuation waiting for a `Return`ed value (strict `Bind`).
- `Set(ident, cont)` — "force this [[senv|suspension]], store the result at `ident`, then
  resume `cont`." This frame is how forcing is threaded through the machine.

## `run_to_branch` (`step.rs:73-82`)

The scheduler never calls `step` directly; it calls `run_to_branch`, which loops `step` tight,
returning a `SmallVec<[Machine; 2]>` only at a **branch** (`Choice`, logic-var split) or
**completion**, and an empty vec on `Fail`. Running determinism in a tight inner loop is the
machine's main throughput lever.

> **Known issue.** Because `run_to_branch` only yields at branch points, a *deterministic*
> divergent loop (`loop n = loop (S n)`) never returns to the scheduler, so the `--timeout`
> (checked between calls in [[eval]]) never fires and the arena grows without bound
> ([[deep-review]] §B9). The fix is a deadline check *inside* this loop.

## `step` (`step.rs:84-606`)

`step` destructures the machine and matches on the head computation. The shape of every arm:
read/close some values, build the successor `Machine`, return `Step::{Continue, Done, Branch, Fail}`.

**Sequencing.**
- `Return(v)` (`:88`): if the stack is empty, drain the next [[senv|suspension]] (`:91`) or
  finish (`Done`, `:103`); otherwise pop a frame — `To` extends the env and runs the
  continuation (`:108`), `Set` stores `v` into the suspension and resumes (`:119`).
- `Bind { comp, cont }` (`:134`): if `comp` is already a `Return(v)`, bind eagerly (`:135`);
  else under `--strict` push a `To` frame and run `comp` (`:146`); else **suspend** `comp` and
  bind a `Susp` for the continuation (`:157`) — see [[suspensions-and-forcing]].
- `Force(v)` (`:172`): [[vclosure|head-close]] `v` to a `Thunk` and run it; a `Susp` triggers
  a `Set`-frame reschedule (`:188`).

**Functions.** `App` pushes the argument as a `Value` frame and runs the operator (`:221`);
`Lambda` pops that `Value` frame, binds it, and runs the body (`:202`).

**Functional-logic.**
- `Choice` (`:233`) → [[nondeterminism|branch]]; empty choice is `Fail`. Clones `lenv`/`senv`
  for all but the last alternative (`:248-271`).
- `Exists` (`:274`) allocates a fresh [[logic-variables|logic variable]] and binds it.
- `Equate` (`:288`) runs [[unify|unification]]; `Ok` continues into the body, a suspension
  reschedules (`:300`), failure prunes (`:311`).

**Eliminators** (`Ifz` `:315`, `Match` `:411`, `Case` `:500`). Each [[vclosure|head-closes]]
its scrutinee and then:
- on a concrete constructor, takes that branch, binding any payload into the env;
- on `Err(SuspAt)`, reschedules via a `Set` frame to force the operand;
- on an **unbound logic variable**, emits `Step::Branch` guessing each constructor with fresh
  sub-variables (the [[nondeterminism|case-split]] mechanism). `Match`/`Case` read the
  variable's element/branch types from `lenv.get_type` (`:450`, `:540`).

**Recursion.** `Rec { body }` (`:593`) thunks itself and binds that thunk at index 0, so the
body can call itself by `Force`-ing variable 0. This is how [[translate|translated functions]]
loop.

> **Cleanliness.** Most arms are 7–8-line `Machine { … done: false }` literals that restate
> five unchanged fields; the suspension-reschedule block is copy-pasted across five arms.
> [[deep-review]] §C1–C2 propose `goto`/`reschedule` helpers to collapse ~150 lines.

Related: [[cbpv]], [[eval]], [[vclosure]], [[unify]], [[senv]], [[lvar]], [[env]].
