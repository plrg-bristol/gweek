---
title: Unification
tags: [concept]
---

# Unification

Unification is how gweek solves the constraint `lhs =:= rhs`: it makes two values equal by
binding [[logic-variables|logic variables]], or fails the branch if they cannot be made
equal. The concept page covers the *idea*; the line-by-line algorithm is in [[unify]].

The constraint is surface `Stmt::Equate`, lowered to `MComputation::Equate { lhs, rhs, body }`
and stepped at `step.rs:323`, which calls `unify(cfg, arena, lhs, rhs, …)` and continues into
`body` on success.

## The algorithm in one breath

`unify` (`unify.rs:16`) is an **iterative worklist**, not recursion: a stack of closure pairs
to reconcile. Each iteration pops a pair, [[vclosure|head-closes]] both sides, and matches on
the two resolved forms:

- **var ~ var** (`unify.rs:34`): both unbound → `identify` them (union the classes). No value
  is chosen; they just become aliases.
- **var ~ value** (`unify.rs:37,44`): bind the variable to the value with `set_vclos`, after
  the [[#occurs-check|occurs check]].
- **value ~ value** (`unify.rs:61`): structural. Equal scalars succeed; matching constructors
  push their children onto the worklist (`Cons`/`Cons`, `Pair`/`Pair`, `Inl`/`Inl`, `Succ`/`Succ`);
  mismatches return `Err(Fail)`.

Pushing children rather than recursing keeps stack depth bounded by the worklist, and means a
single `=:=` can decompose a deep structure in one call.

## Naturals have a dual representation

Naturals can appear as a packed `Nat(u64)` or as symbolic `Zero`/`Succ` (the symbolic form is
needed so an unbound `Nat` can be split into `0` vs `S(fresh)`). Unification reconciles the
two: `Nat(n)` vs `Succ(v)` peels one successor by pushing `Nat(n-1)` against `v`
(`unify.rs:78-90`), `Nat(0)` vs `Succ(_)` fails, and so on. ([[deep-review]] §A3 argued the
`Zero` variant could be retired to collapse these arms; that cleanup is not yet applied.)

## Occurs check

Binding `x` to a term that *contains* `x` would create an infinite term (`x = S x`). The
occurs check (`occurs_lvar`, `vclosure.rs:118`) walks the candidate value looking for the
variable, and unification refuses the bind if found (`unify.rs:37-40,44-48`), returning
`Err(Occurs)`. It is on by default and is **not** a hot path — leave it on ([[deep-review]]
steering notes). `--no-occurs-check` disables it; a resulting cyclic term no longer overflows
the stack on output — [[vclosure|`close`]] bounds its depth and reports a cyclic-term error
([[deep-review]] §B13, fixed).

## When a side isn't ready: suspensions

Head-closing a side can hit a [[suspensions-and-forcing|suspension]] that must run first.
`close_head` then returns `Err(SuspAt)`, `unify` propagates it as `UnifyError::Susp`
(`unify.rs:29-30`), and [[step|the `Equate` step]] reschedules: it pushes a `Set` frame to
force the suspension, runs it, and re-enters the `Equate`. Unification is thus re-driven once
the operand is forced — the constraint itself eagerly forces what it needs.

Related: [[unify]] (the code), [[logic-variables]], [[vclosure]], [[lvar]], [[union-find]].
