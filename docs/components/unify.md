---
title: unify.rs — unification
tags: [component, machine]
source: src/machine/unify.rs
commit: 6ec7c97
---

# `unify.rs`

Implements [[unification]] — the algorithm behind the `=:=` constraint. Called from
[[step|the `Equate` step]] (`step.rs:347`). For the conceptual picture see [[unification]];
this page is the code.

## Signature and error channel

```rust
pub fn unify<'a>(cfg: &Config, arena, lhs, rhs, env, lenv: &mut LogicEnv, senv)
    -> Result<(), UnifyError<'a>>
```

`cfg` is threaded explicitly (it carries `occurs_check` — [[deep-review]] §A2). `UnifyError`
(`unify.rs:10-14`) has three cases: `Occurs` (occurs-check failure), `Fail` (structural
mismatch) and `Susp(SuspAt)` (an operand needs forcing first). The caller turns `Fail`/`Occurs`
into a pruned branch and `Susp` into a reschedule.

## The worklist (`unify.rs:16-121`)

Unification is iterative, not recursive: a `Vec` of closure pairs still to reconcile, seeded
with `(lhs, rhs)`. Each iteration:

1. Pop a pair and [[vclosure|head-close]] both sides; a suspension short-circuits to
   `Err(Susp)` (`:29-30`).
2. Match on the resolved pair:
   - **var ~ var** (`:34`) → `lenv.identify` unions the classes ([[lvar]]). No value chosen.
   - **var ~ value** / **value ~ var** (`:37`, `:44`) → occurs-check if `cfg.occurs_check`,
     then `lenv.set_vclos` binds the variable.
   - **value ~ value** (`:61`) → structural, below.

## Structural arms (`unify.rs:61-114`)

- Equal nullary constructors `Unit`/`Zero`/`Nil` succeed (`:64`).
- `Nat(a)` vs `Nat(b)` → equal or `Fail` (`:67`).
- **Mixed naturals** (`:73-94`): `Nat(0)`~`Zero` succeeds; `Nat(n)`~`Succ(v)` pushes
  `Nat(n-1)`~`v`; `Nat(0)`~`Succ` fails; etc. This block reconciles the
  [[mterms|dual natural representation]] ([[deep-review]] §A3 proposed retiring it; not yet done).
- `Succ`~`Succ`, `Cons`~`Cons`, `Pair`~`Pair`, `Inl`~`Inl`/`Inr`~`Inr` push their children
  (`:96-108`).
- A `Thunk` on either side `panic!`s (`:111`) — values being unified are first-order, never
  thunks; a `Susp` is `unreachable!` because `close_head` resolves or errors first (`:116`).
- Anything else → `Fail` (`:113`).

The occurs check itself lives in [[vclosure|`occurs_lvar`]] (`vclosure.rs:118`) and is on
unless `--no-occurs-check`. With it off, a cyclic binding no longer overflows on output —
[[vclosure|`close`]] bounds its depth ([[deep-review]] §B13).

Related: [[unification]], [[step]], [[lvar]], [[union-find]], [[vclosure]], [[mterms]], [[config]].
