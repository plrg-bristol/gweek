---
title: unify.rs — unification
tags: [component, machine]
source: src/machine/unify.rs
updated: 7972077
---

# `unify.rs`

Implements [[unification]] — the algorithm behind the `=:=` constraint. Called from
[[step|the `Equate` step]] (`step.rs:290`). For the conceptual picture see [[unification]];
this page is the code.

## Signature and error channel

```rust
pub fn unify<'a>(arena, lhs, rhs, env, lenv: &mut LogicEnv, senv) -> Result<(), UnifyError>
```

`UnifyError` (`unify.rs:10`) has three cases: `Occurs` (occurs-check failure), `Fail`
(structural mismatch) and `Susp(SuspAt)` (an operand needs forcing first). The caller turns
`Fail`/`Occurs` into a pruned branch and `Susp` into a reschedule.

## The worklist (`unify.rs:24-118`)

Unification is iterative, not recursive: a `Vec` of closure pairs still to reconcile,
seeded with `(lhs, rhs)` (`:25`). Each iteration:

1. Pop a pair and [[vclosure|head-close]] both sides; a suspension short-circuits to
   `Err(Susp)` (`:28-29`).
2. Match on the resolved pair:
   - **var ~ var** (`:32`) → `lenv.identify` unions the classes ([[lvar]]). No value chosen.
   - **var ~ value** / **value ~ var** (`:35`, `:43`) → occurs-check (if enabled), then
     `lenv.set_vclos` binds the variable.
   - **value ~ value** (`:51`) → structural, below.

## Structural arms (`unify.rs:60-113`)

- Equal nullary constructors `Unit`/`Zero`/`Nil` succeed (`:61`).
- `Nat(a)` vs `Nat(b)` → equal or `Fail` (`:66`).
- **Mixed naturals** (`:73-93`): `Nat(0)`~`Zero` succeeds; `Nat(n)`~`Succ(v)` pushes
  `Nat(n-1)`~`v`; `Nat(0)`~`Succ` fails; etc. This block reconciles the
  [[mterms|dual natural representation]] and is the verbose part [[deep-review]] §A3 flags.
- `Succ`~`Succ`, `Cons`~`Cons`, `Pair`~`Pair`, `Inl`~`Inl`/`Inr`~`Inr` push their children
  (`:95-108`).
- A `Thunk` on either side `panic!`s (`:109`) — values being unified are first-order, never
  thunks; a `Susp` is `unreachable!` because `close_head` resolves or errors first (`:114`).
  [[deep-review]] §5 confirms these are genuinely unreachable today.
- Anything else → `Fail` (`:112`).

The occurs check itself lives in [[vclosure|`occurs_lvar`]] (`vclosure.rs:22`) and is on
unless `--no-occurs-check`.

Related: [[unification]], [[step]], [[lvar]], [[union-find]], [[vclosure]], [[mterms]].
