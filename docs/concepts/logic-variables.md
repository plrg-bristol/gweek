---
title: Logic variables
tags: [concept]
---

# Logic variables

A logic variable is an unknown that the machine may bind later, by [[unification]] or by a
[[nondeterminism|case split]]. They are introduced by `exists x :: T. body` — surface
`Stmt::Exists`, lowered to `MComputation::Exists { ptype, body }` ([[mterms]]) and stepped at
`step.rs:274`:

```rust
MComputation::Exists { ptype, body } => {
    let ident = lenv.fresh(ptype.clone());     // allocate a fresh unbound variable
    let new_env = env.extend_lvar(arena, ident); // push it into the environment
    ...
}
```

So `exists` does two things: it registers a fresh variable of the declared type in the
**logic environment** ([[lvar]]), and it binds that variable into the local [[env|de Bruijn
environment]] via `extend_lvar` so the body can refer to it as an ordinary variable.

## Representation: three kinds of "value reference"

The machine never stores a logic variable inside an `MValue`. Instead, *resolution* is
deferred to [[vclosure|`VClosure`]], which has three variants (`vclosure.rs:11`):

- `Clos { val, env }` — a concrete value in its environment;
- `LogicVar { ident }` — an unresolved logic variable;
- `Susp { ident }` — a [[suspensions-and-forcing|suspended]] computation.

When the machine looks through a variable ([[vclosure|`close_head`]], `vclosure.rs:51`), a de
Bruijn `Var` that points at a logic slot surfaces as `LogicVar { ident }`. Code that needs a
real shape (the eliminators, [[unify|unification]]) sees this and either branches or binds.

## Storage: union-find through `Root`

Bindings live in [[lvar|`LogicEnv`]], which wraps a [[union-find]] keyed by `Ident`
(`lvar.rs`). Two facilities:

- **Binding.** `set_vclos(ident, vclos)` records that a variable now equals a value
  (`lvar.rs:29`). `lookup(ident)` reads it back (`lvar.rs:24`).
- **Aliasing.** When unification meets two *unbound* variables, it merges their equivalence
  classes with `identify` (`lvar.rs:40`, used at `unify.rs:33`), so binding one later binds
  both.

The critical invariant: a class has one canonical representative (its `Root`), and **all
reads and writes go through that root**. This used to be a soundness bug — `lookup` read at
the root but `set_vclos` wrote at the raw ident ([[deep-review]] §B1). It is now correct *by
construction*: [[union-find]] only exposes data behind a `Root` token that only `find` can
mint (`union_find.rs:13`), fixed in commit `0f34f45`. A write simply cannot land in a
non-root slot.

## How an unbound variable becomes a value

Two paths bind a logic variable:

1. **Unification** ([[unify]]) — `x =:= [1,2]` binds `x` directly via `set_vclos`.
2. **Case split** — when an eliminator scrutinises an unbound variable of an algebraic type,
   the machine guesses each constructor. E.g. `Ifz` on an unbound `Nat` (`step.rs:363-405`)
   forks into a branch where the variable is `0` and one where it is `S(fresh)`, the `fresh`
   itself a new logic variable. `Match` does `[]` vs `(h:t)` (`step.rs:449`), `Case` does
   `inl`/`inr` (`step.rs:539`). The guessed type comes from the variable's stored
   `ValueType` ([[type-system]], read via `lenv.get_type`).

## Residual variables in answers

If a solution still mentions an unbound variable, [[vclosure|`close`]] currently only emits a
value for it when its type is `Unit`; otherwise the whole answer is dropped
([[deep-review]] §B7). So `exists x :: Nat. x.` reports 0 solutions instead of a free `x`.
Flagged, not yet fixed.

Related: [[unification]], [[lvar]], [[union-find]], [[vclosure]], [[nondeterminism]].
