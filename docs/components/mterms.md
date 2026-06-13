---
title: mterms.rs — the CBPV term language
tags: [component, machine]
source: src/machine/mterms.rs
updated: 7972077
---

# `mterms.rs`

Defines the machine's term language: the [[cbpv|Call-By-Push-Value]] split into **values**
and **computations**. These are the types every other machine module manipulates. Terms are
allocated in the arena and held by reference (`&'a MValue<'a>`), so they are cheap to share
and `Copy`.

## `MValue` — inert data (`mterms.rs:12-24`)

```rust
pub enum MValue<'a> {
    Var(usize),                              // de Bruijn index — see [[de-bruijn]]
    Unit,
    Nat(u64),                                // packed natural
    Zero, Succ(&'a MValue<'a>),              // symbolic natural
    Pair(&'a MValue<'a>, &'a MValue<'a>),
    Inl(&'a MValue<'a>), Inr(&'a MValue<'a>),// sum injections
    Nil, Cons(&'a MValue<'a>, &'a MValue<'a>),
    Thunk(&'a MComputation<'a>),             // frozen computation
}
```

- **Dual naturals.** A natural is either `Nat(u64)` (compact) or `Zero`/`Succ` (symbolic).
  Both exist because an unbound [[logic-variables|logic variable]] of type `Nat` is
  [[nondeterminism|split]] into `0` and `S(fresh)`, which needs a symbolic successor. Every
  *runtime* site actually produces `Nat`; the `Zero` variant is effectively dead and
  [[deep-review]] §A3 proposes removing it. [[unification|Unification]] and `Ifz` carry the
  arms that reconcile the two forms.
- **`Thunk`** is the value/computation bridge ([[cbpv]]): `comp.thunk(arena)` wraps a
  computation as a value (`mterms.rs:136`).
- **`Display`** renders for solution output: symbolic naturals fold to a number via `to_nat`
  (`mterms.rs:55`), lists to `[a, b, …]` via `to_list` (`:71`), `Inl(())`/`Inr(())` print as
  `true`/`false` (`:43-50`).

## `MComputation` — things that run (`mterms.rs:87-133`)

| Group | Variants | Notes |
|---|---|---|
| Eliminators | `Ifz`, `Match`, `Case` | one continuation per constructor; branch on unbound vars |
| CBPV core | `Return`, `Bind`, `Force`, `Lambda`, `App` | sequencing and functions |
| Functional-logic | `Choice(&[..])`, `Exists`, `Equate` | [[nondeterminism|choice]], [[logic-variables|existentials]], [[unification|`=:=`]] |
| Recursion | `Rec` | self-reference; how functions loop |

How each variant *steps* is the subject of [[step]]. How surface syntax *becomes* these is
[[translate]].

## Helpers

- `thunk(&self, arena)` (`:136`) — allocate `Thunk(self)`.
- `count_nodes` on both types (`:140`, `:167`) — term-size metric used under the
  `opt-stats` feature ([[deep-review]] §C4 notes it is not feature-gated).

Related: [[cbpv]], [[step]], [[translate]], [[value-type]], [[de-bruijn]].
