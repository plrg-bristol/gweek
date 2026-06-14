---
title: translate.rs — surface AST → CBPV
tags: [component, machine]
source: src/machine/translate.rs
commit: d83302b
---

# `translate.rs`

Lowers the checked surface AST into the machine's [[cbpv|CBPV]] term language, turning named
variables into [[de-bruijn|de Bruijn indices]]. Entry point `translate(arena, ast)`
(`translate.rs:67`) returns the main computation plus the list of top-level function values.

## Name resolution: `TEnv` (`translate.rs:10`)

A stack of names. `find(v)` returns the de Bruijn index of the last binding of `v`, counted
from the *end* (`:31-36`). The lowering binds a placeholder for **every intermediate `Bind`**
it introduces, so indices stay aligned — getting these push/pop counts right is the
translator's whole correctness burden. `nullary` (`:39`) tracks zero-argument functions, stored
as thunks and `Force`d at use sites (`:750-756`); `members` maps the functions of a
mutually-recursive group to their `(bundle, index)` (see below).

## Top-level ordering and mutual recursion (`:140`, `:378`)

`order_functions` (`:140`) builds the call graph and runs **Tarjan's SCC** algorithm (`:195`)
to return strongly-connected groups in dependency order. Each group is lowered by
`translate_group` (`:378`):

- A singleton (non-recursive or self-recursive) becomes a `Thunk(Rec { body })` (`:83-93`).
- A genuine **mutually-recursive** group is lowered to a single shared fixpoint
  `rec self. λsel. ifz sel { … }` that dispatches on a selector index; each member is reached
  by applying the bundle to its index (`:742-749`). This is what makes mutual recursion work —
  [[deep-review]] §B3, fixed (no more cycle fallback / panic).

## Lowering functions (`translate_func` `:342`, `build_args` `:435`)

A function becomes nested `Lambda`s, one per argument, under the group's `Rec`. `build_args`
handles each argument; a **pair argument** `Arg::Pair` (`:453`) is destructured by
`bind_pattern` (`:524`), which introduces a fresh logic variable per leaf and equates the
reconstructed pair — so pair-pattern function arguments now lower correctly
([[deep-review]] §B10, fixed). A lambda *with* a pair argument still `panic!`s (`:719-722`),
but the [[type-checker]] rejects lambdas as arguments, so it is unreachable for well-typed
programs.

## Lowering statements and expressions

`translate_stmt` (`:570`) and `translate_expr` (`:675`) walk the AST:

- **`let`** → `Bind { comp, cont }`, the laziness point ([[suspensions-and-forcing]]).
- **`exists`** → `Exists { ptype, body }` with `translate_vtype` mapping the surface type to a
  runtime [[type-system|`ValueType`]].
- **`=:=`** → two `Bind`s evaluating each side, then `Equate { lhs, rhs, body }`.
- **`case`** → `Bind` of the scrutinee into an `Ifz` (Nat) or `Match` (List) eliminator.
- **`if`** (`:572`) → a `Case` on `Bool = Sum(Unit, Unit)` (`Inl` = true, `Inr` = false).
- **data** — `S`/`Cons`/`List`/`Pair`/literals compile to `Bind … Return(constructor)` chains.
- **application** → `Bind` operator, `Bind` argument, then `Force(op) ; App(arg)`.

**Boolean expressions** (`translate_bexpr`, `:894`) are now implemented ([[deep-review]] §B2):
`==`/`!=` lower through a recursive `Nat` equality (`nat_eq_thunk` `:784`, with `!=` via
`negate_comp` `:846`), `&&`/`||` through `translate_connective` (`:915`, short-circuiting via a
`Case`), `!` through `negate_comp`; literal operands are constant-folded (`:856-892`).

> **Remaining panics.** `translate` still `panic!`s on a few conditions the [[type-checker]]
> now rejects upstream — unbound variable (`:36`), pair pattern against a non-product (`:498`),
> and `translate_vtype` on `Int`/unresolved types (`:556-566`, the §B11 path). These are
> unreachable for well-typed programs; routing them to typed errors is the tail of
> [[deep-review]] §A4. `translate`'s signature still returns the tuple directly, not a `Result`.

Related: [[cbpv]], [[de-bruijn]], [[mterms]], [[type-checker]], [[optimizer]], [[step]].
