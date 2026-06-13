---
title: translate.rs — surface AST → CBPV
tags: [component, machine]
source: src/machine/translate.rs
updated: 7972077
---

# `translate.rs`

Lowers the checked surface AST into the machine's [[cbpv|CBPV]] term language, turning named
variables into [[de-bruijn|de Bruijn indices]]. Entry point `translate(arena, ast)`
(`translate.rs:63`) returns the main computation plus the list of top-level function values.

## Name resolution: `TEnv` (`translate.rs:10-51`)

A stack of names. `find(v)` returns the de Bruijn index of the last binding of `v`, counted
from the top (`:27`). Crucially, the lowering binds a placeholder `"_"` for **every
intermediate `Bind`** it introduces, so indices stay aligned — e.g. `Cons` pushes one `"_"`
between head and tail (`:455-466`), `Equate` pushes two (`:372-395`). `nullary` (`:12`) tracks
zero-argument functions, which are stored as thunks and must be `Force`d at use sites
(`:494-498`).

## Top-level reordering (`translate.rs:94-189`)

`reorder_decls` groups each function with its signature, builds a reference graph, and
topologically sorts it (Kahn's algorithm, `:161-171`) so every name is bound before it is used.

> **Known issue.** On a genuine **cycle** (mutual recursion) it falls back to the original
> order (`:173-176`). Since each name is only bound at its own definition site, no linear
> order satisfies a cycle, and the first function references a not-yet-bound name →
> `TEnv::find` panics ([[deep-review]] §B3). The per-function `Rec` wrapper cannot express
> mutual recursion.

## Lowering functions (`translate_func`, `:281-315`)

A function becomes a **thunk of `Rec`** wrapping nested `Lambda`s — one per argument. A nullary
function is `Thunk(Rec { body })` (`:302`); an *n*-ary one curries: each extra argument adds a
`Lambda` that `Return`s a thunk of the rest (`:305-313`). This is the value side of the
[[cbpv]] coercion that [[step|`App`/`Force`]] consume.

> **Known issue.** Only `Arg::Ident` arguments are handled; `Arg::Pair` is `todo!()` (`:288`),
> as is a lambda pair-argument (`:476`). Pair destructuring type-checks but cannot be lowered
> ([[deep-review]] §B10).

## Lowering statements and expressions

`translate_stmt` (`:333`) and `translate_expr` (`:438`) walk the AST. Highlights:

- **`let`** → `Bind { comp, cont }` (`:356`), the laziness point ([[suspensions-and-forcing]]).
- **`exists`** → `Exists { ptype, body }` with `translate_vtype` mapping the surface type to a
  runtime [[type-system|`ValueType`]] (`:317`, `:363`).
- **`=:=`** → two `Bind`s that evaluate each side, then `Equate { lhs, rhs, body }` over the
  bound indices (`:372-395`).
- **`case`** → `Bind` of the scrutinee into an `Ifz` (Nat) or `Match` (List) eliminator
  (`:405-433`); the dispatch comes from the `CasesType` the parser tagged.
- **`if`** → desugars to a `Case` on a `Bool = Sum(Unit,Unit)` (`:335-353`).
- **data** — `S`/`Cons`/`List`/`Pair`/literals each compile to `Bind … Return(constructor)`
  chains so sub-results are named before assembly (`:444-559`).
- **application** → `Bind` operator, `Bind` argument, then `Force(op) ; App(arg)`
  (`:478-489`).

> **Known issue.** `translate_bexpr` is `todo!()` (`:518`), so any program using `==`, `!=`,
> `&&`, `||`, `!`, or `if` type-checks then aborts in translation ([[deep-review]] §B2).
> `translate_vtype` likewise `panic!`s on `Int` and unresolved types (`:324`, `:329` →
> [[deep-review]] §B11).

Related: [[cbpv]], [[de-bruijn]], [[mterms]], [[type-checker]], [[optimizer]], [[step]].
