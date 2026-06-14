---
title: Type system
tags: [concept]
---

# Type system

gweek has two type vocabularies, used at two different times:

- **Surface types** (`Type`, `parser/type.rs`) — what the programmer writes and what the
  [[type-checker]] reasons about: `Arrow`, `Ident` (e.g. `Nat`, `Bool`), `List`, `Product`,
  and `Any` (a wildcard used internally).
- **Runtime value types** (`ValueType`, `value_type.rs:4`) — what the machine carries on a
  [[logic-variables|logic variable]] so it knows how to [[nondeterminism|split]] it. These
  follow the [[cbpv|CBPV]] value/computation split: `ValueType` is `Unit`, `Nat`,
  `Product`, `Sum`, `List`, `Thunk(ComputationType)`; `ComputationType` (`value_type.rs:27`)
  is `Return(ValueType)` (written `F t`) or `Arrow(ValueType, ComputationType)`.

[[translate|`translate_vtype`]] maps the surface types that can label an `exists` into runtime
`ValueType`s — notably `Bool` becomes `Sum(Unit, Unit)` (`true = inl ()`, `false = inr ()`),
which is why booleans need no dedicated runtime form.

## Bidirectional checking

The checker ([[type-checker]], `type_check.rs`) is **bidirectional**: it *synthesises* a type
where one is determined by the term, and *checks* a term against an expected type where one is
known (`check_expr` `:510`, `check_stmt` `:542`). It runs in two passes so functions can be
mutually referenced (signatures collected at `:259-263`, bodies checked at `:266-282`), and
reports problems as a typed `Result<(), Vec<TypeError>>` rather than panicking.

## Polymorphism by instantiation

Type variables are **real**, not nominal. Unification (`type_check.rs:211`) works over fresh
**metavariables** (`?0`, `?1`, …); each *use* of a polymorphic signature is `instantiate`d
(`:83`) with fresh metavariables, so `id :: a -> a` can be applied at any concrete type while
`bad :: a -> b` correctly rejects `bad x = x`. This was [[deep-review]] §B4.

## What the refactor fixed

Several features the original review flagged as broken now work end-to-end ([[deep-review]]):

- **Lambda arguments are checked**, not rejected — `check_expr` is called from `App`'s argument
  position (§B5).
- **`*` binds tighter than `->`** in the type parser, so `A * B -> C` parses correctly (§B6,
  see [[parser]]).
- **`Int` is rejected cleanly** by `resolve_type` (`:580`) instead of slipping through to a
  translation panic (§B11).
- **Boolean expressions and `if`** type-check *and* lower (§B2, see [[translate]]).
- **Pair-pattern function arguments** are accepted and destructured (§B10).

Related: [[type-checker]] (the code), [[value-type]], [[translate]], [[cbpv]].
