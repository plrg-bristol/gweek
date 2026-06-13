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

[[translate|`translate_vtype`]] (`translate.rs:317`) maps the surface types that can label an
`exists` into runtime `ValueType`s — notably `Bool` becomes `Sum(Unit, Unit)`
(`true = inl ()`, `false = inr ()`), which is why booleans need no dedicated runtime form.

## Bidirectional checking

The checker ([[type-checker]], `type_check.rs`) is **bidirectional**: it *synthesises* a type
where one is determined by the term (`synth_stmt` `:193`, `synth_expr` `:319`) and *checks* a
term against an expected type where one is known (`check_expr` `:387`). Type equality is
structural `unify` (`type_check.rs:95`), with `Type::Any` matching anything. It runs in two
passes so functions can be mutually referenced (`:134-138` then `:141-158`).

## Known gaps

The type system is the least finished part of the language; several documented features do
not actually work end-to-end ([[deep-review]] §B4–B6, §B10–B11):

- **Polymorphism is nominal, not real.** A lowercase type variable like `a` is just
  `Type::Ident("a")` and unifies only by string equality (`type_check.rs:95-110`), so a
  signature `id :: a -> a` checks at its definition but every *call* at a concrete type is
  rejected. There is no instantiation.
- **Lambda arguments are rejected.** The `(Lambda, Arrow)` rule lives in `check_expr` but
  `App` synthesises its argument instead of checking it, and `check_expr` is never called —
  so a lambda passed as an argument fails even when the expected type is known
  ([[deep-review]] §B5).
- **`*` and `->` share precedence** in the type parser (`parse.rs:57-83`), so `A * B -> C`
  mis-parses ([[deep-review]] §B6).
- **Checker/translator disagree on the alphabet.** `Int` and boolean expressions pass the
  checker but panic in [[translate|translation]] ([[deep-review]] §B2, §B11).

Related: [[type-checker]] (the code), [[value-type]], [[translate]], [[cbpv]].
