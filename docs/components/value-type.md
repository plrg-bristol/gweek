---
title: value_type.rs — runtime types
tags: [component]
source: src/machine/value_type.rs
commit: 6ec7c97
---

# `value_type.rs`

The runtime type vocabulary, following the [[cbpv|CBPV]] value/computation split. `ValueType`
(`value_type.rs:4-11`) is `Unit`, `Nat`, `Product`, `Sum`, `List`, `Thunk(ComputationType)`;
`ComputationType` (`:27-30`) is `Return(ValueType)` (printed `F(t)`, `:35`) or `Arrow(ValueType,
ComputationType)` (printed `a -> b`, `:36`). Compound cases use `Box` to stay finite. The
`Display` impls (`:13-24`, `:32-38`) print `Unit` as `1`, `List` as `[t]`, `Product` as `a * b`,
`Sum` as `a + b`, and `Thunk` as `U(c)`.

These are the types a [[logic-variables|logic variable]] carries (via [[lvar|`LogicEnv`]]) so
the [[step|eliminators]] know which constructors to guess when [[nondeterminism|splitting]] an
unbound variable. [[translate|`translate_vtype`]] (`translate.rs:554`) produces them from surface
[[type-system|types]] — e.g. `Bool ↦ Sum(Unit, Unit)` (`translate.rs:558-559`).

Related: [[type-system]], [[cbpv]], [[lvar]], [[mterms]].
