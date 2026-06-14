---
title: value_type.rs — runtime types
tags: [component, stub]
source: src/machine/value_type.rs
commit: d83302b
---

# `value_type.rs` *(stub — expand on demand)*

The runtime type vocabulary, following the [[cbpv|CBPV]] value/computation split. `ValueType`
(`value_type.rs:4`) is `Unit`, `Nat`, `Product`, `Sum`, `List`, `Thunk(ComputationType)`;
`ComputationType` (`:27`) is `Return(ValueType)` (printed `F t`) or `Arrow(ValueType,
ComputationType)`. Compound cases use `Box` to stay finite.

These are the types a [[logic-variables|logic variable]] carries (via [[lvar|`LogicEnv`]]) so
the [[step|eliminators]] know which constructors to guess when [[nondeterminism|splitting]] an
unbound variable. [[translate|`translate_vtype`]] produces them from surface
[[type-system|types]] — e.g. `Bool ↦ Sum(Unit, Unit)`.

Related: [[type-system]], [[cbpv]], [[lvar]], [[mterms]].
