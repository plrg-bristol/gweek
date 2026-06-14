---
title: union_find.rs — disjoint sets with data
tags: [component, stub]
source: src/machine/union_find.rs
commit: d83302b
---

# `union_find.rs` *(stub — expand on demand)*

A generic union-find (`UnionFind<T>`, `union_find.rs:36-39`) that stores a datum of type `T`
per node and exposes it **only** through a canonical `Root` token. Used by [[lvar]] to key
[[logic-variables|logic variable]] data on equivalence-class representatives.

**Key design.** `Root(usize)` (`:11`) has a private field, so it can only be produced by
`find` (`:49`), which also does path compression. `get`/`get_mut` (`:81`, `:85`) take a `Root`,
not a raw index — making it *impossible by construction* to read a binding at one slot and
write it at another. This type-level guarantee is the fix for the §B1 soundness bug
([[logic-variables]]).

**API:** `register(datum) -> usize` (`:74`) adds a fresh singleton; `find(ident) -> Root`
(`:49`) canonicalizes with path compression; `canonical(ident) -> usize` (`:68`) returns the
raw root index for read-only display (used to render residual variables); `union(i, j)` (`:89`)
merges by rank (on a tie, `j` becomes root, `:95`); `get`/`get_mut` access data at a `Root`.

Related: [[lvar]], [[logic-variables]], [[unify]], [[deep-review]].
