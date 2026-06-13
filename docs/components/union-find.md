---
title: union_find.rs — disjoint sets with data
tags: [component, stub]
source: src/machine/union_find.rs
updated: 7972077
---

# `union_find.rs` *(stub — expand on demand)*

A generic union-find (`UnionFind<T>`, `union_find.rs:38`) that stores a datum of type `T` per
node and exposes it **only** through a canonical `Root` token. Used by [[lvar]] to key
[[logic-variables|logic variable]] data on equivalence-class representatives.

**Key design.** `Root(usize)` (`:13`) has a private field, so it can only be produced by
`find` (`:51`), which also does path compression. `get`/`get_mut` (`:76`, `:80`) take a `Root`,
not a raw index — making it *impossible by construction* to read a binding at one slot and
write it at another. This type-level guarantee is the fix for the §B1 soundness bug
([[logic-variables]]).

**API:** `register(datum) -> Ident` (`:69`) adds a fresh singleton; `find(ident) -> Root`
(`:51`) canonicalizes with path compression; `union(i, j)` (`:84`) merges by rank (on a tie,
`j` becomes root, `:95`); `get`/`get_mut` access data at a `Root`.

Related: [[lvar]], [[logic-variables]], [[unify]], [[deep-review]].
