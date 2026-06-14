---
title: union_find.rs — disjoint sets with data
tags: [component]
source: src/machine/union_find.rs
commit: 6ec7c97
---

# `union_find.rs`

`UnionFind<T>` (`union_find.rs:36-39`) is a generic union-find that *owns* a datum of type `T`
per node and exposes it **only** through a canonical `Root` token. [[lvar|`LogicEnv`]] instantiates
it at `T = (ValueType, Option<VClosure>)` to key [[logic-variables|logic variable]] data on
equivalence-class representatives.

## The `Root` token

`Root(usize)` (`:10-11`) wraps the canonical class index, but its field is private to the module.
A `Root` can therefore only be produced by `find` (or the self-root that `register` establishes
implicitly). Because `get`/`get_mut` (`:81-83`, `:85-87`) take a `Root` rather than a raw
`usize`, it is *impossible by construction* to read a binding at one slot while writing it at
another — the read/write canonicalization invariant is inexpressible to violate from outside the
module. This type-level guarantee is the fix for the §B1 soundness bug ([[logic-variables]],
[[lvar]]).

Fusing the union-find with its data (one `Vec<Node>` plus one `Vec<T>`, `:37-38`) also removes
the desync surface that two parallel vectors would create: there is no second array whose indices
could drift out of step.

## Structure and operations

Each `Node` (`:13-17`) holds a rank `depth` and a `Cell<Option<usize>>` parent pointer; the
`Cell` lets `find` compress paths through a shared `&self`.

- `register(datum) -> usize` (`:74-79`) appends a fresh singleton node carrying `datum` (its own
  root) and returns its index.
- `find(ident) -> Root` (`:49-63`) walks to the root, then does a second pass of path
  compression, pointing every node on the path directly at the root.
- `canonical(ident) -> usize` (`:68-70`) returns the root as a raw `usize` for read-only uses
  (e.g. naming a residual variable by a stable class id) that do not address per-variable
  storage — it deliberately bypasses the `Root` token.
- `union(i, j)` (`:89-103`) merges by rank: the deeper tree's root stays root; on a tie, `j`'s
  root becomes the parent and its rank increments (`:99-102`). (This tie rule is why [[lvar]]'s
  B1 regression test binds the *first* argument to exercise the non-root write.)
- `get`/`get_mut` (`:81-87`) access the per-node datum at a `Root`.

`UnionFind` derives `Clone` (`:35`); [[lvar]] clones it copy-on-write behind an `Rc`, which is
the source of the §P2 performance issue.

Related: [[lvar]], [[logic-variables]], [[unify]], [[deep-review]].
