---
title: lvar.rs — logic-variable environment
tags: [component]
source: src/machine/lvar.rs
commit: 6ec7c97
---

# `lvar.rs`

`LogicEnv<'a>` (`lvar.rs:9-11`) is the store of [[logic-variables|logic variable]] bindings and
equivalence classes. It wraps an `Rc<`[[union-find|`UnionFind`]]`>` whose per-variable datum is
`(ValueType, Option<VClosure>)` — the variable's [[type-system|declared type]] plus its binding
if any. The `Rc` gives copy-on-write semantics so [[nondeterminism|branching]] can clone the
store cheaply; the first mutation on a shared clone deep-copies it (`Rc::make_mut`, see the
performance note below).

Variables are identified by the `LVar` newtype ([[mterms|mod.rs]]`:21`), a `usize` wrapper
distinct from suspensions' `SuspId` ([[mterms|mod.rs]]`:23`) — the [[deep-review]] §A5 split that
makes the two index spaces non-interchangeable at the type level.

## API

- `fresh(ptype) -> LVar` (`:20-22`) registers a new unbound variable of the given type via
  `UnionFind::register`, returning its `LVar`. Called by `Exists` and by the case-split branches
  in [[step]].
- `lookup(ident) -> Option<VClosure>` (`:24-27`) reads the binding at the class **root**:
  `find(ident.0)` then `get(root).1`.
- `set_vclos(ident, vclos)` (`:29-33`) records a binding, again at the **root**: it resolves
  `find(ident.0)` *before* writing `get_mut(root).1`.
- `get_type(ident) -> ValueType` (`:35-38`) reads the stored `ValueType` at the root — the type
  the eliminators consult to know which constructors to guess when splitting an unbound variable.
- `identify(i, j)` (`:40-42`) unions two classes (used at `unify.rs:34` when two unbound
  variables meet), so binding either one later binds both.
- `root(ident) -> LVar` (`:47-49`) returns the canonical representative of the class (via
  `UnionFind::canonical`), so [[vclosure|`close`]] can render every member of a unified class as
  a single residual placeholder.

## Invariant: read and write through the root

Every read and write canonicalizes through the union-find **root** (`store.find(ident.0)` in
`lookup`, `set_vclos`, and `get_type`). This is what makes binding sound: a constraint placed on
any member of an equivalence class is visible through every member.

The invariant is enforced *by construction* by [[union-find]]'s `Root` token — only `find` can
mint one, and `get`/`get_mut` accept only a `Root`, so a write physically cannot land in a
non-root slot. This is the fix for the §B1 soundness bug (commit `0f34f45`), where the old
`set_vclos` wrote at the raw ident while `lookup` read at the root, silently losing constraints
on non-root members. A regression test pins it (`:52-96`): it unions `{a, b}` so `a` is the
*non-root* member, binds `a`, and asserts the binding is visible through both idents — see
[[logic-variables]].

> **Performance (still open, [[deep-review]] §P2).** The backtracking state is copy-on-write
> `Rc<UnionFind>` (`:10`). The first write on a clone shared by a sibling branch triggers
> `Rc::make_mut`, which deep-copies the *entire* store, so a search of depth N that mutates at
> each level is O(N²) in store size. The proposed trail/undo-log redesign is **not** yet applied.

Related: [[logic-variables]], [[union-find]], [[unify]], [[vclosure]], [[value-type]].
