---
title: lvar.rs — logic-variable environment
tags: [component, stub]
source: src/machine/lvar.rs
commit: d83302b
---

# `lvar.rs` *(stub — expand on demand)*

`LogicEnv<'a>` (`lvar.rs:9-11`) is the store of [[logic-variables|logic variable]] bindings and
equivalence classes. It wraps an `Rc<`[[union-find|`UnionFind`]]`>` whose per-variable datum
is `(ValueType, Option<VClosure>)` — the variable's [[type-system|declared type]] plus its
binding if any. The `Rc` gives copy-on-write semantics so [[nondeterminism|branching]] can
clone it cheaply (`Rc::make_mut` on write).

Variables are identified by the `LVar` newtype ([[mterms|mod.rs]]`:21`), not a bare `usize` —
distinct from suspensions' `SuspId` (the [[deep-review]] §A5 split).

**API:** `fresh(ptype) -> LVar` (`:20`) registers a new unbound variable; `lookup(ident)`
(`:24`) and `get_type(ident)` (`:35`) read at the class **root**; `set_vclos(ident, vclos)`
(`:29`) writes the binding at the root; `identify(i, j)` (`:40`) unions two classes;
`root(ident) -> LVar` (`:47`) exposes the canonical representative (used by [[vclosure|`close`]]
to render residual free variables as a single placeholder).

**Invariant.** All reads and writes canonicalize through the union-find **root**
(`store.find(ident.0)`). This is enforced by [[union-find]]'s `Root` token (only `find` mints
one), which fixed the §B1 soundness bug (commit `0f34f45`) — see [[logic-variables]]. A
regression test pins it (`:52-96`).

> **Performance (still open).** Copy-on-write `Rc<UnionFind>` means the first write on a shared
> clone deep-copies the whole store → O(N²) on deep search ([[deep-review]] §P2, a
> trail/undo-log redesign, is **not** yet applied).

Related: [[logic-variables]], [[union-find]], [[unify]], [[vclosure]], [[value-type]].
