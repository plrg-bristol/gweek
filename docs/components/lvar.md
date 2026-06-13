---
title: lvar.rs — logic-variable environment
tags: [component, stub]
source: src/machine/lvar.rs
updated: 7972077
---

# `lvar.rs` *(stub — expand on demand)*

`LogicEnv<'a>` (`lvar.rs:9`) is the store of [[logic-variables|logic variable]] bindings and
equivalence classes. It wraps an `Rc<`[[union-find|`UnionFind`]]`>` whose per-variable datum
is `(ValueType, Option<VClosure>)` — the variable's [[type-system|declared type]] plus its
binding if any. The `Rc` gives copy-on-write semantics so [[nondeterminism|branching]] can
clone it cheaply (`Rc::make_mut` on write).

**API:** `fresh(ptype) -> Ident` (`:20`) registers a new unbound variable; `lookup(ident)`
(`:24`) and `get_type(ident)` (`:35`) read at the class **root**; `set_vclos(ident, vclos)`
(`:29`) writes the binding at the root; `identify(i, j)` (`:40`) unions two classes.

**Invariant.** All reads and writes go through the union-find **root**. This is enforced by
[[union-find]]'s `Root` token (only `find` mints one), which is what fixed the §B1 soundness
bug in commit `0f34f45` — see [[logic-variables]] for the full story.

> **Performance.** Copy-on-write `Rc<Vec>` means the first write on a shared clone deep-copies
> the whole store → O(N²) on deep search ([[deep-review]] §P2, which proposes a trail/undo log).

Related: [[logic-variables]], [[union-find]], [[unify]], [[vclosure]], [[value-type]].
