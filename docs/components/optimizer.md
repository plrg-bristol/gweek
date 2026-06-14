---
title: optimize.rs — the peephole optimizer
tags: [component, stub]
source: src/machine/optimize.rs
commit: d83302b
---

# `optimize.rs` *(stub — expand on demand)*

An optional peephole optimizer over [[cbpv|CBPV]] terms, enabled with `-o`. `optimize` (`:6`)
and `optimize_val` (`:20`) rewrite the term before [[eval|evaluation]]; the pass is verified to
preserve the solution multiset on every terminating example ([[deep-review]] §5). Still the
largest module and the best candidate for its own detailed page.

**Core machinery — one generic binder-aware traversal.** `map_val` (`:116`) and `map_comp`
(`:140`) walk a term carrying a `binders` depth and apply a leaf callback `f(binders, &Var)`;
the depth is incremented at exactly the binding forms. The three rewriting passes are now thin
wrappers over `map_comp`:

- `shift_comp` (`:207`) — renumber free variables (`i >= cutoff`).
- `subst_comp` (`:225`) — substitute a value for a variable, shifting and decrementing.
- `swap_comp` (`:297`) — exchange adjacent binders.

This collapsed the three byte-identical traversals into one shared definition —
[[deep-review]] §A1, fixed. The optimizer proper is `opt_comp_env` (`:379`, recurse then
`rewrite`) with the rule dispatcher `rewrite` (`:440`) applying beta/eta/dead-bind/pull rules
over an environment of statically-known bindings (`deep_resolve`, `:343`).

> **Also fixed:** `resolve_val` (the pass-through wrapper) was deleted in favour of
> `deep_resolve` ([[deep-review]] §C5); `count_nodes` use is gated behind `opt-stats` (§C4).

Related: [[pipeline]], [[de-bruijn]], [[cbpv]], [[mterms]], [[translate]].
