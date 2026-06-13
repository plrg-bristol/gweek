---
title: optimize.rs — the peephole optimizer
tags: [component, stub]
source: src/machine/optimize.rs
updated: 7972077
---

# `optimize.rs` *(stub — expand on demand)*

An optional peephole optimizer over [[cbpv|CBPV]] terms, enabled with `-o`. `optimize` /
`optimize_val` rewrite the term before [[eval|evaluation]]; the pass is verified to preserve
the solution multiset on every terminating example ([[deep-review]] §5). At 1,272 lines this
is the largest module and the best candidate for its own detailed page.

**Core machinery — binder-aware traversals.** Three passes rewrite the term while tracking
[[de-bruijn|de Bruijn]] depth across binders:

- `shift` (`optimize.rs:113-188`) — renumber free variables.
- `subst` (`:194-268`) — substitute a value for a variable.
- `swap` (`:329-397`) — exchange adjacent binders.

Each increments depth at the same binding forms (`Bind.cont`, `Lambda`, `Exists`, `Rec`,
`Ifz.sk`, `Case`, `Match.consk` at +2).

> **Architecture note.** These three traversals are byte-identical except for the `Var` leaf
> action; [[deep-review]] §A1 proposes a single generic `map_comp`/`map_val` to remove ~200
> lines and make the binder rules single-source. `resolve_val` is also a pass-through wrapper
> over `deep_resolve` (§C5).

Related: [[pipeline]], [[de-bruijn]], [[cbpv]], [[mterms]], [[translate]].
