---
title: optimize.rs — the equational optimizer
tags: [component, machine]
source: src/machine/optimize.rs
commit: 6ec7c97
---

# `optimize.rs`

An optional optimizer over [[cbpv|CBPV]] terms, enabled with `-o`. It rewrites the term before
[[eval|evaluation]] using equational laws of the CBPV theory; the pass is verified to preserve
the solution multiset on every terminating example ([[deep-review]] §5). It is the largest
machine module.

Two entry points: `optimize` (`:6`) optimizes the main computation, `optimize_val` (`:20`)
optimizes a top-level function value (recursing into its `Thunk`). Both are pure rewrites on
arena-allocated terms; the optional `opt-stats` feature (`:39-109`) instruments rule firings and
prints node-count deltas via [[mterms|`count_nodes`]].

## Core machinery: one generic binder-aware traversal (`:111-192`)

`map_val` (`:116`) and `map_comp` (`:140`) rebuild a term while carrying a `binders` count — the
number of binders crossed from the traversal root to the current leaf — and apply a leaf
callback `f(binders, &Var)` at every `Var`. The per-form depth table (which forms bind, and by
how much: `Bind.cont` +1, `Lambda`/`Exists`/`Rec`/`Ifz.sk` +1, `Case.inlk`/`inrk` +1,
`Match.consk` +2) lives here once. The three [[de-bruijn|de Bruijn]] passes are thin wrappers:

- `shift_val`/`shift_comp` (`:196`, `:207`) — renumber free variables (`i >= binders`) by
  `delta`. `shift_comp` short-circuits `delta == 0`.
- `subst_comp` (`:225`) — replace `Var(depth)` with the replacement shifted past the crossed
  binders, and decrement every `Var(i)` with `i > depth`.
- `swap_comp` (`:297`) — exchange the two adjacent binders at `depth`/`depth+1`.

This collapsed what were three byte-identical binder-aware traversals into one shared
definition — [[deep-review]] §A1, fixed.

## Free-variable and structural helpers (`:238-330`)

- `val_contains` (`:242`) — does a value occur as a strict sub-value? Used for the equate cycle
  rule (`V =:= C[V]` → fail).
- `has_free_var_val`/`has_free_var_comp` (`:256`, `:268`) — does de Bruijn index `target` occur
  free? Drives the dead-bind and lam-equate rules.
- `is_total` (`:311`) — conservative "guaranteed to return" check (`Return`, and `Bind`/`Ifz`/
  `Match`/`Case` whose branches are all total). Guards the dead-end rule.
- `is_fail` (`:324`) / `fail` (`:328`) — recognise and build the empty `Choice(&[])`, i.e. the
  failed computation.

## The driver: recurse, then rewrite (`:363-437`)

Optimization is term rewriting under a **compile-time environment** `Env = Vec<Option<&MValue>>`
(`:332`) recording statically-known bindings (`None` for opaque binders, `Some(v)` for a binding
proved equal to a value). `push_env` (`:334`) prepends an entry for a freshly crossed binder.

`opt_comp_env` (`:379`) is the core loop: `opt_subterms` (`:384`) first optimizes every
subterm under the extended environment, then `rewrite` (`:440`) tries top-level rules; whenever
a rule fires it re-optimizes the result (so rewriting runs to a fixpoint). `opt_subterms` is the
only place that extends the environment: a `Bind` of a `Return(v)` records the (deeply resolved)
`v` so downstream eliminators can fire (`:387-396`); all other binders push `None`.

`deep_resolve` (`:343`) chases a value through the environment to a fully-concrete form (shifting
each substituted binding past its index), so the decision rules can see the actual constructor
behind a variable. `opt_val` (`:363`) recurses structurally into values, optimizing computations
inside `Thunk`s.

## Rewrite rules (`rewrite`, `:440-854`)

`rewrite` dispatches on the head form. The rules, grouped by form:

- **`Bind`** (`:448`): `fail to x. M` → `fail`; eta `M to x. return x` → `M`; dead-bind
  `return V to x. M` → `M↓` when `x ∉ FV(M)`; variable aliasing `return Var(i) to x. M` →
  `M[Var(i)/x]`; dead-end `M to x. fail` → `fail` when `M` total; and the four **pull/assoc**
  rules that hoist a producer out of the binding position: bind-assoc, pull-choice (`:522`),
  pull-exists (`:538`), pull-equate (`:551`).
- **`Force`** (`:567`): `force(thunk M)` → `M`, resolving the value through the environment.
- **`App`** (`:579`): beta `(λx. M)(V)` → `M[V/x]`; app-bind `(M to x. N)(V)` →
  `M to x. N(V↑)`.
- **`Choice`** (`:602`): flatten nested choices, drop `fail` branches, unwrap a singleton.
- **`Exists`** (`:634`): `exists x. fail` → `fail`.
- **`Equate`** (`:642`): `fail` body → fail; reflexivity (`V =:= V. M` → `M`); cycle (via
  `val_contains`) → fail; hoist `Exists`/`Choice` out of the body (eq-exists, eq-choice); and
  the **parameter laws** decomposing matching constructors (`Succ`/`Succ`, `Cons`/`Cons`,
  `Pair`/`Pair`, `Inl`/`Inl`, `Inr`/`Inr`) or failing on clashes (`Succ`/`Zero`, `Cons`/`Nil`,
  `Inl`/`Inr`), all over `deep_resolve`d operands (`:689-742`).
- **`Lambda`** (`:750`): `λx. fail` → `fail`; push the lambda into a `Choice`; swap with an
  inner `Exists` (lam-exists, via `swap_comp`); hoist an inner `Equate` whose operands do not
  mention `x` (lam-equate).
- **Eliminators** `Ifz` (`:797`), `Match` (`:815`), `Case` (`:835`): `deep_resolve` the
  scrutinee; if it is a known constructor, beta-reduce into the matching branch (substituting
  the payload), otherwise leave the eliminator in place.

> **Also fixed:** the `resolve_val` pass-through wrapper was deleted in favour of `deep_resolve`
> ([[deep-review]] §C5); `count_nodes` is used only behind the `opt-stats` feature (§C4).

A `#[cfg(test)]` suite (`:856-1178`) pins each rule (beta, eta, pull-choice, equate
decomposition, …) with small hand-built terms.

Related: [[pipeline]], [[de-bruijn]], [[cbpv]], [[mterms]], [[translate]], [[eval]].
