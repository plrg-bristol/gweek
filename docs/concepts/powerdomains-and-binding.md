---
title: Powerdomains and binding
tags: [concept]
---

# Powerdomains and binding

> **Background.** gweek's nondeterminism has a unit `fail` (the empty computation,
> [[nondeterminism|`Choice([])`]]) and a binary choice `<>`. Sequencing is [[cbpv|`Need`/`Bind`]].
> Two equations one would like of `fail` and sequencing are the **zero laws**:
>
> - **right-zero**  `M to x. fail  =  fail`
> - **left-zero**   `fail to x. M  =  fail`
>
> Both hold in the **lower (Hoare) powerdomain**. The catch is that you cannot also be
> *termination-sensitive* — distinguish a divergent search `Ω` from `fail` — while keeping
> both, under any sequential evaluator. This note records why, and what gweek does about it.

## The collapse theorem

Work in any model whose bind is **strict in its first argument** — `⊥ >>= k = ⊥` — which is
exactly what a sequential evaluator does: you must run `M` before you can know what to bind `x`
to. Instantiate right-zero at `M := ⊥`:

```
⊥  =  ⊥ >>= (λ_. fail)     -- strictness of bind
   =  fail                  -- right-zero
```

So **strict bind + right-zero ⟹ `⊥ = fail`**. Termination-sensitivity (`⊥ ≠ fail`) is
inconsistent with right-zero the moment bind is strict. The contrapositive is the design
constraint: *to keep right-zero termination-sensitively you must make bind non-strict (lazy).*
That is what [[cbpv|`Need`]] does — and the price is that a non-strict bind cannot see a `fail`
on its left when the body diverges, so it loses left-zero. The two laws are the two horns;
sequential bind impales itself on one or the other.

## The sequentiality obstruction, demonstrated

Take a divergent witness `go` (`loop n = loop n. go = loop Z.`) and run all four corners.
`let` is by-need ([[cbpv|`Need`]]); `let strict` is CBV ([[cbpv|`Bind`]]):

| witness (something diverges) | `let` (by-need) | `let strict` (CBV) | law |
|---|---|---|---|
| `let _ = go in fail` | **halts → `fail`** ✓ | diverges ✗ | right-zero `M to x. fail = fail` |
| `let _ = fail in go` | diverges ✗ | **halts → `fail`** ✓ | left-zero `fail to x. M = fail` |

Each strategy validates exactly one law termination-sensitively, and they are mirror images.
To validate *both* an evaluator of `A to x. B` would have to return `fail` as soon as **either**
`A` or `B` reduces to `fail`, while the other may diverge — a **parallel-fail** operator. It is
not sequentially definable (a one-redex-at-a-time machine must commit to one side first), and it
is not even schedulable when `x ∈ fv(B)` (you cannot start `B` before `A` produces the value
bound to `x`). This is Plotkin's parallel-or obstruction in nondeterministic clothing.

## Where undecidability actually enters

The *model* question above is a decidable impossibility. But *verifying the law on a program* is
genuinely undecidable: termination-sensitively, `go to x. fail = fail` iff `go` halts, so deciding

```
M to x. fail   ≃   fail        (≃ termination-sensitive observational equivalence)
```

reduces to the halting problem. So "does this program respect right-zero?" is Rice-undecidable,
even though "can a termination-sensitive model satisfy right-zero?" is a one-line *no*.

## The powerdomain dictionary

The right-zero law for divergent `M` is exactly the axiom that separates the powerdomains:

| powerdomain | observation | `⊥` vs `fail` | right-zero | `K <> K = K` |
|---|---|---|---|---|
| **lower / Hoare** | may-converge | identified | ✓ | ✓ |
| **convex / Plotkin** | termination-sensitive | distinct | ✗ | ✓ |

The lower powerdomain *buys* both zero laws precisely *by* identifying divergence with failure;
the convex powerdomain *pays* for termination-sensitivity precisely *by* giving up right-zero
(its bind is strict and it keeps `⊥ ≠ fail`, so by the collapse theorem it cannot have
right-zero). "Both laws **and** termination-sensitive" asks for a model strictly between the two,
which — sequentially — is not there.

## What gweek does

gweek is a **solution enumerator**, and its only real observation is *which solutions are
emitted*. Divergence is not observable except via [[cli|`--timeout`]], which is not a semantic
observation. So `⊥ = fail` is already true of gweek's observable behaviour, and the natural
specification is the **lower (Hoare) powerdomain / may-convergence**. Under that reading:

- **Both zero laws hold unconditionally**, and the by-need-vs-strict question is purely
  operational — both are adequate. By-need is the default because it discharges right-zero
  cheaply (it never starts `M` when the continuation fails) and prunes the search; `let strict`
  is a sound knob that discharges left-zero cheaply (it dies on the bound failure before the
  body). Neither is "more correct."
- **Adequacy requires a complete/fair search** — a solution exists iff it is eventually emitted —
  so that a divergence on one branch cannot hide a solution on another. [[search-strategies|BFS,
  Fair, and IDDFS]] are complete; **DFS is not**, and is inadequate for the lower powerdomain
  (a left divergence swallows solutions to its right). The [[suspensions-and-forcing|end-of-run
  drain]] is what secures left-zero operationally on the terminating fragment.

## Idempotency: set vs multiset

There is one residual choice. By default `5 <> 5` yields `{5, 5}` and `let x = (0 <> 1) in 5`
yields `{5, 5}` — gweek emits a **multiset**, so `<>` is *not* idempotent and the true model is
the **free nondeterminism monad**, not the lower powerdomain. The multiset monad still satisfies
both zero laws on the terminating fragment, but it has no clean fixpoint story, so it cannot host
the *divergent* zero laws that motivate this note.

If the lower powerdomain is the intended specification, then `<>` must be idempotent, which
operationally means **deduplicating the emitted solution set** — the observation *is* a set of
results, so you dedup what you observe. [[cli|`--distinct`]] turns this on: each distinct
rendered solution is emitted once, so `5 <> 5 = {5}` and `let x = (0 <> 1) in 5 = {5}`. The cost
is memory — the set of seen solutions is retained for the whole run (cf. the unbounded-frontier
hazard of [[search-strategies|BFS]]), so it is bounded only for finite solution sets, which is
gweek's intended domain anyway.

The decision is therefore explicit: leave `--distinct` off and call the model the *free
nondeterminism monad* (multiplicity is observable), or turn it on and call it the *lower
powerdomain* (the set of solutions is the observation). The zero laws hold either way; only
idempotency and the divergence story distinguish them.
