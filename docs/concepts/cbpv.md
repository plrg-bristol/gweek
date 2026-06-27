---
title: Call-By-Push-Value
tags: [concept]
---

# Call-By-Push-Value (CBPV)

CBPV is the intermediate language gweek compiles to. Its slogan is *"a value **is**, a
computation **does**."* Everything in the machine is split into two syntactic categories,
and that split is what makes evaluation order — and therefore the search — explicit.

The two categories are defined in [[mterms]] (`mterms.rs`):

- **Values** (`MValue`, `mterms.rs:12`) are inert data: `Unit`, `Nat`, `Zero`/`Succ`, `Pair`,
  `Inl`/`Inr`, `Nil`/`Cons`, de Bruijn `Var`, and `Thunk` (a frozen computation). Naturals
  have two representations — a packed `Nat(u64)` literal and the unary `Zero`/`Succ` spine that
  pattern-matching and unification build incrementally; both render via `to_nat` (`mterms.rs:55`).
- **Computations** (`MComputation`, `mterms.rs:87`) are things that run: `Return`, `Bind`, `Need`,
  `Force`, `Lambda`, `App`, `Choice`, `Exists`, `Equate`, `Rec`, and the eliminators
  `Ifz` / `Match` / `Case`.

## The two coercions

Values and computations are bridged by a dual pair:

| Coercion | Term | Meaning |
|---|---|---|
| computation → value | `Thunk(c)` (`mterms.rs:23`) | freeze a computation into a value you can pass around |
| value → computation | `Force(v)` (`mterms.rs:110`) | run a thunked computation |

So a gweek function is a **thunk of a `Lambda`** ([[elaborate|`elaborate_func`]],
`elaborate.rs:342`): calling it means `Force`-ing the thunk and then `App`-lying arguments.

## Sequencing is explicit: `Return` / `Need` / `Bind`

There is no implicit "evaluate this sub-expression first." A computation that produces a
value uses `Return(v)` (`mterms.rs:105`); to use that value you must sequence it into a
continuation, and gweek has two ways to do so:

```
Need { comp, cont }     -- by-need: suspend comp; bind a thunk for it at index 0 of cont's env
Bind { comp, cont }     -- strict:  run comp to a value now; bind that value at index 0
```

`Need` (`step.rs:259`) is the workhorse. gweek is lazy, so the surface language's nested data
constructors — and the bare surface `let x = e` — all compile to chains of `Need … Return` via
[[elaborate|`seq`]], so that each sub-result is named before it is used. This is where
**laziness** enters: a non-`Return` `comp` is *suspended* rather than run, and forced only on
demand ([[suspensions-and-forcing]]) — which is what lets narrowing prune the search. Its
strict counterpart `Bind` (`step.rs:228`) runs `comp` eagerly and is reached only by the
explicit `let strict x = e`.

## Eliminators

The three eliminators take a *value* and a continuation per shape:

- `Ifz { num, zk, sk }` — naturals (`step.rs:362`)
- `Match { list, nilk, consk }` — lists (`step.rs:448`)
- `Case { sum, inlk, inrk }` — sums (`step.rs:527`)

Each first [[vclosure|head-closes]] its scrutinee. When the scrutinee turns out to be an
unresolved [[logic-variables|logic variable]], the eliminator does not get stuck — it
**branches**, guessing each possible shape ([[nondeterminism]]). That single mechanism is
how "pattern-matching on an unknown" becomes search.

## Why gweek uses CBPV

Logic programming needs to *pause, copy, and resume* evaluation at branch points. CBPV gives
a term language where the next step is always determined by the head constructor, with no
hidden control flow — so the machine state ([[step]]) can be made fully explicit and cloned.
A direct recursive evaluator could not be snapshotted this way.

Related: [[mterms]] (the term types), [[step]] (how each form steps), [[elaborate]] (how
surface syntax becomes CBPV), [[de-bruijn]] (variable representation).
