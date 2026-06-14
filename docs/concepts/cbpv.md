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
- **Computations** (`MComputation`, `mterms.rs:87`) are things that run: `Return`, `Bind`,
  `Force`, `Lambda`, `App`, `Choice`, `Exists`, `Equate`, `Rec`, and the eliminators
  `Ifz` / `Match` / `Case`.

## The two coercions

Values and computations are bridged by a dual pair:

| Coercion | Term | Meaning |
|---|---|---|
| computation → value | `Thunk(c)` (`mterms.rs:23`) | freeze a computation into a value you can pass around |
| value → computation | `Force(v)` (`mterms.rs:110`) | run a thunked computation |

So a gweek function is a **thunk of a `Lambda`** ([[translate|`translate_func`]],
`translate.rs:342`): calling it means `Force`-ing the thunk and then `App`-lying arguments.

## Sequencing is explicit: `Return` / `Bind`

There is no implicit "evaluate this sub-expression first." A computation that produces a
value uses `Return(v)` (`mterms.rs:105`); to use that value you must `Bind` it:

```
Bind { comp, cont }     -- run comp; bind its returned value at index 0 of cont's env
```

`Bind` (`step.rs:201`) is the workhorse: the surface language's nested data constructors all
compile to chains of `Bind … Return` so that each sub-result is named before it is used
([[translate]]). It is also where **laziness** enters: a non-`Return` `comp` is *suspended*
rather than run, unless `--strict` is set ([[suspensions-and-forcing]]).

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

Related: [[mterms]] (the term types), [[step]] (how each form steps), [[translate]] (how
surface syntax becomes CBPV), [[de-bruijn]] (variable representation).
