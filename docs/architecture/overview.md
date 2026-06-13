---
title: Overview
tags: [architecture]
updated: 7972077
---

# Overview

gweek is an interpreter for a small **functional-logic** language: functional in that
programs are pattern-matching equations over first-order data, logical in that they can
introduce **logic variables** (`exists x :: T`), constrain them by **unification**
(`lhs =:= rhs`), branch **non-deterministically** (`a <> b`), and **search** for all
solutions.

The implementation is organised as a classic pipeline feeding an **abstract machine**:

```
source text
   │  parser/         chumsky combinators → surface AST (Decl/Stmt/Expr/Type)
   ▼
surface AST
   │  type_check.rs   bidirectional checker; rejects ill-typed programs
   ▼
checked AST
   │  machine/translate.rs   lowering to Call-By-Push-Value, de Bruijn indices
   ▼
CBPV term (MComputation)
   │  machine/optimize.rs    optional peephole optimizer (-o)
   ▼
optimized term
   │  machine/eval.rs        a search strategy drives many copies of the machine
   ▼
solutions
```

See [[pipeline]] for the stage-by-stage walk-through with `file:line` anchors.

## Why an abstract machine

Evaluation is **not** a recursive `eval` function. Instead the program is compiled to a
[[cbpv|Call-By-Push-Value]] term and run on an explicit-state machine ([[step]]). A
machine state ([[step|`Machine`]], `step.rs:60`) bundles:

- a **computation closure** `cclos` — the term being run, paired with its [[env|environment]];
- a **stack** of continuation frames (`step.rs:34`);
- a **logic environment** [[lvar|`lenv`]] — bindings of logic variables;
- a **suspension environment** [[senv|`senv`]] — delayed `let` computations.

Making the state explicit is what lets gweek do logic programming: at a branch point the
machine is simply **cloned**, and each clone explores one alternative. The [[search-strategies|scheduler]]
decides the order. A recursive evaluator could not be paused, copied, and resumed this way.

## The two big representation choices

1. **Everything is arena-allocated.** Terms, environments, and stacks live in a single
   `bumpalo::Bump` for the whole run (`eval.rs:29`). Allocation is a pointer bump; closures
   are thin pointers, so cloning a machine at a branch point is cheap. The trade-off is that
   the arena is never reclaimed mid-run — see [[deep-review]] §P3.

2. **A value/computation split** ([[cbpv]]). [[mterms|`MValue`]] is inert data (naturals,
   lists, pairs, sums, thunks); [[mterms|`MComputation`]] is everything that *does* something
   (returns, binds, forces, branches, unifies). This split is what makes evaluation order —
   and therefore the search — explicit and controllable.

## Module map

| Area | Modules | Page |
|---|---|---|
| Frontend | `parser/*` | [[parser]] |
| Types | `type_check.rs`, `machine/value_type.rs` | [[type-checker]], [[type-system]] |
| Lowering | `machine/translate.rs` | [[translate]] |
| Optimizer | `machine/optimize.rs` | [[optimizer]] |
| Machine core | `machine/{mterms,step,eval}.rs` | [[mterms]], [[step]], [[eval]] |
| Logic engine | `machine/{unify,lvar,union_find}.rs` | [[unify]], [[lvar]], [[union-find]] |
| Laziness | `machine/{senv,vclosure,env}.rs` | [[senv]], [[vclosure]], [[env]] |
| Config / entry | `machine/config.rs`, `main.rs`, `lib.rs` | [[config]], [[main-and-lib]], [[cli]] |

## What gweek deliberately is not

A research interpreter, not a production one. It favours a clear operational story over
speed and surfaces many internal-invariant violations as `panic!` rather than typed errors
([[deep-review]] §A4). The performance characteristics (copy-on-write backtracking,
unbounded arena growth) are documented, not hidden — see [[deep-review]] §P2–P3.
