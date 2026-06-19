---
title: Overview
tags: [architecture]
---

# Overview

gweek is an interpreter for a small **functional-logic** language: functional in that programs
are pattern-matching equations over first-order data, logical in that they can introduce **logic
variables** (`exists x :: T`), constrain them by **unification** (`lhs =:= rhs`), branch
**non-deterministically** (`a <> b`), and **search** for all solutions.

The implementation is a classic pipeline feeding an **abstract machine**:

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
CBPV term
   │  machine/optimize.rs    optional peephole optimizer (-o)
   ▼
optimized term
   │  machine/eval.rs        a search strategy drives many copies of the machine
   ▼
solutions
```

For per-module detail, read the rustdoc: `cargo doc --no-deps --document-private-items --open`.

## Why an abstract machine

Evaluation is **not** a recursive `eval` function. Instead the program is compiled to a
[[cbpv|Call-By-Push-Value]] term and run on an explicit-state machine. A machine state bundles a
**computation closure** (the term being run, paired with its environment), a **stack** of
continuation frames, a **logic environment** of logic-variable bindings, and a **suspension
environment** of delayed `let` computations.

Making the state explicit is what lets gweek do logic programming: at a branch point the machine
is simply **cloned**, and each clone explores one alternative; the [[search-strategies|scheduler]]
decides the order. A recursive evaluator could not be paused, copied, and resumed this way.

## The two big representation choices

1. **Everything is arena-allocated.** Terms, environments, and stacks live in a single
   `bumpalo::Bump` for the whole run. Allocation is a pointer bump; closures are thin pointers,
   so cloning a machine at a branch point is cheap. The trade-off is that the arena is never
   reclaimed mid-run — see [[deep-review]] §P3.

2. **A value/computation split** ([[cbpv]]). `MValue` is inert data (naturals, lists, pairs,
   sums, thunks); `MComputation` is everything that *does* something (returns, binds, forces,
   branches, unifies). This split is what makes evaluation order — and therefore the search —
   explicit and controllable.

## What gweek deliberately is not

A research interpreter, not a production one. It favours a clear operational story over speed.
User-reachable errors flow through typed channels; the `panic!`s that remain are true machine
invariants ([[deep-review]] §A4, tail). The **performance** characteristics it documents are
still open: copy-on-write backtracking state ([[deep-review]] §P2) and unbounded arena growth
(§P3) are not yet redesigned.
