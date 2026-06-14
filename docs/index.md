---
title: gweek — developer wiki
tags: [meta]
---

# gweek

**gweek** is a functional-logic programming language. Its interpreter is a
[Call-By-Push-Value](https://en.wikipedia.org/wiki/Call-by-push-value) abstract
machine (~6,400 lines of Rust) supporting existential search over first-order data
(naturals, lists, pairs, sums), finitary non-determinism, and unification.

```
change :: Nat -> [Nat]
change n = case n of
    Z -> []
  | S m -> let c = coin in
            exists rest :: Nat.
            add c rest =:= n.
            c : change rest.

change 20.            -- how many ways to make 20 from coins {1,2,10}?
```

This wiki documents the *implementation*. It is maintained by an LLM that tracks the
source tree — see [[AGENTS|the schema]] for how it works and how to keep it in sync.
New here? Start with [[overview]], then [[pipeline]].

> **Try it:** in-browser playground at <https://plrg-bristol.github.io/gweek/>.

## Architecture

- [[overview]] — what gweek is and how the interpreter is organised
- [[pipeline]] — the journey of a program: parse → type-check → translate → optimize → evaluate

## Concepts

- [[cbpv]] — Call-By-Push-Value: the value/computation split the machine is built on
- [[logic-variables]] — existentials, union-find, and how unbound variables are represented
- [[unification]] — the `=:=` constraint solver
- [[suspensions-and-forcing]] — lazy `let` bindings and when they get forced
- [[nondeterminism]] — choice (`<>`), failure, and logic-variable case splits
- [[search-strategies]] — BFS / DFS / IDDFS / Fair, and when to use each
- [[de-bruijn]] — nameless variable representation across translation and the machine
- [[type-system]] — the bidirectional type checker and the runtime type lattice

## Components (by source module)

The machine core:

- [[mterms]] — `src/machine/mterms.rs` · the CBPV term language (`MValue` / `MComputation`)
- [[step]] — `src/machine/step.rs` · the single-step transition function
- [[eval]] — `src/machine/eval.rs` · the search schedulers
- [[unify]] — `src/machine/unify.rs` · the unification algorithm
- [[translate]] — `src/machine/translate.rs` · surface AST → CBPV
- [[optimizer]] — `src/machine/optimize.rs` · the equational CBPV optimizer

Frontend & types:

- [[parser]] — `src/parser/` · chumsky combinators → surface AST
- [[type-checker]] — `src/type_check.rs` · bidirectional checker with HM-style instantiation

Runtime support:

- [[lvar]] — `src/machine/lvar.rs` · logic-variable environment
- [[union-find]] — `src/machine/union_find.rs` · variable aliasing
- [[senv]] — `src/machine/senv.rs` · the suspension store
- [[env]] — `src/machine/env.rs` · the de Bruijn value environment
- [[vclosure]] — `src/machine/vclosure.rs` · value closures, forcing, and `close`
- [[value-type]] — `src/machine/value_type.rs` · the runtime type lattice
- [[config]] — `src/machine/config.rs` · runtime knobs (the in-memory CLI flags)

Entry points:

- [[main-and-lib]] — `src/main.rs`, `src/lib.rs` · CLI entry and WASM bindings

## Reference

- [[cli]] — command-line flags
- [[grammar]] — surface syntax
- [[examples]] — the programs in `examples/`

## Review

- [[deep-review]] — a multi-reviewer audit (correctness, simplicity, architecture, performance)
