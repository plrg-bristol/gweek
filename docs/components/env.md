---
title: env.rs — de Bruijn value environment
tags: [component]
source: src/machine/env.rs
commit: 6ec7c97
---

# `env.rs`

`Env<'a>` (`env.rs:14`) is the runtime variable environment: a persistent cons-list of
[[vclosure|`VClosure`]]s backed by the bump arena, indexed by [[de-bruijn|de Bruijn]] position.
The list cells are an internal `EnvInner` enum — `Nil` or `Cons(VClosure, Env)` (`:6-9`) — and
`Env` is a single `&'a EnvInner` pointer to the head cell. Because it is just a pointer, `Env` is
`Copy` and O(1) to clone, which is what makes cloning a [[step|machine]] at a
[[nondeterminism|branch]] cheap. (`Debug` is hand-written to print `Env(...)`, `:16-20`, since the
shared structure is not worth dumping.)

## API

- `empty(arena)` (`:23-25`) allocates a `Nil` cell.
- `lookup(i) -> Option<VClosure>` (`:27-42`) walks `i` cons cells down the list and returns the
  closure there, or `None` if the index runs off the end.
- `extend_val(arena, val, env)` (`:44-50`) pushes a value closure at the head — see the dealiasing
  subtlety below.
- `extend_lvar(arena, ident: LVar)` (`:52-54`) pushes a `VClosure::LogicVar` for a
  [[lvar|logic variable]].
- `extend_susp(arena, ident: SuspId)` (`:56-58`) pushes a `VClosure::Susp` for a
  [[senv|suspension]].

Each `extend_*` allocates one fresh `Cons` cell pointing at the current head, so the old `Env`
remains valid — sibling branches share the tail.

## Subtlety: `extend_val` dealiases

`extend_val` does not blindly push `Clos { val, env }`. If `val` is itself a `Var(i)`, it follows
the variable chain through the supplied env until it reaches a non-`Var` closure, and pushes
*that* (`:46-49`). This collapses chains of indirection eagerly, so a later `lookup` lands on a
real closure in one hop rather than threading through aliased slots. This eager variable
resolution was made the default in commit `da38763` (the `--eager-vars` flag was removed);
[[deep-review]] steering notes call it load-bearing for correctness of the closing operations.

Under the `opt-stats` feature, `count_nodes` (`:60-75`) totals the `MValue` node count reachable
through `Clos` entries, for [[optimizer]] instrumentation.

Related: [[de-bruijn]], [[vclosure]], [[step]], [[lvar]], [[senv]].
