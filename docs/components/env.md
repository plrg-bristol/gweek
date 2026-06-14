---
title: env.rs — de Bruijn value environment
tags: [component, stub]
source: src/machine/env.rs
commit: d83302b
---

# `env.rs` *(stub — expand on demand)*

`Env<'a>` (`env.rs:14`) is the runtime variable environment: a persistent cons-list of
[[vclosure|`VClosure`]]s backed by the arena, indexed by [[de-bruijn|de Bruijn]] position.
Because `Env` is just a pointer to its head cell, it is `Copy` and O(1) to clone — which is
what makes cloning a [[step|machine]] at a [[nondeterminism|branch]] cheap.

**API:** `empty(arena)` (`:23`); `lookup(i)` (`:27`) walks `i` cells down; `extend_val`
(`:44`), `extend_lvar(ident: LVar)` (`:52`), `extend_susp(ident: SuspId)` (`:56`) push a value
/ [[lvar|logic-var]] / [[senv|suspension]] closure at the head.

**Subtlety.** `extend_val` **dealiases**: if the pushed value is itself a `Var`, it follows
the variable chain through the given env instead of adding another indirection layer (`:44-50`).
This eager variable resolution was made the default in commit `da38763`; [[deep-review]]
steering notes call it load-bearing.

Related: [[de-bruijn]], [[vclosure]], [[step]], [[lvar]], [[senv]].
