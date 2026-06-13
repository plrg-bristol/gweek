---
title: vclosure.rs — value closures
tags: [component, stub]
source: src/machine/vclosure.rs
updated: 7972077
---

# `vclosure.rs` *(stub — expand on demand)*

`VClosure<'a>` (`vclosure.rs:11`) is how the machine refers to a value whose resolution may be
deferred. Three variants: `Clos { val, env }` (a concrete value in its
[[env|environment]]), `LogicVar { ident }` (an unresolved [[logic-variables|logic variable]]),
`Susp { ident }` (a [[suspensions-and-forcing|suspension]]). This indirection is what lets
[[unify|unification]] and the [[step|eliminators]] discover that "a value" is actually an
unknown to branch on.

**The two closing operations:**

- `close_head(lenv, senv)` (`:51`) — resolve *one level*: follow `Var` indices through the
  env, look up logic vars and suspensions, and stop at the first concrete head form (or return
  `Err(SuspAt)` if it hits an unforced suspension). The workhorse called by [[step]] and
  [[unify]] before they inspect a value's shape.
- `close(arena, lenv, senv)` (`:69`) — resolve *fully* to a ground `MValue` for output,
  recursively closing every sub-closure. Returns `None` when it can't (notably a residual
  free logic variable of non-`Unit` type → [[deep-review]] §B7).

`occurs_lvar` (`:22`) implements the [[unification#occurs-check|occurs check]].

Related: [[logic-variables]], [[unification]], [[step]], [[env]], [[lvar]], [[senv]].
