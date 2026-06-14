---
title: vclosure.rs — value closures
tags: [component, stub]
source: src/machine/vclosure.rs
commit: d83302b
---

# `vclosure.rs` *(stub — expand on demand)*

`VClosure<'a>` (`vclosure.rs:11-15`) is how the machine refers to a value whose resolution may
be deferred. Three variants: `Clos { val, env }` (a concrete value in its [[env|environment]]),
`LogicVar { ident: LVar }` (an unresolved [[logic-variables|logic variable]]),
`Susp { ident: SuspId }` (a [[suspensions-and-forcing|suspension]]). This indirection is what
lets [[unify|unification]] and the [[step|eliminators]] discover that "a value" is actually an
unknown to branch on.

**The two closing operations:**

- `close_head(lenv, senv) -> Result<VClosure, SuspAt>` (`:149`) — resolve *one level*: follow
  `Var` indices through the env, look up logic vars and suspensions, and stop at the first
  concrete head form (or return `Err(SuspAt)` if it hits an unforced suspension). The workhorse
  called by [[step]] and [[unify]] before they inspect a value's shape.
- `close(lenv, senv) -> Result<Closed, CyclicTerm>` (`:172`) — resolve *fully* to a ground
  answer term for output. It is **iterative**, driven by an explicit work stack of `Task`s
  (`:262-273`) rather than recursion, with a depth guard `MAX_CLOSE_DEPTH = 1<<16` (`:45`,
  checked at `:181`) so a cyclic term reports `CyclicTerm` instead of overflowing the stack
  ([[deep-review]] §B13, fixed). The result is a `Closed` enum (`:24-34`).

**Residual free variables.** An unbound logic variable in an answer no longer drops the
solution. `close` emits `Closed::Unit` for an unbound variable of type `Unit`, and otherwise a
`Closed::Free(lenv.root(ident))` placeholder (`:218-226`) — rendered `_<id>`, keyed on the
canonical [[union-find|root]] so unified variables share one name ([[deep-review]] §B7, fixed).

`occurs_lvar` (`:118`) implements the [[unification#occurs-check|occurs check]].

Related: [[logic-variables]], [[unification]], [[step]], [[env]], [[lvar]], [[senv]].
