---
title: vclosure.rs — value closures
tags: [component]
source: src/machine/vclosure.rs
commit: 6ec7c97
---

# `vclosure.rs`

`VClosure<'a>` (`vclosure.rs:11-15`) is how the machine refers to a value whose resolution may be
deferred. It is a `Copy` enum with three variants: `Clos { val, env }` (a concrete `MValue` in its
[[env|environment]]), `LogicVar { ident: LVar }` (an unresolved [[logic-variables|logic variable]]),
and `Susp { ident: SuspId }` (a [[suspensions-and-forcing|suspension]]). This indirection is what
lets [[unify|unification]] and the [[step|eliminators]] discover that "a value" is actually an
unknown to branch on or a thunk to force. `mk_clos(val, env)` (`:114-116`) is the `Clos`
constructor.

## The two closing operations

- `close_head(lenv, senv) -> Result<VClosure, SuspAt>` (`:149-165`) resolves *one level*. It
  loops, following `Var` indices through the env (`env.lookup`), chasing bound logic variables
  through [[lvar|`LogicEnv::lookup`]], and forcing suspensions via [[senv|`SuspEnv::lookup`]],
  stopping at the first concrete head form or at an *unbound* logic variable. If it meets a
  still-pending suspension, `senv.lookup` returns `Err`, which `?` propagates as `Err(SuspAt)`.
  This is the workhorse [[step]] and [[unify]] call before inspecting a value's shape; a returned
  `Err(SuspAt)` is what prompts a [[step|`reschedule`]].

- `close(lenv, senv) -> Result<Closed, CyclicTerm>` (`:172-259`) resolves *fully* to a ground
  answer term for output. It is **iterative**, driven by an explicit work stack of `Task`s
  (`:262-265`) with `Combine` markers (`:267-273`) doing a post-order assembly: `Resolve` tasks
  expand a closure and push child `Resolve`s plus a `Combine`, which later pops finished subterms
  off the `out` stack and builds the parent node. Using an explicit stack rather than native
  recursion means the depth bound is enforced regardless of stack-frame size. `MAX_CLOSE_DEPTH`
  is `1 << 16` (`:45`), checked per `Resolve` (`:181-183`); beyond it the term is assumed cyclic
  and `close` returns `Err(CyclicTerm)` (`:38-39`) instead of looping forever. Cyclic terms can
  only arise with `--no-occurs-check`. This is the [[deep-review]] §B13 fix (commit `af56c79`).

The result is a `Closed` enum (`:24-34`), the printable shape mirroring `MValue` plus a `Free`
placeholder. Its `Display` impl (`:47-79`) prints `Nat` numerals, collapses `Succ` chains and
`Cons` spines via the `to_nat`/`to_list` helpers (`:81-111`), and renders `Inl ()`/`Inr ()` as
`true`/`false`.

## Residual free variables

An unbound logic variable in an answer no longer drops the solution. When `close` hits an
unbound `LogicVar` (`:218-226`), it emits `Closed::Unit` for one of type `Unit`, and otherwise a
`Closed::Free(lenv.root(ident))` placeholder — printed `_<id>` (`:50`), keyed on the canonical
[[union-find|root]] so members of one unified class share a single name. This is [[deep-review]]
§B7, fixed in commit `af56c79`.

## Occurs check

`occurs_lvar(lenv, senv, ident) -> Result<bool, SuspAt>` (`:118-147`) implements the
[[unification#occurs-check|occurs check]]: it head-closes the value and recurses into every
sub-value looking for `ident`, returning `true` if the variable occurs within its own candidate
binding. It can also return `Err(SuspAt)` if a suspension blocks resolution. `MValue::Zero` is
still a handled case here (`:140`) and is mapped to `Closed::Nat(0)` in `close` (`:192`) — the
redundancy of `Zero` alongside `Nat` is [[deep-review]] §A3, **still open**.

Related: [[logic-variables]], [[unification]], [[step]], [[env]], [[lvar]], [[senv]].
