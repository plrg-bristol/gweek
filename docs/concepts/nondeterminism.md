---
title: Non-determinism
tags: [concept]
---

# Non-determinism

A gweek program describes a *search tree*, not a single execution. Most machine steps are
deterministic — one state, one successor. Some steps **branch**, and the set of leaves of the
resulting tree is the set of solutions. Two things branch:

## 1. Explicit choice: `a <> b`

Surface `Stmt::Choice`, lowered to `MComputation::Choice(&[..])` ([[mterms]]). The step
(`step.rs:233`) turns a choice of *n* alternatives into *n* machine states, each continuing
with one alternative and a **clone** of the logic and suspension environments so the branches
don't interfere (`step.rs:248-271`). Two degenerate cases:

- `Choice(&[])` is **failure** — `Step::Fail`, which prunes the branch (`step.rs:235`). The
  surface keyword `fail` lowers to exactly this (`translate.rs:396`).
- `Choice` of one alternative just continues, no branch.

## 2. Logic-variable case splits

When an eliminator ([[cbpv|`Ifz`/`Match`/`Case`]]) scrutinises an unbound
[[logic-variables|logic variable]], its shape is unknown, so the machine **guesses every
constructor**, one per branch:

| Eliminator | Branches | Code |
|---|---|---|
| `Ifz` (Nat) | `x = 0` ‖ `x = S(fresh)` | `step.rs:363-405` |
| `Match` (List) | `x = []` ‖ `x = (fresh:fresh)` | `step.rs:449-494` |
| `Case` (Sum) | `x = inl(fresh)` ‖ `x = inr(fresh)` | `step.rs:539-587` |

Each branch binds the variable to the guessed shape (with fresh sub-variables) in a cloned
`lenv` and continues. This is the engine of generative search: `exists xs :: [Nat]. … case xs …`
will enumerate lists of every length.

> Because the natural and list splits introduce an *unbounded* family of shapes (`0,1,2,…`;
> lists of every length), a branch can recurse forever. Whether the search still terminates
> depends entirely on the [[search-strategies|strategy]] — this is the central reason `--bfs`
> / `--fair` exist.

## How branches are scheduled

`step` reports a branch as `Step::Branch(SmallVec<[Machine; 2]>)` (`step.rs:14`). The
[[step|`run_to_branch`]] loop runs deterministic steps tight and only hands control back to
the scheduler at a branch or at completion (`step.rs:73`). The [[eval|scheduler]] then decides
the order branches are explored — depth-first, breadth-first, or fair — see
[[search-strategies]]. The same tree, explored in different orders, finds the same solutions
but with very different termination and memory behaviour.

## Pruning

A branch dies when a [[unification|unification]] fails (`step.rs:311`, `Err(_) => Step::Fail`)
or an explicit `fail` / empty choice is reached. The interpreter offers `absurd`-style helpers
in programs to prune deliberately; the practical art of pruning *early* (forcing constraints
before generating more candidates) is covered in [[suspensions-and-forcing]].

Related: [[search-strategies]], [[step]], [[eval]], [[logic-variables]], [[unification]].
