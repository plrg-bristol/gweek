---
title: Examples
tags: [reference]
source: examples/
commit: 6ec7c97
---

# Examples

The `examples/` directory holds runnable programs (`.gwk`, plus a couple of `.bll`). They
double as a tour of the language and as the basis for the integration tests in
[[main-and-lib|`main.rs`]] (`perm`, `find_list`, `nqueens`). Run any with e.g.
`gweek --fair examples/coins.gwk` — see [[cli]].

## Constraint search / puzzles

These are the showcase programs: generate candidates non-deterministically and prune with
[[unification|`=:=`]] constraints. The art of pruning *early* is [[suspensions-and-forcing]].

| File | What it does |
|---|---|
| `coins.gwk` | Coin-change: ways to make a total from coins {1, 2, 10} (the [[index|README]] example). |
| `nqueens.gwk`, `nqueens10.gwk` | N-queens placement (the worked example in [[suspensions-and-forcing]]). |
| `magic.gwk`, `magic_slow.gwk` | 3×3 magic square — fast (incremental) vs naive (generate-then-test). |
| `magic4.gwk`, `magic4_slow.gwk` | 4×4 magic square: incremental pick-and-prune vs naive generate-and-test. |
| `pythagorean.gwk` | Pythagorean triples via search. |
| `subset_sum.gwk` | Subset summing to a target. |
| `map_color.gwk` | Graph/map colouring. |
| `square1.gwk`, `square2.gwk` | Integer square root by search: `exists n :: Nat. mult n n =:= 16. n` (the two differ only in how `add` recurses). |

## List operations

| File | What it does |
|---|---|
| `perm.gwk`, `perm2.bll` | Permutations (test pins 720 solutions). |
| `sort.gwk` | Sorting as search. |
| `find_list.gwk` | Search over lists (test pins 462 solutions). |
| `head.gwk`, `last.gwk`, `no-last.gwk` | Head/last element relations. |
| `split.gwk` | Splits a natural into two addends: `exists x y. add x y =:= 100. (x, y)`. |
| `id.gwk` | Identity. |

## Non-determinism, laziness & edge cases

| File | What it does |
|---|---|
| `fair.gwk` | Exercises fair search ([[search-strategies]]). |
| `loop.gwk` | `exists x :: Nat. x =:= (S x). x.` — a self-referential constraint that diverges; `--timeout` now halts it even though it never branches ([[deep-review]] §B9, fixed). |
| `inert.gwk` | `exists x :: Nat. x.` — now reports a residual free variable `_<id>` ([[logic-variables|residual answers]], [[deep-review]] §B7, fixed; pinned by an [[eval|eval test]]). |
| `poke.gwk`, `spooky.gwk`, `test.gwk` | Assorted probes. |
| `fibonacci_search.bll` | Fibonacci via search (`.bll` syntax). |

> The descriptions are read from the programs themselves; the files carry no header comments.
> The three entries with pinned solution counts (`perm` → 720, `find_list` → 462, `nqueens` →
> 92) are asserted by the integration tests in `main.rs` (`main.rs:240-284`). Turning the
> remaining entries into full worked records (input → expected solutions → strategy notes) is
> good follow-up work.

Related: [[cli]], [[suspensions-and-forcing]], [[nondeterminism]], [[search-strategies]].
