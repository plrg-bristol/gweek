---
title: eval.rs — the search schedulers
tags: [component, machine]
source: src/machine/eval.rs
commit: d83302b
---

# `eval.rs`

Owns the **search**: it creates the runtime arena, builds the initial machine, and runs one
of four [[search-strategies|scheduling strategies]] that drive [[step|`run_to_branch`]] over
the [[nondeterminism|search tree]], recording solutions.

## Entry points (`eval.rs:51-113`)

All take `cfg: &Config` explicitly (no thread-local — [[deep-review]] §A2, fixed), create a
fresh `Bump`, import the top-level function values into the initial [[env|environment]]
(`import_env`, `:116`), and compute an absolute deadline (`deadline_from`, `:27`):

| Function | Used by | Output |
|---|---|---|
| `eval` (`:51`) | CLI | prints `> solution` lines and a summary |
| `eval_collect` (`:65`) | WASM batch | returns all solutions as one `String` |
| `eval_streaming` (`:83`) | WASM streaming | calls a callback per solution |
| `run` (`:102`) | tests | returns the solution count |

They funnel into `run_internal` (`:124`), which dispatches on [[config|`Strategy`]] to one of
the four loops and returns `(solutions, timed_out)`.

## The four loops

Each pulls a machine, calls `run_to_branch(cfg, deadline)`, records `Done` machines via
`record_solution` (`:151`), and schedules the rest. Cheap deadline polling is centralized in a
`Clock` helper (`:34-48`, `expired()` reads `Instant::now()` only every 1024 ticks) —
[[deep-review]] §C6, fixed.

- **`eval_bfs`** (`:163`) — two vectors, *current* and *next* level; drains current into next.
  Complete and fair, but the frontier (and arena) can blow up. Default strategy.
- **`eval_dfs`** (`:192`) — a stack; pushes branch results reversed to preserve left-to-right
  order. Fast and lean, incomplete on infinite branches.
- **`eval_iddfs`** (`:217`) — repeated depth-limited DFS, doubling the limit until a round
  prunes nothing. It counts solutions found in the **frontier window** `[depth_limit/2,
  depth_limit)` (`:245-248`), so each solution is counted in exactly one round — no
  cross-round string dedup, and distinct derivations that render identically are no longer
  collapsed ([[deep-review]] §B8/§P4, fixed; pinned by a test at `:378`).
- **`eval_fair`** (`:263`) — round-robin over a queue of work-stacks; each gets a step `QUOTA`
  before yielding to the back, spreading branch alternatives across the queue for fairness.
  Complete with DFS-like speed — the recommended general default.

## Recording and rendering solutions

`record_solution` (`:151`) fires when the machine halted on a `Return(v)`; it
[[vclosure|closes]] `v` to a `Closed` answer via `output` (`:321`) and stops early if
`cfg.first_only`. An answer with a residual free [[logic-variables|logic variable]] is now
**reported** (as a `_<id>` placeholder), not dropped ([[deep-review]] §B7, fixed; test
`inert_reports_free_variable` at `:363`); a cyclic term renders as an error rather than
overflowing the stack (§B13).

Related: [[search-strategies]], [[step]], [[nondeterminism]], [[config]], [[vclosure]].
