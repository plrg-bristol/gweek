---
title: eval.rs — the search schedulers
tags: [component, machine]
source: src/machine/eval.rs
updated: 7972077
---

# `eval.rs`

Owns the **search**: it creates the runtime arena, builds the initial machine, and runs one
of four [[search-strategies|scheduling strategies]] that drive [[step|`run_to_branch`]] over
the [[nondeterminism|search tree]], recording solutions.

## Entry points (`eval.rs:27-91`)

All four create a fresh `Bump` and import the top-level function values into the initial
[[env|environment]] (`import_env`, `:94`):

| Function | Used by | Output |
|---|---|---|
| `eval` (`:27`) | CLI | prints `> solution` lines and a summary |
| `eval_collect` (`:42`) | WASM batch | returns all solutions as one `String` |
| `eval_streaming` (`:61`) | WASM streaming | calls a callback per solution |
| `run` (`:80`) | tests | returns the solution count |

They funnel into `run_internal` (`:102`), which dispatches on [[config|`Strategy`]] to one of
the four loops below and returns `(solutions, timed_out)`.

> **Architecture note.** `run` (the test entry) takes `strategy` explicitly but reads other
> options (`strict`, `occurs_check`, `first_only`) and the deadline from the
> [[config|thread-local `Config`]], which it does not set — so a test can run `Dfs` while the
> global still says `Bfs`. [[deep-review]] §A2 recommends threading one immutable `&Config`
> instead of the thread-local.

## The four loops

Each pulls a machine, calls `run_to_branch`, records `Done` machines via `record_solution`
(`:130`), and schedules the rest. A timeout is checked every 1024 iterations
(`iters & 1023 == 0`).

- **`eval_bfs`** (`:143`) — two vectors, *current* and *next* level; drains current into next.
  Complete and fair, but the frontier (and arena) can blow up. Default strategy.
- **`eval_dfs`** (`:169`) — a stack; pushes branch results reversed to preserve left-to-right
  order. Fast and lean, incomplete on infinite branches.
- **`eval_iddfs`** (`:191`) — repeated depth-limited DFS, doubling the limit until a round
  prunes nothing. Depth only increments at real branches (`is_branch`, `:209`).
  > **Known issue.** It dedups solutions across rounds with a `HashSet<String>` keyed on the
  > *rendered* output (`:214`), so two genuinely distinct derivations that print the same
  > string collapse to one — undercounting versus BFS/DFS ([[deep-review]] §B8).
- **`eval_fair`** (`:237`) — round-robin over a queue of work-stacks; each gets a `QUOTA` of
  10,000 steps (`:238`) before yielding to the back. At a branch it spreads alternatives
  across the queue for fairness (`:257-273`). Complete with DFS-like speed — the recommended
  general default.

## Recording and rendering solutions

`record_solution` (`:130`) fires only when the machine halted on a `Return(v)`; it
[[vclosure|closes]] `v` to a ground term via `output` (`:293`) and stops early if
`config().first_only`. Closing can return `None` — in particular for answers with a residual
free [[logic-variables|logic variable]] of non-`Unit` type, which are then silently dropped
([[deep-review]] §B7).

Related: [[search-strategies]], [[step]], [[nondeterminism]], [[config]], [[vclosure]].
