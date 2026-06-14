---
title: CLI reference
tags: [reference]
source: src/main.rs
commit: 6ec7c97
---

# CLI reference

```
gweek [OPTIONS] <source_file>
```

Flags are parsed in `main.rs:27-72` and used to construct a [[config|`Config`]]. The
corresponding WASM parameters are in [[main-and-lib|`lib.rs`]].

## Search strategy

Pick at most one. The flags are order-independent; if more than one is given the last wins
(`main.rs:39-42`). When **no** strategy flag is given the default is `--bfs` (`main.rs:28`),
which is also what `--help` labels "(default)". The trade-offs are explained in
[[search-strategies]].

| Flag | Strategy | Notes |
|---|---|---|
| `--bfs` | Breadth-first | The actual default. Complete and fair, memory-heavy. |
| `--dfs` | Depth-first | Fast and lean, incomplete on infinite branches. |
| `--iddfs` | Iterative deepening | Complete, low memory; re-explores, with exact per-frontier counting (§B8). |
| `--fair` | Fair round-robin DFS | Complete, DFS-speed, no re-exploration. Best general-purpose choice. |

## Other flags

| Flag | Effect | Code |
|---|---|---|
| `-o` | Enable the peephole [[optimizer]] | `main.rs` → [[pipeline]] step 4 |
| `--timeout <N>` | Wall-clock timeout in seconds (default 60) | checked inside [[step|`run_to_branch`]] too, so divergent loops honour it (§B9 fixed) |
| `--first` | Stop after the first solution | [[eval|`record_solution`]] / `cfg.first_only` |
| `--strict` | Evaluate `let` RHS before binding (no [[suspensions-and-forcing|suspensions]]) | [[step|`Bind`]] `step.rs:201` |
| `--no-occurs-check` | Skip the [[unification#occurs-check|occurs check]] (faster, unsound) | `unify.rs:37,45`; a resulting cyclic term is reported, not crashed (§B13 fixed) |
| `--help` / `-h` | Usage | |

## Example

```
$ gweek --fair --first examples/coins.gwk
> [10, 10, 10, 10, 10]
>>> 1 solutions
```

See [[examples]] for the bundled programs, and the [web playground](https://plrg-bristol.github.io/gweek/)
which exposes the same options. The WASM entry points take each of these as an explicit
parameter (`run_gweek`/`run_gweek_batch`, `lib.rs:104,132`); the strategy is passed as a string
(`"dfs"`/`"iddfs"`/`"fair"`, anything else defaulting to BFS, `lib.rs:29-34`).

Related: [[config]], [[search-strategies]], [[main-and-lib]], [[examples]].
