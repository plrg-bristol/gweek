---
title: CLI reference
tags: [reference]
source: src/main.rs
updated: 7972077
---

# CLI reference

```
gweek [OPTIONS] <source_file>
```

Flags are parsed in `main.rs:28-72` and stored in a [[config|`Config`]]. The corresponding
WASM parameters are in [[main-and-lib|`lib.rs`]].

## Search strategy

Pick at most one; default is `--bfs`. The trade-offs are explained in [[search-strategies]].

| Flag | Strategy | Notes |
|---|---|---|
| `--bfs` | Breadth-first | Default. Complete and fair, memory-heavy. |
| `--dfs` | Depth-first | Fast and lean, incomplete on infinite branches. |
| `--iddfs` | Iterative deepening | Complete, low memory; re-explores and dedups (see §B8). |
| `--fair` | Fair round-robin DFS | Complete, DFS-speed, no re-exploration. **Recommended default.** |

## Other flags

| Flag | Effect | Code |
|---|---|---|
| `-o` | Enable the peephole [[optimizer]] | `main.rs` → [[pipeline]] step 4 |
| `--timeout <N>` | Wall-clock timeout in seconds (default 60) | checked in [[eval]] (caveat: §B9) |
| `--first` | Stop after the first solution | [[eval|`record_solution`]] / `config.first_only` |
| `--strict` | Evaluate `let` RHS before binding (no [[suspensions-and-forcing|suspensions]]) | [[step|`Bind`]] `step.rs:146` |
| `--no-occurs-check` | Skip the [[unification#occurs-check|occurs check]] (faster, unsound) | `unify.rs:36,44` (caveat: §B13) |
| `--help` / `-h` | Usage | |

## Example

```
$ gweek --fair --first examples/coins.gwk
> [10, 10, 10, 10, 10]
>>> 1 solutions
```

See [[examples]] for the bundled programs, and the [web playground](https://plrg-bristol.github.io/gweek/)
which exposes the same options.

Related: [[config]], [[search-strategies]], [[main-and-lib]], [[examples]].
