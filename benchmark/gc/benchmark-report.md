# `need` vs `main` — memory & time benchmark

**Date:** 2026-06-27
**Branch:** `need` (dirty, 1 uncommitted change)
**Baseline:** `main` (committed results from `benchmark/gc/results-main.csv`)

## Method

The benchmark measures **peak memory footprint** (macOS `phys_footprint` high-water mark)
and **wall-clock time** via `/usr/bin/time -l` for gweek running four search programs
across three search strategies.

- **Programs:** `perm`, `nqueens`, `coins` (complete enumeration), `pythagorean` (unbounded, cut off at 12s)
- **Strategies:** `bfs`, `fair`, `dfs`
- **Repeats:** 3 per (program, strategy) for completing programs; 1 for `pythagorean` (30 runs total)
- **Metric:** median across repeats

The `need` binary was built with `cargo +stable build --release`. Each run executed:

```
/usr/bin/time -l target/release/gweek --<strategy> --timeout <timeout> examples/<program>.gwk
```

Peak memory was extracted via `awk '"'"'/peak memory footprint/{print $1}'"'"'`, wall time via
`awk '"'"'/ real /{print $1}'"'"'`, and solution counts via `grep -c '"'"'^>'"'"'` to verify equal work.

The benchmark was run inline across several ral turns, appending CSV rows to
`benchmark/gc/results-need.csv`.

## Solution counts

Identical between branches — equal-work comparison holds:

| Program | Solutions |
|---------|-----------|
| perm | 721 |
| nqueens | 93 |
| coins | 11,692 |
| pythagorean | 5 (bfs/fair), 1 (dfs) — time-limited |

## Results

### Wall time (median seconds)

| Program | Strategy | main (s) | need (s) | Δ |
|---------|----------|----------|----------|-----|
| perm | bfs | 0.06 | 0.51 | +750% |
| perm | fair | 0.06 | 0.42 | +600% |
| perm | dfs | 0.04 | 0.21 | +425% |
| nqueens | bfs | 0.08 | 0.22 | +175% |
| nqueens | fair | 0.08 | 0.32 | +300% |
| nqueens | dfs | 0.07 | 0.22 | +214% |
| coins | bfs | 0.41 | 7.04 | +1,617% |
| coins | fair | 0.39 | 5.23 | +1,241% |
| coins | dfs | 0.20 | 1.32 | +560% |
| pythagorean | bfs | 12.42 | 13.23 | +7% |
| pythagorean | fair | 12.49 | 12.01 | −4% |
| pythagorean | dfs | 12.42 | 13.19 | +6% |

**All completing programs are substantially slower on `need`.** The copying GC adds
tracing and copying overhead: perm slows 5–8×, nqueens 2.7–4×, coins 6.6–17×.
Pythagoran times are near-identical (dominated by the 12s timeout).

### Peak memory (median MB)

| Program | Strategy | main (MB) | need (MB) | Δ |
|---------|----------|-----------|-----------|-----|
| perm | bfs | 54.8 | 135.4 | +147% |
| perm | fair | 48.8 | 97.6 | +100% |
| perm | dfs | 29.4 | 6.6 | −77% |
| nqueens | bfs | 169.3 | 117.6 | −31% |
| nqueens | fair | 170.5 | 106.0 | −38% |
| nqueens | dfs | 157.2 | 10.3 | −93% |
| coins | bfs | 239.4 | 797.2 | +233% |
| coins | fair | 235.3 | 474.2 | +102% |
| coins | dfs | 71.3 | 13.0 | −82% |
| pythagorean | bfs | 13,093.2 | 505.5 | −96% |
| pythagorean | fair | 13,565.3 | 753.7 | −94% |
| pythagorean | dfs | 12,723.5 | 711.9 | −94% |

## Interpretation

- **The GC trades wall time for memory.** Across every completing program and strategy,
  `need` is slower — from 2.7× (nqueens bfs) to 17× (coins bfs). The copying collector
  traces and copies live objects; on a bump-arena baseline that never frees, this is pure
  overhead. Whether the memory savings justify the slowdown depends on the workload.

- **DFS memory wins are dramatic (−77% to −93%).** DFS holds only a single root-to-leaf
  path live; on `main` nearly all resident memory was dead arena nodes from backtracked
  branches. The collector reclaims them: `perm` dfs 29→7 MB, `coins` dfs 71→13 MB,
  `nqueens` dfs 157→10 MB.

- **BFS/fair on `perm` and `coins` regress in both dimensions.** These runs are dominated
  by a genuinely *live* breadth-first frontier, which a tracing collector cannot shrink.
  The semi-space headroom and GC overhead make them both slower (6–17×) and larger
  (+100% to +233%).

- **`pythagorean` plateaus instead of exploding (−94% to −96%).** `main` reaches ~13 GB
  in 12s and climbs toward OOM; the `need` branch holds ~500–750 MB and could run
  indefinitely. Time is roughly unchanged (dominated by the timeout).

- **`nqueens` BFS/fair are the sweet spot:** modest time cost (2.7–4×) for meaningful
  memory savings (−31% to −38%). Enough of the arena was garbage to reward collection
  without the extreme overhead seen on coins.

## Raw data

- `benchmark/gc/results-need.csv` — all 30 runs from this session
- `benchmark/gc/results-main.csv` — committed baseline from `main`
- `benchmark/gc/results-gc.csv` — committed runs from `plan/copying-gc-nursery` (for reference)
