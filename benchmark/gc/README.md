# Memory benchmark: copying GC + nursery vs. the bump-arena baseline

This harness measures gweek's **peak memory footprint** to quantify what the
copying collector and GHC-style nursery (`plan/copying-gc-nursery`) reclaim
versus the never-freeing `bumpalo` arena on `main`. It is the measurement behind
the table in `PLAN.md`.

## Method

- **Metric.** `/usr/bin/time -l`'s *peak memory footprint* (macOS phys_footprint
  high-water mark, bytes) — the same number `PLAN.md` quotes. Wall time is also
  recorded but is incidental here.
- **Two workload classes:**
  - **complete** — `perm`, `nqueens`, `coins` run to *full enumeration*. Both
    branches find the identical solution count (720 / 92 / 11691), so peak memory
    is an apples-to-apples comparison of the same work.
  - **long** — `pythagorean` never terminates and is cut off at a 12s wall-clock
    timeout. This is the *unbounded-garbage* scenario. ⚠️ The two branches do
    **different amounts of work** in 12s, so the numbers are not equal-work; they
    show whether memory *plateaus* (GC) or *grows without bound* (arena), not a
    precise ratio.
- Each `complete` cell is run 3× and the **median** peak is reported (peak is
  near-deterministic; variance is well under 1%).

## Running

```sh
# Full A/B: builds each ref in release, benchmarks both, prints the table.
benchmark/gc/ab.sh                      # defaults: plan/copying-gc-nursery vs main
benchmark/gc/ab.sh <gc_ref> <base_ref>  # override refs

# Or measure one binary and compare existing CSVs:
benchmark/gc/bench.sh target/release/gweek gc > benchmark/gc/results-gc.csv
benchmark/gc/compare.sh
```

`results-gc.csv` / `results-main.csv` in this directory are the committed runs
(Apple Silicon, macOS, release build: `lto=true`, `codegen-units=1`).

## Results

Refs benchmarked:

- **gc** — `plan/copying-gc-nursery` @ `b9e245d`
- **main** — `main` @ `01de946`

| program | strat | kind | main MB | gc MB | change |
|---|---|---|--:|--:|--:|
| perm | bfs | complete | 54.8 | 53.4 | −3% |
| perm | fair | complete | 48.8 | 51.3 | **+5%** |
| perm | dfs | complete | 29.4 | 6.3 | **−79%** |
| nqueens | bfs | complete | 169.3 | 78.0 | −54% |
| nqueens | fair | complete | 170.5 | 62.9 | −63% |
| nqueens | dfs | complete | 157.2 | 10.6 | **−93%** |
| coins | bfs | complete | 239.4 | 232.7 | −3% |
| coins | fair | complete | 235.3 | 221.0 | −6% |
| coins | dfs | complete | 71.3 | 9.1 | **−87%** |
| pythagorean | bfs | long | 13093 | 731 | −94% |
| pythagorean | fair | long | 13565 | 641 | −95% |
| pythagorean | dfs | long | 12724 | 1047 | −92% |

## Reading the numbers

- **DFS is the headline win (−79% to −93%).** DFS holds only a single
  root-to-leaf path live, so on `main` nearly all resident memory was *dead*
  arena nodes from backtracked branches. The collector reclaims them: `perm` dfs
  29→6 MB, `coins` dfs 71→9 MB, `nqueens` dfs 157→11 MB. This is exactly the
  pathology `PLAN.md` calls out.
- **`nqueens` BFS/fair drop ~55–63%** — even with a wide live frontier, a large
  fraction of the arena was garbage the collector can now free.
- **`pythagorean` plateaus instead of exploding.** `main` reaches ~13 GB in 12s
  and is climbing (heading for OOM); the GC branch holds well under 1 GB and
  could run indefinitely. Equal-work caveat applies, but the qualitative result —
  bounded vs. unbounded — is unambiguous.
- **`perm`/`coins` under BFS/fair barely move (and `perm fair` is ~5% *worse*).**
  These runs are dominated by a genuinely *live* breadth-first frontier, which a
  tracing collector cannot shrink (an explicit non-goal in `PLAN.md`). The small
  regression is the copying collector's semispace headroom showing through when
  there is little garbage to recover. Use `--fair`/`--dfs` for these.

Bottom line: the collector reclaims dead arena nodes as designed — order-of-
magnitude wins wherever garbage dominated the resident set (all DFS runs,
`nqueens`, and any long-running search), with a few-percent semispace cost on the
rare runs whose footprint is already almost entirely live.
