# Peak memory: `plan/copying-gc-nursery` vs `main`

Peak memory footprint (`/usr/bin/time -l`), median of 3 runs. Apple Silicon,
macOS, release build (`lto=true`, `codegen-units=1`). Regenerate with
`benchmark/gc/ab.sh`.

- **gc** — `plan/copying-gc-nursery` @ `b9e245d` (fix(machine): keep IDDFS's starting env immortal across collections)
- **main** — `main` @ `01de946` (refactor(parser): merge Stmt into a single Expr type)

| program | strat | kind | main | gc branch | change |
|---|---|---|--:|--:|--:|
| perm | bfs | complete | 54.8 MB | 53.4 MB | −3% |
| perm | fair | complete | 48.8 MB | 51.3 MB | **+5%** |
| perm | dfs | complete | 29.4 MB | 6.3 MB | **−79%** |
| nqueens | bfs | complete | 169.3 MB | 78.0 MB | −54% |
| nqueens | fair | complete | 170.5 MB | 62.9 MB | −63% |
| nqueens | dfs | complete | 157.2 MB | 10.6 MB | **−93%** |
| coins | bfs | complete | 239.4 MB | 232.7 MB | −3% |
| coins | fair | complete | 235.3 MB | 221.0 MB | −6% |
| coins | dfs | complete | 71.3 MB | 9.1 MB | **−87%** |
| pythagorean | bfs | long | 13093 MB | 731 MB | −94% |
| pythagorean | fair | long | 13565 MB | 641 MB | −95% |
| pythagorean | dfs | long | 12724 MB | 1047 MB | −92% |

**kind** — `complete`: run to full enumeration; both branches find the identical
solution count (720 / 92 / 11691), so peak memory is an equal-work comparison.
`long`: `pythagorean` never terminates, cut at a 12s timeout; the branches do
different amounts of work in that window, so these rows show bounded-vs-unbounded
behaviour, not a precise ratio.

See `README.md` for method and interpretation.
