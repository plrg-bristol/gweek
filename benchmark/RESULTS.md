# Gweek vs Curry Benchmarks

Comparing Gweek (release build) against KiCS2 3.3.0 (Curry → Haskell → native) and PAKCS 3.8.0 (Curry → SWI-Prolog 10.0).

**System:** Apple M3, macOS, arm64
**Runs:** 3 (median wall-clock time)

## Results

### Gweek strategies and optimizer

| Benchmark      | Solutions | BFS    | DFS    | Fair   | BFS -o | DFS -o |
|----------------|-----------|--------|--------|--------|--------|--------|
| perm(7)        | 5,040     | 0.014s | 0.013s | 0.014s | 0.011s | 0.011s |
| nqueens(8)     | 92        | 0.071s | 0.060s | 0.065s | 0.048s | 0.044s |
| coins(20)      | 11,691    | 0.423s | 0.211s | 0.410s | 0.392s | 0.189s |
| permsort(12)   | 1         | 6.96s  | 4.79s  | 5.18s  | 4.87s  | 3.46s  |
| half(1600)     | 1         | 0.094s | 0.095s | 0.091s | 0.074s | 0.075s |
| last(100)      | 1         | 0.004s | 0.003s | 0.003s | 0.003s | 0.003s |
| find_list(7,5) | 462       | 0.005s | 0.005s | 0.006s | 0.006s | 0.005s |

The `-o` flag enables the peephole optimizer. It gives the biggest improvement on permsort (28% faster) and nqueens (27% faster), with coins also showing a meaningful gain (10%).

### Gweek vs Curry

| Benchmark      | Solutions | Gweek DFS -o | KiCS2   | PAKCS   | vs KiCS2 | vs PAKCS |
|----------------|-----------|--------------|---------|---------|----------|----------|
| perm(7)        | 5,040     | 0.011s       | 2.23s   | 1.99s   | 203×     | 181×     |
| nqueens(8)     | 92        | 0.044s       | 1.73s   | 5.12s   | 39×      | 116×     |
| coins(20)      | 11,691    | 0.189s       | 2.39s   | 14.0s   | 13×      | 74×      |
| permsort(12)   | 1         | 3.46s        | 1.82s   | 55.7s   | **0.5×** | 16×      |
| half(1600)     | 1         | 0.075s       | 2.14s   | 178s    | 29×      | 2,373×   |
| last(100)      | 1         | 0.003s       | 1.87s   | 0.71s   | 623×     | 237×     |
| find_list(7,5) | 462       | 0.005s       | 1.85s   | >60s*   | 370×     | —        |

Speedups compare the best Gweek configuration (DFS -o) against each Curry system. Both PAKCS and KiCS2 use DFS.

\* PAKCS finds 1 of 462 solutions in ~14s, then stalls.

## Analysis

Gweek is **13–623× faster** than KiCS2 on 6 of 7 benchmarks, and **16–2,373× faster** than PAKCS on all comparable benchmarks.

### Why permsort is the outlier

Permsort is the one benchmark where KiCS2 beats Gweek (~1.9× faster). This is because permsort is *pure nondeterministic backtracking* — it uses zero logic variables, zero unification. The program generates permutations via nondeterministic insertion (`<>`), tests if each is sorted, and fails fast on the first out-of-order pair. The search tree is enormous (exploring up to 12! = 479M candidates) but each branch does almost no work.

This makes permsort a microbenchmark for raw backtracking loop speed. Gweek's CEK machine executes each step by matching on the current computation term, manipulating closures, and bumping reference counts on the `Rc`-wrapped logic and suspension environments at every branch point — all interpreted. KiCS2 compiles Curry to Haskell, which GHC compiles to native machine code; branching and pattern matching become direct jumps and stack manipulation with no interpretation overhead.

On every other benchmark, this per-step overhead is dwarfed by the cost of the actual logic programming work (unification, logic variable narrowing, Peano arithmetic). Permsort is the edge case where there is no such work to amortize against.

### Why find_list highlights Gweek's strength

The **find_list** benchmark is where Gweek's design shines most: it discovers list structure entirely through unification over free logic variables, finding all 462 solutions in 5ms. KiCS2 completes this benchmark in ~1.85s — making Gweek roughly **370× faster**. Most of KiCS2's time here is startup overhead (loading the compiled Haskell binary), but even accounting for that, Gweek's narrowing is substantially faster. PAKCS uses residuation (suspending evaluation until variables are bound) and cannot enumerate over unbound list variables; it finds only 1 of 462 solutions in ~14s before stalling.

The key difference: Gweek's abstract machine performs narrowing-by-need natively, exploring the space of possible list structures through unification in a single pass. KiCS2 must compile pull-tab representations for the free variable narrowing, and while it handles this correctly, the overhead of representing all the nondeterministic choices in the list spine is substantial. This is the benchmark where logic variable handling matters most, and Gweek's CEK machine was designed precisely for this kind of work.

## Benchmarks

**perm(7)** — Generate all 5,040 permutations of [1..7] by nondeterministic insertion.

**nqueens(8)** — Find all 92 solutions to 8-queens using Peano arithmetic for diagonal safety checks.

**coins(20)** — Find all 11,691 ways to make change for 20 using coins of value 1, 2, and 10. Uses a nondeterministic `coin` function and a logic variable `rest` constrained by unification.

**permsort(12)** — Sort a 12-element list by nondeterministic permutation sort: generate a permutation, check if sorted.

**half(1600)** — Compute half of the Peano number 1600 via inverse computation: find `x` such that `add x x =:= 1600`.

**last(100)** — Find the last element of a 100-element list via unification: find `xs`, `y` such that `cat xs [y] =:= list`.

**find_list(7,5)** — Find all 462 lists of length 7 whose elements sum to 5. The list is a free logic variable discovered entirely through unification.

## Notes

- All programs use Peano naturals (unary encoding).
- KiCS2 times include ~1.2s startup overhead (loading compiled Haskell binary).
- PAKCS times include ~0.8s SWI-Prolog startup overhead.
- Fair strategy performs similarly to BFS on these benchmarks; its advantage is on programs with infinite branches where DFS diverges.
- BFS has higher memory overhead than DFS, which accounts for the gap on coins and permsort.

## Reproducing

```
cargo build --release
python3 benchmark/run.py            # Gweek only (or auto-detects KiCS2)
python3 benchmark/run.py --kics2    # Gweek vs KiCS2
python3 benchmark/run.py --pakcs    # also include PAKCS (slow)
python3 benchmark/run.py --runs 5   # more runs for stability
```

Override paths via environment variables:
```
GWEEK_BIN=/path/to/gweek KICS2_DIR=/path/to/kics2 python3 benchmark/run.py
```

Default paths: KiCS2 at `benchmark/kics2-3.3.0-arm64-darwin/`, PAKCS at `benchmark/pakcs-3.8.0/`.
