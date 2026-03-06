# Search Strategies

## The search tree

The gweek machine evaluates a program by stepping through an abstract
machine. Most steps are deterministic: one machine state produces exactly
one successor. But some steps *branch*:

- **Choice** (`<>`): the program explicitly offers alternatives.
- **Case on a logic variable**: when `case x of Z -> ... | S n -> ...`
  encounters an unresolved logic variable, the machine splits into one
  branch where `x = Z` and another where `x = S(fresh)`. Similarly for
  lists (`[] / (h:t)`).

These branch points form a *search tree*. Each leaf is either a
solution (the computation returned a value) or a dead end (a
unification failed). The search strategy determines the order in which
the machine explores this tree.

## Strategies

### `--bfs` (breadth-first search, default)

Explores the tree level by level. All machine states at depth *d* are
stepped before any state at depth *d+1*.

**Pros:** Complete and fair. If a solution exists at finite depth, BFS
will find it. Solutions are discovered in order of depth.

**Cons:** Memory-hungry. The number of active machine states can grow
exponentially with depth. For programs with large finite branching
(e.g. permutations), this means tens of thousands of simultaneous
states.

**Best for:** Programs with logic variables that create infinite
branches, when you want guaranteed completeness and don't mind the
memory cost.

### `--dfs` (depth-first search)

Explores the tree by following a single path as deep as possible,
backtracking when it hits a dead end or solution.

**Pros:** Memory-efficient (stack proportional to tree depth, not
width). Very fast for programs with finite branching.

**Cons:** Incomplete on infinite branches. If a logic variable case
split creates an infinite chain of successors (e.g. trying
`n = 0, 1, 2, 3, ...` forever), DFS will follow it without ever
backtracking to try sibling branches.

**Best for:** Programs that branch only via `<>` (finite choice), like
permutation-based search (n-queens, sorting).

### `--iddfs` (iterative deepening depth-first search)

Runs DFS repeatedly with increasing depth limits (1, 2, 4, 8, ...).
At each iteration, branches that exceed the limit are pruned. The
limit doubles until no branches are pruned, meaning the entire tree
has been explored.

**Pros:** Complete (like BFS) with DFS-like memory usage. Finds
shallow solutions first.

**Cons:** Re-explores the tree at each iteration. Solutions are
deduplicated via a hash set, which adds memory and comparison
overhead. In practice about 1.5x slower than DFS on finite programs.

**Best for:** When you want completeness guarantees with low memory,
and can tolerate re-exploration overhead.

### `--fair` (fair round-robin DFS)

Maintains a queue of branches. Pops a branch from the front, runs it
DFS for up to 10,000 steps, then pushes any unfinished work to the
back of the queue. The next branch gets its turn.

**Pros:** Complete (every branch eventually gets stepped), with
DFS-like speed on finite programs (each branch typically finishes
within its quota). No re-exploration, no deduplication needed.

**Cons:** Very long-running single branches get interrupted and
resumed, adding a small overhead from queue management. The fixed
quota (10,000 steps) is a tuning parameter — too small wastes time on
context switching, too large delays fairness.

**Best for:** Mixed programs that combine finite choice with logic
variable splitting. Gets DFS speed where it counts and BFS fairness
where it's needed.

## Summary

```
            Complete?   Memory    Speed (finite)   Speed (infinite)
  --bfs     yes         high      slow             fair
  --dfs     no          low       fast             diverges
  --iddfs   yes         low       medium           fair
  --fair    yes         low       fast             fair
```

When in doubt, use `--fair`.
