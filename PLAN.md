# Plan: reclaiming memory with a copying collector and a GHC-style nursery

## Problem

Every long-lived runtime structure is allocated in a single `bumpalo::Bump` arena
shared by the whole search (`eval.rs` builds one `Bump` per run; `Machine.arena`
threads `&'a Bump` everywhere). A bump allocator never frees individual
allocations — only the entire arena drops, at the end of `eval`. So every `Env`
cons-cell (`env.rs`), `Stack` cons-cell (`step.rs`), and runtime `MValue`
(`Nat`/`Succ`/`Cons`/`Inl`/`Inr`/fresh `Var`/thunks) that any branch ever touched
stays resident until the run ends, including the allocations of branches that
died long ago.

### The garbage dominates the live set

Measured peak memory (`/usr/bin/time -l`, peak footprint):

| program | BFS | fair | DFS |
|---|--:|--:|--:|
| perm    | 54.8 MB | 48.9 MB | 29.2 MB |
| nqueens | 169.5 MB | 170.5 MB | — |

DFS on `perm` keeps a *single root-to-leaf path* live (kilobytes) yet holds
29 MB; nqueens is ~170 MB regardless of strategy. The resident memory is almost
entirely **dead arena nodes from explored-and-abandoned branches**, not the
reachable live set. Search strategy barely moves it. Genuine reclamation is the
right lever.

### Why not reference counting

A prior `Rc`-based version of these persistent structures was abandoned for being
too slow. The reason is structural: the machine clones an `Env` and a `Stack` on
*every step* (`step.rs` rebuilds the `Machine` in each arm) and clones
`lenv`/`senv` on every branch. `Rc` pays refcount traffic *per clone and per
drop* — i.e. on the hottest path in the interpreter. The lesson: reclamation cost
must land **per-collection**, not **per-operation**. That means a **tracing
collector**, not refcounting.

## Goals

- Reclaim arena nodes that are no longer reachable from any live machine.
- Keep allocation at bump speed between collections (no per-clone/per-drop tax).
- Preserve structural sharing exactly (a prefix shared by N branches stays one
  object after collection).
- Same observable results and solution counts; only memory and timing change.

## Non-goals

- Shrinking the genuinely-large *live* frontier of pathological BFS runs
  (`magic4`, `square2` at 20–30 GB). A tracing collector reclaims only dead
  memory; a large reachable frontier stays. That is a search-strategy concern
  (`--fair`/`--dfs`), orthogonal to this work.
- Concurrency / parallel GC.

## Enabling property: the arena is immutable and back-pointing

Verified: there is no interior mutability and no `unsafe` in the arena data
(`MValue`/`Env`/`Stack`). The only `Cell` near the machine is in
`union_find.rs` (path-compression parent slots holding `usize` indices, living
*outside* the arena inside `lenv`'s `Rc`); the `Cell`s in `optimize.rs` are
thread-local stat counters. Arena nodes are therefore **immutable once
allocated**, and the construction discipline guarantees **newer nodes only point
to older nodes** (`Cons(new, old_tail)`, `Succ`/`Cons`/`Inl` over
already-allocated children, `thunk` over an existing computation term).

Consequence for GC: **there are no intra-arena old→young pointers**, because the
only way to make one is to mutate an old object to point at a younger one, which
never happens. The mutable state (`lenv`'s `UnionFind`, `senv`'s `Vec`) lives
*outside* the arena and is already part of the root set. This removes the single
most error-prone piece of a generational collector — **no write barrier and no
remembered set are needed.**

## Design overview

A moving (copying) collector. Two phases of delivery:

1. **Phase 1 — single-space Cheney copying collector.** Establishes the hard,
   risky machinery: index handles, the tracer, forwarding pointers, the root
   set, and safe points. Lands reclamation on its own.
2. **Phase 2 — GHC-style generational nursery.** A refinement layered on Phase 1:
   a small young space collected frequently and cheaply (work ∝ survivors),
   survivors promoted to an old space collected rarely. Reuses all of Phase 1's
   machinery; adds only the space split and a promotion policy. No write barrier
   (see above).
3. **Phase 3 (optional) — DFS heap-checkpoint reset.** An O(1) fast path for
   chronological backtracking; composes with the collector.

### Prerequisite for any moving collector: handles instead of `&'a` references

A moving collector relocates objects, so raw `&'a T` references cannot survive a
collection. Replace arena pointers with **`NodeId(u32)` indices** into a
vector-backed arena. This is unavoidable for copying GC and has a large side
benefit: it **removes the viral `'a` lifetime** threaded through the entire
`machine` module. `Env`/`Stack` clone stays a `u32` copy (as cheap as today's
pointer copy).

## Phase 1 — single-space Cheney copying collector

### 1.1 Heap representation

Introduce a `Heap` that owns the nodes and hands out `NodeId`s.

- A node is the union of what is currently arena-allocated: `MValue`, `EnvInner`,
  `StackInner` (and the small `StkClosure` payload). Decide between:
  - **one tagged node arena** (a `Vec<Node>` with an enum), simplest for a
    copying collector since everything moves uniformly; or
  - **separate typed arenas** per node kind (`Vec<MValue>`, `Vec<EnvInner>`, …),
    better cache behaviour, but the collector must walk each.

  Recommendation: start with a single tagged `Vec<Node>` for simplicity; revisit
  if profiling shows it matters.
- `NodeId(u32)` replaces every `&'a MValue`, `Env(&'a EnvInner)`,
  `Stack(&'a StackInner)`. `Env` and `Stack` become newtypes over `NodeId`.
- Allocation = push to the live `Vec` and return the index — bump-equivalent.

### 1.2 The collector (Cheney two-space)

- Maintain from-space and to-space `Vec<Node>`.
- `collect(roots)`:
  1. For each root `NodeId`, `forward` it into to-space and overwrite the root
     with the new id.
  2. Cheney scan: walk to-space from the scan pointer; for each node, forward its
     children in place; advance until scan catches the free pointer.
  3. Swap spaces; clear from-space.
- `forward(id)`: if the from-space node already holds a forwarding marker, return
  the stored new id (this is what **preserves sharing** — every reference to a
  shared node resolves to the same copy). Otherwise copy the node to to-space,
  write a forwarding marker into the old slot, return the new id.
- Forwarding marker: reserve a `Node::Forwarded(NodeId)` variant (tagged arena
  makes this trivial).

### 1.3 Root set

Roots are exactly what the scheduler holds live, plus the embedded closures:

- Every `Machine` currently in the scheduler's collection
  (`Vec<Machine>` / `VecDeque<Vec<Machine>>` in `eval.rs`). For each machine:
  - `cclos`: the computation id is a *program* term (see 1.6) + the `Env` id;
  - `stack`: the `Stack` id;
  - `lenv`: every `VClosure` stored in the `UnionFind` payload
    (`(ValueType, Option<VClosure>)`) — each `Clos { val, env }` contributes a
    `val` id and an `env` id;
  - `senv`: every entry, `Ok(VClosure)` or `Err(CClosure)`, contributes ids.
- The machine being driven by `run_to_branch` at the moment of collection (it is
  handed back to the scheduler at a safe point — see 1.5 — so it is in the root
  set by construction).

**Critical:** the collector must reach *every* id, including those buried in
`UnionFind` and `SuspEnv`. Missing one is a use-after-free (a dangling id into
reclaimed-and-reused space). Enumerate these deliberately and test for it.

### 1.4 Program terms vs runtime values

The elaborated program (`MComputation` tree and the top-level `MValue`s from
`elaborate`) is allocated once and lives for the whole run. Options:

- Keep program terms in a **separate immortal region** never collected, and have
  the collector treat ids into it as leaves (cheapest; the AST is the bulk of
  "permanent" data). Requires distinguishing program-region ids from heap ids
  (e.g. a tag bit, or a separate id space).
- Or fold them into the heap and let them be traced/promoted normally (simpler
  id scheme; the AST just always survives).

Recommendation: separate immortal region for program terms — it keeps every
collection from copying the whole AST and pairs naturally with the nursery in
Phase 2.

### 1.5 Safe points and triggering

- The collector runs only at a **safe point**, where all live state sits in the
  scheduler's machine collection and nothing is mid-`step`. The natural safe
  point is the scheduler loop in `eval.rs`, between `run_to_branch` calls.
- `run_to_branch` (`step.rs`) can run many allocating steps without returning
  (a divergent deterministic loop never yields). Piggyback the existing `Clock`
  poll (`step.rs:137`, every 1024 ticks) with a **heap-watermark check**: when
  the live `Vec` exceeds the threshold, return the current machine to the
  scheduler (a new `RunResult::NeedGc(Machine)` variant), which collects and then
  resumes it.
- Trigger policy: collect when used bytes cross a watermark; grow the watermark
  adaptively (e.g. target survivors ≤ X% of space) to avoid thrashing.

### 1.6 Migration mechanics

- Thread a `&mut Heap` (or `&Heap` with interior allocation cursor) where `&'a
  Bump` is threaded today. The `'a` lifetime parameter disappears from `Machine`,
  `Env`, `Stack`, `VClosure`, `CClosure`, `MValue` references, etc.
- `env.rs`, `step.rs` (`Stack`), `vclosure.rs`, `unify.rs`, `lvar.rs`, `senv.rs`,
  `eval.rs`, `elaborate.rs`, `optimize.rs`, and `main.rs` all touch the arena and
  need updating. Expect this to be the bulk of the diff.
- `VClosure`, `StkFrame`, `StkClosure`, `EnvInner`, `MValue` hold ids instead of
  references; they stay `Copy` (a `u32` is `Copy`).

### 1.7 Phase 1 acceptance

- All existing tests pass (`src/main.rs` example tests, the `eval.rs`/`lvar.rs`
  unit tests, `tests/`).
- Solution counts unchanged across all examples and strategies.
- Peak memory on `perm`/`nqueens`/`coins` drops substantially vs the current
  arena; allocation-bound runtime stays within an acceptable factor of today.

## Phase 2 — generational nursery

Layered on Phase 1's tracer, forwarding, roots, and safe points.

- **Two spaces:** a small **nursery** (young) and an **old** generation. Allocate
  into the nursery by bump.
- **Minor GC:** when the nursery fills, copy live nursery nodes (Cheney) into the
  old generation; reset the nursery. Work is proportional to *survivors*, so a
  churny frontier that mostly dies is reclaimed cheaply.
- **Promotion:** survivors of a minor GC move to old. (Optionally an intermediate
  age before tenuring; start with immediate promotion for simplicity.)
- **Major GC:** collect the old generation rarely (e.g. when it grows past a
  watermark) with the same copying collector.
- **No write barrier / remembered set:** justified by the immutability +
  back-pointing invariant (§ "Enabling property"). A node's children are older
  than it, hence already promoted or copied in the same pass, so all edges become
  old→old after a minor GC. Roots for a minor GC are the scheduler's machines
  plus `lenv`/`senv` (scanned wholesale — they are not arena-resident). **Add a
  debug assertion** that scans for any old→young edge after a minor GC to catch a
  violated invariant early.
- **Tuning:** nursery size is a knob (GHC uses a few MB/core). Make it
  configurable; measure premature-promotion vs cache behaviour.

### Where the nursery wins and where it doesn't

- Wins big on DFS/fair: small live set, heavy churn — most nursery objects die
  before a minor GC, and the shared core is promoted once and left alone (a plain
  single-space Cheney would recopy that core every collection).
- Smaller win on pathological BFS (`magic4`, `square2`): the live frontier is
  genuinely huge, so much of the nursery survives → promotion churn → leans on
  major GC. Still helps; the marginal advantage over plain copying shrinks.

### Phase 2 acceptance

- Same correctness criteria as Phase 1.
- Minor GC pause time scales with survivors, not nursery size, on a churn-heavy
  workload (measure on `perm` DFS).
- Old-generation growth is bounded by the genuine live set, not total allocation.

## Phase 3 (optional) — DFS heap-checkpoint reset

For chronological (`--dfs`) backtracking, the back-pointing invariant means that
on backtracking past a choice point, everything allocated in the failed branch is
unreachable (surviving siblings were forked holding only pre-branch ids). So:

- Record the nursery's bump cursor at each choice point (a mark stack).
- On backtracking to that depth, reset the cursor to the mark — O(1) reclamation,
  no tracing.
- Bindings already backtrack via the copy-on-write `lenv`, so no trail is needed.
- Only valid under single-stack discipline (DFS); BFS/fair keep many branches
  simultaneously live and out of allocation order, so they rely on the collector.
- Composes with Phase 2: DFS then rarely fills the nursery.

## Correctness invariants (must hold throughout)

1. **Sharing preserved.** Forwarding pointers make every reference to a shared
   node resolve to one copy. Test: a program with heavy sharing must not grow
   memory after a collection.
2. **Complete root enumeration.** Every id reachable from a live machine —
   including ids inside `UnionFind` and `SuspEnv` — is a root or reachable from
   one. Test: stress collection mid-search and compare results to a no-GC run.
3. **Collection only at safe points.** Never mid-`step`; only when state is in the
   scheduler's machine collection.
4. **No old→young edges after minor GC** (Phase 2). Debug-assert by scanning.

## Testing

- Existing suites must pass unchanged (`cargo test`).
- **Differential test:** run every example under every strategy with GC forced
  very aggressively (tiny nursery / low watermark) and assert identical solution
  counts and rendered solutions to a high-watermark (effectively no-GC) run.
- **Sharing regression:** a deeply-shared structure stays flat in memory across
  forced collections.
- **Invariant assertions** compiled in debug (roots complete; no old→young).

## Benchmarking

- Harness: `/usr/bin/time -l` peak footprint + wall time, as used for the
  baseline table above.
- Track for `perm`, `nqueens`, `coins` (completing) and `magic`, `nqueens10`
  (heavier): peak memory and runtime, current arena vs Phase 1 vs Phase 2.
- Success: large peak-memory reduction on the garbage-dominated cases with
  allocation-bound runtime within an acceptable factor; nursery (Phase 2) beats
  single-space (Phase 1) on the shared-core workloads.

## Risks

- **Migration size.** The `&'a Bump` → `NodeId` change touches most of the
  `machine` module. Mitigate by doing the pure mechanical handle migration first
  (no collector yet, immortal heap), get it green, then add the collector.
- **Missed root → use-after-free.** The `lenv`/`senv` embedded closures are easy
  to forget. Mitigate with the differential test under aggressive GC and debug
  assertions.
- **Collector overhead regresses runtime.** Mitigate with adaptive watermarks and
  the generational split so the stable core is not recopied.
- **`--no-occurs-check` cycles.** Unsound mode can already build cyclic terms; a
  *copying* collector handles cycles correctly (forwarding pointers break the
  cycle on first visit), unlike refcounting — so this is fine, but include a
  cyclic-term case in the differential test.

## Sequencing summary

1. Mechanical migration: `&'a Bump` references → `NodeId` into an immortal
   `Heap`; remove the `'a` lifetime. Green tests, no reclamation yet.
2. Phase 1: single-space Cheney collector + roots + safe points + watermark.
3. Phase 2: split into nursery + old generation; promotion; no write barrier.
4. Phase 3 (optional): DFS heap-checkpoint reset.

## Known issue: IDDFS reuses a stale starting env across collections

The differential test `collection_preserves_solutions` (aggressive watermark)
fails under `--iddfs` with an out-of-bounds panic in `union_find.rs` (an empty
`UnionFind` indexed by a live `Var`). The cause is that `import_env` builds the
starting `env` once, and `eval_iddfs` reuses that same `Env` handle to spawn a
`fresh_machine` at the top of *every* deepening round. A collection during round
*N* rewrites the heap, but that `env` handle is held only by the iddfs driver
between rounds — it is never in the root set handed to `collect` — so it is not
forwarded. Round *N+1* then starts a machine from a stale id pointing at a
reused-and-overwritten node, and the first `Var` lookup resolves against the
machine's freshly-empty `lenv`, panicking. BFS/DFS/fair each build `env` once and
consume it once before any collection, so they are unaffected. Two clean fixes:
rebuild the starting env from the immortal top-level values at the start of each
round (localizes the restart semantics to iddfs), or make the top-level program
env immortal (matches §1.4 — it is program setup, never mutated, and must outlive
every collection — but needs an immortal env/stack store in `Heap`).
