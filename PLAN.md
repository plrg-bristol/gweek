# Implementation plan: `need` as fair delayed conjunction

## Goal

Change the operational meaning of `Need` from:

```text
run the main computation;
when it returns, drain pending suspensions sequentially
```

to:

```text
run the main computation and all required residual suspensions as a fair conjunction;
emit an answer only when the main computation has returned and all required residuals have succeeded;
fail the whole branch as soon as any required residual search is exhausted
```

This is intended to validate equations such as:

```text
fail need x. N  ≃  fail
```

even when `N` diverges, and to make associativity/exchange of independent residual obligations less sensitive to registration/drain order.

The implementation should preserve the existing search-strategy interface as much as possible, but internally the scheduled unit should become a **branch** containing multiple live machines rather than a single `Machine`.

---

## Current implementation summary

The current machine state is roughly:

```rust
pub struct Machine {
    pub cclos: CClosure,
    pub stack: Stack,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
    pub done: bool,
}
```

`Need { comp, cont }` currently does:

```text
if comp is syntactically Return(v):
    bind v strictly and continue cont
else:
    allocate a fresh suspension for comp
    bind x to Susp(sid)
    continue cont
```

`SuspEnv` currently stores each suspension as either:

```rust
Err(CClosure)   // pending suspension
Ok(VClosure)   // evaluated suspension
```

When a value inspection reaches a `Susp`, `VClosure::close_head` returns `Err(SuspAt)`. The current `step.rs` handles this by `reschedule`: it runs the suspension immediately and pushes a `Set(sid, cont)` stack frame so that the returned value is memoised before resuming the blocked computation.

Separately, when `Return` is reached with an empty stack, the current machine calls `senv.next()` and sequentially drains pending suspensions before setting `done = true`.

The scheduler in `eval.rs` currently schedules whole `Machine`s under BFS/DFS/IDDFS/Fair. It already has safe points between `run_to_branch` calls and already knows how to collect roots from live machines.

---

## Desired semantic model

A search state should be:

```text
Search = fair set of branches

Branch =
  branch-local logic store
  branch-local suspension store
  table of live machines
  ready queue
  wait queues for suspensions
  set of required obligations
  optional candidate answer
```

Inside a branch, machines are conjunctive: they share the same logic and suspension state, and finite failure of a required machine kills the branch.

Across branches, alternatives are disjunctive: failure of one branch discards only that branch.

The central distinction is:

```text
<>         forks disjunctive branches
need/force schedules or joins conjunctive suspension evaluation
```

---

## High-level staged migration

Do this in four phases.

1. Refactor the current evaluator so branch-local state is explicit, while preserving existing observable behaviour.
2. Replace `SuspEnv` entries with a tri-state suspension representation.
3. Introduce a branch-internal fair scheduler and remove answer-time sequential drain.
4. Rework tests/docs around delayed conjunction and residual obligations.

The most important engineering decision is to avoid doing all semantic changes in one patch. First make the structure able to express branch-local scheduling, then change the meaning of `Need`.

---

## Phase 1: Introduce `Branch` without changing semantics yet

### 1.1 Add branch and machine identifiers

Add new internal identifiers in `machine/mod.rs` or a new `machine/branch.rs`:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct MachineId(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum MachineRole {
    Main,
    SuspEval { target: SuspId },
}
```

Initially `MachineId(pub usize)` is fine. A generational index can be introduced later if stale IDs become a problem.

### 1.2 Split machine-local execution state from branch-local stores

Target shape:

```rust
pub(crate) struct Machine {
    pub cclos: CClosure,
    pub stack: Stack,
}

pub(crate) struct Thread {
    pub machine: Machine,
    pub role: MachineRole,
    pub state: ThreadState,
}

pub(crate) enum ThreadState {
    Runnable,
    WaitingOn(SuspId),
    Returned(VClosure),
    Failed,
}

pub(crate) struct Branch {
    pub machines: Vec<Option<Thread>>,
    pub ready: VecDeque<MachineId>,
    pub waiters: HashMap<SuspId, Vec<MachineId>>,
    pub main: MachineId,

    pub lenv: LogicEnv,
    pub senv: SuspEnv,

    pub obligations: Vec<SuspId>,
    pub candidate_answer: Option<VClosure>,
}
```

This is a structural change: `LogicEnv` and `SuspEnv` should be owned by `Branch`, not by every `Machine`.

Why: under conjunctive scheduling, the main machine and residual machines must genuinely share substitutions and memo cells. The current `Rc` copy-on-write stores are correct for disjunctive branch cloning, but they are not sufficient for conjunctive sharing if each machine owns its own `lenv`/`senv`.

### 1.3 Change `Machine::step` to borrow branch stores

Replace:

```rust
fn step(self, cfg: &Config, heap: &mut Heap) -> Step
```

with something like:

```rust
fn step(
    self,
    cfg: &Config,
    heap: &mut Heap,
    lenv: &mut LogicEnv,
    senv: &mut SuspEnv,
) -> Step
```

The `Machine` no longer carries `lenv` or `senv`. The branch passes mutable references in for one step.

### 1.4 Replace `RunResult` over machines with branch-step outcomes

The current `run_to_branch` is designed to run one machine until it reaches a branch point or answer. Keep that idea, but make the result describe a thread-level outcome:

```rust
pub(crate) enum StepOutcome {
    Continue(Machine),

    // Object-language nondeterminism or logic-variable case split.
    Fork(Vec<BranchAlternative>),

    // A computation tried to inspect a suspension that is not Done.
    BlockedOn {
        susp: SuspAt,
        resume: Machine,
    },

    // Empty-stack return. Scheduler decides what this means
    // depending on MachineRole.
    Returned(VClosure),

    Failed,

    NeedGc(Machine),
    TimedOut,
}

pub(crate) struct BranchAlternative {
    pub machine: Machine,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
}
```

`BranchAlternative` is needed for logic-variable splits such as `Ifz`, `Match`, and `Case`, because each alternative mutates `LogicEnv` differently. Ordinary `Choice` alternatives can share/cloned stores unchanged.

As an intermediate step, you may keep the old `StepResult = SmallVec<[Machine; 2]>` and only introduce `BranchAlternative` when moving `lenv` out of `Machine`. But the target should make store changes explicit.

### 1.5 Preserve old behaviour initially

During Phase 1, still implement old answer-time drain. That means:

```text
main returned
  if senv has pending suspensions:
      schedule next pending suspension sequentially, old-style
  else:
      branch done
```

This lets the refactor land separately from the semantic change.

Acceptance criteria for Phase 1:

```text
cargo test passes
all existing example solution counts unchanged
BFS/DFS/IDDFS/Fair still work
aggressive GC differential tests still pass
```

---

## Phase 2: Replace `SuspEnv` with tri-state entries

### 2.1 Define suspension state

Replace the current `Result<VClosure, CClosure>` encoding with:

```rust
#[derive(Clone, Copy, Debug)]
pub(crate) enum SuspState {
    Suspended(CClosure),
    Running(MachineId),
    Done(VClosure),
}
```

Then:

```rust
#[derive(Clone)]
pub struct SuspEnv {
    entries: Rc<Vec<SuspState>>,
}
```

Remove or temporarily ignore `next_pending`. Under the new semantics, pending required suspensions are tracked by the branch’s `obligations`, not by a linear drain cursor.

### 2.2 Update `SuspEnv` API

Suggested API:

```rust
impl SuspEnv {
    pub fn new() -> SuspEnv;

    pub fn fresh(&mut self, cclos: CClosure) -> SuspId;

    pub fn get(&self, ident: SuspId) -> SuspState;

    pub fn mark_running(&mut self, ident: SuspId, owner: MachineId);

    pub fn set_done(&mut self, ident: SuspId, vclos: VClosure);

    pub fn lookup(&self, ident: &SuspId) -> Result<VClosure, SuspAt>;
}
```

`lookup` should keep the existing external meaning for `close_head`:

```text
Done(v)          => Ok(v)
Suspended(cclos) => Err(SuspAt { ident, cclos })
Running(_)       => Err(SuspAt { ident, cclos? })
```

However, `Running` does not have a `CClosure`. This suggests splitting the API:

```rust
pub enum SuspLookup {
    Done(VClosure),
    Suspended(SuspAt),
    Running(MachineId),
}
```

Then `VClosure::close_head` can return:

```rust
Result<VClosure, SuspBlock>
```

where:

```rust
pub enum SuspBlock {
    Suspended(SuspAt),
    Running { ident: SuspId, owner: MachineId },
}
```

This is cleaner than pretending a running suspension still has a closure.

### 2.3 Adjust forcing sites

The following current sites expect `Err(SuspAt)` and call `reschedule`:

```text
Force
Equate/unify
Ifz
Match
Case
occurs check
```

The new behaviour should be:

```text
if close_head sees Done:
    continue normally

if close_head sees Suspended:
    scheduler should start that suspension and block current thread

if close_head sees Running:
    scheduler should block current thread and join the existing owner
```

This means the low-level stepper should no longer call `reschedule` directly. Instead it should return `StepOutcome::BlockedOn`.

### 2.4 Preserve GC forwarding

Update `SuspEnv::forwarded` to handle:

```rust
SuspState::Suspended((comp, env)) => forward env
SuspState::Running(_)            => no heap pointers
SuspState::Done(vclos)           => forward vclos
```

The `Running(MachineId)` field is scheduler metadata and should not be forwarded by the heap.

Acceptance criteria for Phase 2:

```text
cargo test passes under old drain semantics
forced suspensions still memoise exactly once
GC tests still pass with Suspended/Running/Done entries
```

---

## Phase 3: Implement branch-internal fair scheduling

### 3.1 New top-level scheduled unit

Change the external schedulers in `eval.rs` from scheduling `Machine` to scheduling `Branch`.

Current shape:

```rust
Vec<Machine>
VecDeque<Vec<Machine>>
```

Target shape:

```rust
Vec<Branch>
VecDeque<Vec<Branch>>
```

or, for the fair scheduler, possibly:

```rust
VecDeque<Branch>
```

Initially, keep the existing strategy names and broad behaviour:

```text
BFS   = breadth-first over disjunctive branch frontier
DFS   = depth-first over disjunctive branch frontier
IDDFS = depth-limited over disjunctive branch depth
Fair  = round-robin over disjunctive branch groups
```

Inside each branch, use a small fair scheduler over the branch’s `ready` queue.

### 3.2 Branch stepping function

Add:

```rust
pub(crate) enum BranchRunResult {
    Yield(Vec<Branch>),
    Solution(VClosure, Branch),
    Dead,
    NeedGc(Branch),
    TimedOut,
}
```

or:

```rust
pub(crate) enum BranchOutcome {
    Continue(Branch),
    Fork(Vec<Branch>),
    Emit { answer: String, branch: Branch },
    Dead,
    NeedGc(Branch),
    TimedOut,
}
```

A branch is stepped by choosing one runnable thread from `ready`, running it until the next significant event, and then updating the branch.

Pseudo-code:

```rust
fn run_branch_quantum(
    mut branch: Branch,
    cfg: &Config,
    heap: &mut Heap,
    deadline: Instant,
) -> BranchOutcome {
    let Some(mid) = branch.ready.pop_front() else {
        return branch.if_complete_or_stuck();
    };

    let thread = branch.take_thread(mid);

    match thread.machine.run_to_event(cfg, heap, &mut branch.lenv, &mut branch.senv, deadline) {
        Continue(machine) => {
            branch.put_runnable(mid, thread.role, machine);
            BranchOutcome::Continue(branch)
        }

        BlockedOn { susp, resume } => {
            branch.block_on(mid, thread.role, resume, susp);
            BranchOutcome::Continue(branch)
        }

        Returned(vclos) => {
            branch.thread_returned(mid, thread.role, vclos, heap);
            branch.after_progress()
        }

        Fork(alts) => {
            let branches = branch.fork_thread(mid, thread.role, alts);
            BranchOutcome::Fork(branches)
        }

        Failed => {
            branch.thread_failed(mid, thread.role)
        }

        NeedGc(machine) => {
            branch.put_runnable(mid, thread.role, machine);
            BranchOutcome::NeedGc(branch)
        }

        TimedOut => BranchOutcome::TimedOut,
    }
}
```

### 3.3 Blocking on a suspension

When a thread hits a suspension:

```rust
fn block_on(
    &mut self,
    mid: MachineId,
    role: MachineRole,
    resume: Machine,
    block: SuspBlock,
)
```

Behaviour:

```text
Suspended(sid, cclos):
    allocate a new machine id owner
    set senv[sid] = Running(owner)
    put current thread into WaitingOn(sid)
    add current id to waiters[sid]
    enqueue owner as Runnable with role SuspEval { target: sid }

Running(sid, owner):
    do not start another evaluator
    put current thread into WaitingOn(sid)
    add current id to waiters[sid]
```

The waiting thread should keep its `resume` machine unchanged. Once the suspension is `Done`, waking the thread and re-running the same machine should cause `close_head` to see the completed value.

### 3.4 `Need` registers obligations

Change `Need { comp, cont }` from “create a suspension and continue” to:

```text
create suspension sid for comp
add sid to branch.obligations
bind x to Susp(sid)
continue cont
```

The stepper probably cannot mutate `branch.obligations` directly if it only sees `senv`. So add a step outcome:

```rust
StepOutcome::NewObligation {
    sid: SuspId,
    cont: Machine,
}
```

or let `Machine::step` return an effect list:

```rust
pub(crate) enum BranchEffect {
    RegisterObligation(SuspId),
}
```

Recommended simple target:

```rust
StepOutcome::ContinueWithEffects {
    machine: Machine,
    effects: SmallVec<[BranchEffect; 2]>,
}
```

For `Need`, the effect is:

```rust
BranchEffect::RegisterObligation(sid)
```

The branch scheduler records the obligation and may optionally enqueue it immediately.

### 3.5 Starting obligations fairly

After registering a required suspension, there are two choices:

1. Start it immediately.
2. Leave it `Suspended` but let the branch scheduler periodically start suspended obligations.

Recommendation: start it immediately.

```text
Need:
    sid = senv.fresh(M)
    obligations.push(sid)
    start_suspension_if_needed(sid)
    continue N
```

This gives `fail need x. Ω` the intended behaviour: the `fail` obligation is live before the main diverges.

### 3.6 Suspension return

When a thread with role:

```rust
MachineRole::SuspEval { target: sid }
```

returns `vclos`:

```text
set senv[sid] = Done(vclos)
wake every waiter in waiters[sid]
remove/wake queue entry
mark the suspension thread complete
```

Waking means:

```text
ThreadState::WaitingOn(sid) -> ThreadState::Runnable
push_back(mid) into ready queue
```

If `sid` is in `obligations`, it remains there as a completed obligation. Completion checks inspect `senv[sid]`.

### 3.7 Main return

When the main thread returns:

```text
candidate_answer = Some(vclos)
```

Do not emit immediately. Instead:

```text
if all obligations are Done:
    emit candidate answer
else:
    keep scheduling residual machines
```

If no residual machine is runnable and not all obligations are done, the branch is stuck. This should only happen because of a bug or unsupported cyclic dependency; in debug builds, report enough state to diagnose it.

### 3.8 Failure propagation

Rules:

```text
main thread fails:
    branch dies

required suspension thread fails:
    branch dies

non-required helper thread fails:
    branch dies unless such threads are introduced later with different semantics
```

Initially, all branch-internal spawned suspension evaluators should be required or forced by a required/main computation, so failure should kill the branch.

Important nondeterminism case:

```text
(fail <> return 1) need x. return V
```

This should not fail outright. It should fork into two branches:

```text
branch A: obligation alternative fail      -> dies
branch B: obligation alternative return 1  -> may emit V
```

This falls out naturally if every object-language `Choice` forks the whole `Branch`, not merely the current machine.

### 3.9 Forking branches

When a thread reaches `Choice` or a logic-variable case split, clone the whole branch once per alternative.

For each alternative:

```text
clone branch
replace the selected thread with the alternative machine
use the alternative lenv/senv if the split specialised stores
enqueue selected thread
```

The clone includes:

```text
main id
machines table
ready queue
wait queues
obligations
candidate answer
lenv/senv
```

Because `LogicEnv` and `SuspEnv` are already `Rc` copy-on-write stores, branch cloning should remain cheap.

### 3.10 Completion test

Add:

```rust
impl Branch {
    fn obligations_done(&self) -> bool {
        self.obligations.iter().all(|sid| {
            matches!(self.senv.get(*sid), SuspState::Done(_))
        })
    }

    fn ready_to_emit(&self) -> bool {
        self.candidate_answer.is_some() && self.obligations_done()
    }
}
```

Once a branch emits a candidate answer, the branch should be considered consumed, as in the current `done` machine handling. If later you want multiple answers from still-live residual searches, that should arise from earlier branch forks, not from continuing an emitted branch.

---

## Phase 4: Update GC root handling

The current collector forwards roots from live `Machine`s. After this refactor, roots are in live `Branch`es.

### 4.1 Replace machine-root collection

Current root categories:

```text
Machine.cclos.env
Machine.stack
Machine.lenv
Machine.senv
```

New root categories:

```text
for each live Branch:
    Branch.lenv
    Branch.senv
    for each live Thread:
        Thread.machine.cclos.env
        Thread.machine.stack
    Branch.candidate_answer, if any
```

If `ThreadState::Returned(VClosure)` is retained, that `VClosure` is also a root. If returned values are immediately moved into `candidate_answer` or `senv.Done`, there may be no separate returned-thread root.

### 4.2 Preserve store deduplication

The current collector deduplicates forwarded `LogicEnv` and `SuspEnv` stores by their `Rc` pointer identity. Keep this idea, but apply it at branch level:

```rust
fn forward_branch_roots(heap: &mut Heap, branches: &mut [&mut Branch]) {
    let mut lenv_map = HashMap::new();
    let mut senv_map = HashMap::new();

    for branch in branches {
        forward branch.lenv using lenv_map;
        forward branch.senv using senv_map;

        for thread in branch.live_threads_mut() {
            thread.machine.cclos.1 = heap.forward_env(thread.machine.cclos.1);
            thread.machine.stack = Stack(heap.forward(thread.machine.stack.0));
        }

        forward candidate_answer if present;
    }
}
```

### 4.3 Forward new suspension states

`SuspEnv::forwarded` must handle:

```text
Suspended(cclos): forward cclos.env
Running(machine_id): no heap forwarding
Done(vclos): forward vclos
```

The existing heap invariant remains intact: mutable scheduling tables live outside the heap and are scanned as roots; heap nodes themselves remain immutable.

---

## Phase 5: Tests

### 5.1 Existing regression tests

Before changing semantics, get Phase 1/2 passing:

```text
cargo test
existing examples under BFS/DFS/IDDFS/Fair
existing collection_preserves_solutions
```

Expect some solution ordering changes once branch-internal fairness lands. Tests should compare sorted rendered solutions where order is not semantically relevant.

### 5.2 New semantic tests for delayed conjunction

Add tests in `eval.rs` or integration tests.

#### Failure absorption

```text
fail need x. return V
```

Expected:

```text
0 solutions
```

#### Failure absorption against divergence

```text
loop n = loop n.
go = loop Z.

fail need x. go.
```

Expected under fair/conjunctive scheduling:

```text
0 solutions, without timeout
```

This is the key regression test.

#### Symmetric failure/divergence exchange

```text
loop n = loop n.
go = loop Z.

-- left
go need x. (fail need y. return 0)

-- right
fail need y. (go need x. return 0)
```

Expected:

```text
both have 0 solutions
```

The important bit is that the divergent residual cannot hide the failing residual forever.

#### Associativity sanity

Use terminating components first:

```text
M need x. (N need y. P)
(M need x. N) need y. P
```

where `M`, `N`, and `P` are small terminating computations. Expected equal solution multisets.

Then add a failing residual:

```text
M = fail
N = return 1
P = return 2
```

Expected both fail.

#### Nondeterministic residual

```text
(fail <> return 1) need x. return 0
```

Expected:

```text
one solution: 0
```

For multiset behaviour:

```text
(return 1 <> return 2) need x. return 0
```

Expected with default multiset semantics:

```text
two solutions: 0, 0
```

Expected with `--distinct`:

```text
one rendered solution: 0
```

### 5.3 Memoisation tests

A forced residual must not duplicate work.

Test shape:

```text
let x = (0 <> 1) in
pair x x
```

Expected:

```text
(0,0)
(1,1)
```

not:

```text
(0,0)
(0,1)
(1,0)
(1,1)
```

This verifies that `Running(owner)` and `Done(vclos)` preserve call-by-need sharing.

### 5.4 Waiter tests

Use two consumers of the same suspension:

```text
let x = expensive_or_branching in
case x of ...
case x of ...
```

Expected: second force joins the already-running or completed suspension; it should not start a duplicate evaluator.

### 5.5 GC stress tests

Extend the existing aggressive-watermark differential test so it covers:

```text
main waiting on Running suspension
multiple waiters on one SuspId
candidate_answer stored while obligations still running
Running(MachineId) entries in SuspEnv
```

The goal is to catch missed roots in:

```text
Branch.candidate_answer
Thread.machine
SuspEnv::Suspended
SuspEnv::Done
waited/resume machines
```

---

## Phase 6: Documentation updates

Update the conceptual docs to stop describing `need` as ordinary lazy binding with answer-time drain.

Suggested new wording:

```text
A `need` binding creates a suspension and also registers it as a residual obligation of the current branch. The main computation may proceed before the suspension is demanded, but a branch can emit an answer only after every registered obligation has succeeded. Obligations are scheduled fairly alongside the main computation, so finite failure of an unused obligation eventually prunes the branch.
```

Explicitly distinguish:

```text
ordinary call-by-need sharing:
    evaluate at most once, when demanded

gweek `need`:
    evaluate at most once, but also validate eventually as a branch obligation
```

Also update the powerdomain note:

```text
The previous sequential-drain evaluator validated left-zero only on the terminating fragment. The conjunctive scheduler operationalises the required parallel-fail behaviour by fairly interleaving main and residual machines within a branch.
```

---

## Implementation order checklist

Recommended patch sequence:

1. Add `Branch`, `Thread`, `MachineId`, `MachineRole`, but keep one main machine per branch.
2. Move `lenv` and `senv` from `Machine` to `Branch`.
3. Update `collect`/`forward_roots` to work over `Branch`.
4. Change schedulers in `eval.rs` to schedule `Branch` instead of `Machine`.
5. Preserve old behaviour with sequential drain; verify all tests pass.
6. Replace `SuspEnv` entries with `SuspState::{Suspended, Running, Done}`.
7. Replace `reschedule` with `StepOutcome::BlockedOn`.
8. Add wait queues and `start_suspension_if_needed`.
9. Change `Need` to register obligations.
10. Remove `senv.next()` answer-time drain.
11. Implement “emit only when candidate answer exists and obligations are done.”
12. Add delayed-conjunction tests.
13. Update docs.

---

## Open design questions

### Should syntactic `Need(Return(v), cont)` still optimise to strict binding?

Currently `Need` special-cases syntactic `Return(v)` and binds immediately. This is probably still fine: a `Return` obligation is already successful and cannot fail or diverge.

However, if multiplicity/provenance of obligations ever matters, even this optimisation should be reviewed. For now, keep it.

### Should `Running` live in `SuspEnv`?

Recommended:

```rust
SuspState::Running(MachineId)
```

This keeps the “at most one evaluator per suspension” invariant local to the suspension entry.

Alternative:

```text
SuspEnv stores only Suspended/Done
Branch has running_suspensions: HashMap<SuspId, MachineId>
```

This avoids storing scheduler IDs in `SuspEnv`, but it splits the state machine across two structures. The tri-state `SuspEnv` is clearer.

### Should `obligations` be a `Vec`, `IndexSet`, or bitset?

Start with:

```rust
Vec<SuspId>
```

`Need` creates each `SuspId` once, so duplicates should not arise. Add debug assertions if needed.

### What is the exact behaviour of DFS?

DFS is already incomplete for infinite branches. The new conjunctive scheduler should not try to make DFS semantically fair. It can still use the same branch-internal stepping machinery, but the user-facing completeness claims should continue to recommend `--fair`, BFS, or IDDFS for complete search.

### Could this be implemented with Rust async?

Not recommended. This scheduler is part of the object-language semantics: failure, branch cloning, memoisation, and logic-store sharing have custom meanings. A small explicit scheduler is easier to test and reason about than mapping this onto `Future` wakeups.

---

## Core invariants

Maintain these throughout:

```text
1. At most one live evaluator per SuspId in a branch.

2. All machines inside a branch share one LogicEnv and one SuspEnv.

3. Object-language Choice forks disjunctive Branches, not merely isolated machines.

4. A branch emits only when:
   main has returned
   and every required SuspId is Done.

5. Failure of a required conjunct kills the branch.

6. Failure of one disjunctive alternative kills only that alternative branch.

7. GC sees every heap handle reachable from:
   branch stores
   live thread machines
   candidate answers
   completed suspensions
   suspended closures
   waiting/resume machines.

8. Existing call-by-need sharing is preserved:
   forcing a Running suspension joins it;
   forcing a Done suspension reuses the memoised value;
   no suspension evaluator is duplicated within one branch.
```

---

## Minimal pseudocode for the final evaluator

```rust
while let Some(branch) = frontier.pop_next() {
    match run_branch_quantum(branch, cfg, heap, deadline) {
        BranchOutcome::Fork(branches) => {
            frontier.extend(branches);
        }

        BranchOutcome::Continue(branch) => {
            frontier.push_later(branch);
        }

        BranchOutcome::Emit { answer, branch: _ } => {
            if sink.record(answer) && cfg.first_only {
                break;
            }
        }

        BranchOutcome::Dead => {}

        BranchOutcome::NeedGc(branch) => {
            frontier.push_now(branch);
            collect_branches(heap, frontier.live_branches_mut());
        }

        BranchOutcome::TimedOut => {
            timed_out = true;
            break;
        }
    }
}
```

Branch quantum:

```rust
fn run_branch_quantum(mut branch: Branch, ...) -> BranchOutcome {
    let Some(mid) = branch.ready.pop_front() else {
        return if branch.ready_to_emit() {
            branch.emit()
        } else {
            BranchOutcome::Dead // or Stuck diagnostic in debug builds
        };
    };

    let thread = branch.take(mid);

    match thread.machine.run_to_event(..., &mut branch.lenv, &mut branch.senv) {
        Returned(v) if thread.role == Main => {
            branch.candidate_answer = Some(v);
            branch.after_progress()
        }

        Returned(v) if thread.role == SuspEval { target } => {
            branch.senv.set_done(target, v);
            branch.wake_waiters(target);
            branch.after_progress()
        }

        BlockedOn { block, resume } => {
            branch.block_or_start(mid, thread.role, resume, block);
            branch.after_progress()
        }

        Fork(alternatives) => {
            branch.fork_current_thread(mid, thread.role, alternatives)
        }

        Failed => {
            BranchOutcome::Dead
        }

        Continue(machine) => {
            branch.put_runnable(mid, thread.role, machine);
            branch.after_progress()
        }

        NeedGc(machine) => {
            branch.put_runnable(mid, thread.role, machine);
            BranchOutcome::NeedGc(branch)
        }

        TimedOut => BranchOutcome::TimedOut,
    }
}
```

`after_progress` should prefer emitting if possible:

```rust
fn after_progress(self) -> BranchOutcome {
    if self.ready_to_emit() {
        self.emit()
    } else if self.has_runnable_work() {
        BranchOutcome::Continue(self)
    } else {
        BranchOutcome::Continue(self) // or Stuck; decide after cyclic-dependency tests
    }
}
```

---

## Expected payoff

This change makes `need` a genuine residual-obligation construct rather than a sequential answer-drain mechanism.

It should recover the intended operational laws:

```text
fail need x. N  ≃  fail

(M need x. N) need y. P
≃
M need x. (N need y. P)

M need x. (L need y. N)
≃
L need y. (M need x. N)
    when independent
```

The crucial behavioural improvement is:

```text
fail need x. Ω
```

no longer diverges merely because the main computation diverges before answer-drain. The failing residual is a live conjunct and is fairly scheduled.

