# `need` reimplementation: before and after

## What was there

gweek is an existential logic programming language. Its abstract machine evaluates
Call-By-Push-Value terms under a search scheduler (BFS, DFS, IDDFS, or Fair). The
central binding construct is `let x = e in body`, which elaborates to the IR term
`Need { comp: e, cont: body }`.

**Before this refactor**, `Need` was just lazy binding with sequential drain:

1. `Need { comp, cont }` suspends `comp` in the suspension environment and binds
   `x` to a `Susp(sid)` reference.
2. The suspension is forced only when `x` is inspected — by unification, a case
   scrutinee, or forcing. This is standard call-by-need.
3. When the main computation returns (empty-stack `Return`), the machine
   sequentially drains any pending forced suspensions before emitting an answer.

This clean model has two consequences:

- **`fail need x. Ω` diverges.** The main computation runs first. `fail` is
  wrapped in the `Need`, so the suspension containing `fail` is created but
  never examined, and `Ω` diverges.
- **The left-zero law `fail need x. M ≃ fail` does not hold observationally.**
  It holds only in the lower (Hoare) powerdomain where `Ω` and `fail` are
  indistinguishable. gweek observes divergence as a timeout, not as zero
  solutions.

The `Machine` struct carried all state internally:

    pub struct Machine {
        pub cclos: CClosure,      // computation + environment
        pub stack: Stack,          // continuation frames
        pub lenv: LogicEnv,        // logic variable store
        pub senv: SuspEnv,         // suspension store
        pub done: bool,
    }

Schedulers worked over `Vec<Machine>`. At branch points the Machine was cloned,
each carrying its own `lenv` and `senv` via `Rc` copy-on-write.

## What was built

The refactor introduces the **Branch**: a concurrent search unit containing
multiple **cooperatively scheduled threads** sharing one logic environment and
suspension store. `Need` no longer just defers evaluation; it registers a
**residual obligation** that must succeed before the branch can emit.

### Structural changes

- `lenv` and `senv` are **owned by the Branch**, not individual Machines.
  `step()` borrows them mutably — essential for conjunctive sharing.
- `Machine` is stripped to `{ cclos, stack, done }`.
- Schedulers operate over `Vec<Branch>`. The strategy interface (BFS/DFS/
  IDDFS/Fair) is unchanged.
- GC root scanning walks all threads in every live branch.

### Tri-state suspension environment

`SuspEnv` changed from `Result<VClosure, CClosure>` to:

    enum SuspState {
        Suspended(CClosure),   // pending
        Running(CClosure),     // being evaluated by a thread
        Done(VClosure),        // memoized
    }

This lets the branch track in-flight suspensions and avoid duplicate
evaluators. The old API is preserved; new methods support branch lifecycle.

### Semantic change: `Need` as fair conjunction

Old: create suspension, continue cont, drain at answer-time.

New: create suspension, register it as an **obligation**, start evaluating it
**immediately** as a concurrent thread, continue cont. The branch emits only
when the main computation has returned AND every obligation is `Done`. If any
obligation thread fails, the whole branch dies.

### Blocking and waking

- `Suspended` → evaluate **inline** (zero overhead, identical to old code).
- `Running` → **block** current thread, join existing evaluator. When done,
  wake all waiters.

### Forking and Choice

When a thread hits `Choice`, the **whole branch** is cloned — not just the
machine. Each clone preserves all other threads, the ready queue, obligations
list, and candidate answer. This is critical for `(fail <> 1) need x. 0`.

## Laws

| Law | Before | After |
|-----|--------|-------|
| `fail need x. M ≃ fail` | Lower powerdomain only | Observationally |
| `fail need x. Ω` terminates | No (diverges) | Yes |
| `(M need x. N) need y. P ≃ M need x. (N need y. P)` | Holds | Holds |

## Performance

Inline evaluation for non-obligation suspensions means zero overhead for
`Force`/`Ifz`/`Match`/`Case`/`Equate`. Only `Need` adds one thread insertion
per `let` binding. Full suite: **69 tests, 2.56s** — identical to baseline.
