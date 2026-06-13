---
title: Deep review (audit)
tags: [review]
updated: 7972077
---

# Gweek — Code Review

> **Status — historical snapshot.** This audit was produced before commit `7972077`. At least
> one finding is now resolved: **B1** (the union-find slot soundness bug) was fixed in
> `0f34f45` — logic-variable storage now canonicalizes through `Root` by construction, see
> [[union-find]] and [[logic-variables]]. The other findings are referenced as "known issue"
> callouts throughout the wiki; **verify each against current code before acting on it.** When
> a finding is fixed, note it here and in the relevant page (a [[AGENTS|lint]] task).

A full review of the `gweek` interpreter (~6,250 LOC of Rust in `src/`): a
Call-By-Push-Value (CBPV) abstract machine for a functional-logic language,
with logic variables, unification, four search strategies, and a peephole
optimizer.

**Baseline:** `cargo build` is green; `cargo test` passes 45/45. The findings
below are *latent* — they do not break the current example suite or tests —
unless explicitly marked as reproduced.

## How this review was produced

- The whole `src/` tree was read first-hand.
- Six independent reviewers swept the code across dimensions (evaluator,
  unification+optimizer, frontend, cleanliness, architecture, performance),
  each grounding every claim in `file:line` references and, where relevant,
  running `gweek`.
- Every candidate **bug** was then put to three adversarial verifiers, each
  with a distinct lens — operational-semantics reasoning, de Bruijn / index
  arithmetic, and empirical execution — and kept only on a ≥2/3 vote. Quality
  findings got a grounded verifier. This pass *rejected* five plausible-looking
  bug claims (see [§5](#5-verified-non-issues)).
- The headline correctness bugs (boolean exprs, `Int`, mutual recursion,
  numeric case patterns, polymorphic application) were reproduced directly
  against the built binary. The divergent-loop timeout bug (B9) was **not**
  re-run — it has unbounded memory growth and already carries 3/3 confirmation.

## Scorecard

| Dimension | Confirmed | Headline |
|---|---|---|
| Correctness bugs | 13 | Unification can silently drop solutions (union-find slot bug) |
| Simplicity / cleanliness | 13 | `step.rs` is ~150 lines of `Machine{…}` rebuild boilerplate |
| Architecture | 5 | Three copy-pasted de Bruijn traversals; global thread-local config |
| Performance | 9 | Copy-on-write `Rc<Vec>` backtracking state → O(N²) on deep search |

---

## 1. Correctness bugs

Ordered by severity. ✅ = reproduced first-hand during this review.

### B1 — Unification can write a binding to a dead union-find slot and lose the solution `[high]`
**`src/machine/lvar.rs:29-37`** (reached from `unify.rs:33,41,49`)

`LogicEnv::lookup` reads the binding at the **union-find root**
(`entries[find(ident)]`), but `set_vclos` writes at the **raw ident**
(`entries[ident]`). When `unify` merges two unbound logic variables via
`identify` (union) and later binds one of them with `set_vclos(ident, …)`, if
that `ident` is not the union-find root the value lands in a slot `lookup` never
reads. The constraint is silently dropped, and a *satisfiable* query can return
0 solutions depending only on which variable the union-find happened to pick as
root. This is a soundness hole — the most serious finding here, even though no
current example triggers it.

**Fix:** resolve the root before writing:
```rust
pub fn set_vclos(&mut self, ident: Ident, vclos: VClosure<'a>) {
    let root = self.union_vars.find(ident);
    let ptype = self.get_type(root);
    Rc::make_mut(&mut self.entries)[root] = (ptype, Some(vclos));
}
```
All examples and the full test suite still pass with this fix.

### B2 — Boolean expressions type-check, then panic in translation ✅ `[high]`
**`src/machine/translate.rs:518-520`** (`translate_bexpr` is `todo!()`),
reached from `translate.rs:490`.

`synth_bexpr` (`type_check.rs:406-427`) happily types `==`, `!=`, `&&`, `||`,
`!` as `Bool`, so any program using them passes the type checker and then
aborts. `if … then … else …` is unusable for the same reason (its condition
lowers through `translate_bexpr`).

```
$ echo 'true == false.' | gweek /dev/stdin
thread 'main' panicked at src/machine/translate.rs:519:5:
not yet implemented: boolean expressions not yet implemented
```

**Fix:** implement `translate_bexpr`. `Bool` is already `Sum(Unit,Unit)`
(`Inl`=true / `Inr`=false); lower `==`/`!=` on `Nat` to `Ifz`/`Equate`,
`&&`/`||` to nested `Case`, `!` to swapping `Inl`/`Inr`. Until then the type
checker should *reject* boolean exprs so the failure is a clean type error.

### B3 — Mutual recursion across top-level functions panics ✅ `[high]`
**`src/machine/translate.rs:173-176`** (cycle fallback), `:281-282`, `:32`.

`reorder_decls` topologically sorts functions by reference, but on a genuine
cycle it falls back to the *original* order. Each function name is bound into
`TEnv` only at its own definition site, so no linear order can satisfy mutual
recursion — the first function in the group references a not-yet-bound name and
`TEnv::find` panics.

```
$ gweek mutual.gwk      # f calls g, g calls f
thread 'main' panicked at src/machine/translate.rs:32:32:
Variable g not found in environment
```

**Fix:** pre-bind **all** top-level function names into `TEnv` before
translating any body (mirroring the type checker's first pass,
`type_check.rs:134-138`), and emit each recursive group through a fixpoint so de
Bruijn indices resolve across the group. The per-function `Rec` wrapper cannot
express mutual recursion.

### B4 — Lowercase type variables are rigid strings, not polymorphism ✅ `[high]`
**`src/type_check.rs:95-110`** (`unify`), `:363-374` (`App`).

Type variables are `Type::Ident("a")` and unify only by string equality. There
is no instantiation, so a polymorphic function cannot be applied at a concrete
type: `id :: a -> a` type-checks at its definition but every call is rejected.

```
$ gweek poly.gwk        # id :: a -> a; id x = x. id 5.
Type error: in application: type mismatch: expected a, got Nat
```

Every polymorphic signature in the parser tests (`a -> a`, `a -> b -> a`) is
therefore unusable. **Fix:** either real HM-style instantiation (fresh
metavariables per use + substitution), or — minimally — treat lowercase
`Ident` type variables as unifiable wildcards (like `Type::Any`).

### B5 — Lambdas can never be passed as arguments; the checking code is dead `[high]`
**`src/type_check.rs:387-404`** (`check_expr`, never called), `:367`.

`check_expr` holds the only `(Lambda, Arrow)` rule but is never invoked
(`rg` confirms only the definition). `synth_expr` for `Lambda` unconditionally
errors “cannot infer type of lambda” (`:377-379`), and `App` *synthesizes* the
argument instead of *checking* it against the known parameter type — so any
lambda argument is rejected even when the expected type is fully known.
`resolve_return_type` (`:455-457`) is dead with it.

**Fix:** call `check_expr` from the `App` argument position (replace
`synth_expr(ctx, arg)` + `unify` at `:367-368` with `check_expr(ctx, arg,
&param)`), and from other positions with a known expected type.

### B6 — Type parser: `*` and `->` share precedence, so `A * B -> C` mis-parses `[high]`
**`src/parser/parse.rs:57-83`** (`type_parser`).

Both `->` and `*` are equal-precedence right-recursive operators over the same
rule, so `Nat * Nat -> Nat` parses as `Product(Nat, Arrow(Nat,Nat))` instead of
`Arrow(Product(Nat,Nat), Nat)`. A function taking a pair cannot be written
without parenthesising the product, and `peel_arrows` then fails (top
constructor is `Product`). **Fix:** layer the grammar — `*` binds tighter than
`->`; `->` right-associates.

### B7 — Solutions containing a free logic variable are silently dropped `[high]`
**`src/machine/vclosure.rs:102-110`** (`close`), `eval.rs:130-141,293-295`.

When a machine finishes with an answer that still mentions an unresolved logic
variable, `close` returns `None` for every type except `Unit`, and
`record_solution` only counts/prints inside `if let Some(s)`. So a valid
solution with a residual free variable is neither printed nor counted — across
all four strategies. `examples/inert.gwk` (`exists x :: Nat. x.`) is meant to
return a free `x` but yields 0 solutions. **Fix:** have `close` emit a
placeholder (`_<id>`) for unresolved variables of *all* types, so residual
answers are reported (standard for functional-logic languages).

### B8 — IDDFS deduplicates by output string, undercounting distinct solutions `[high]`
**`src/machine/eval.rs:194,211-221`** (`eval_iddfs`).

To avoid recounting across deepening rounds, IDDFS keys a `HashSet<String>` on
the *rendered output*. Two genuinely distinct derivations that print the same
string collapse to one, so IDDFS — documented as “complete” — reports a smaller
count than BFS/DFS/Fair whenever distinct solutions share a rendering.
**Fix:** key dedup on the derivation/branch path, or restructure deepening so
each round only counts newly-reachable solutions (no cross-round dedup).

### B9 — `--timeout` is ignored for a divergent non-branching computation `[high]`
**`src/machine/step.rs:73-82`** (`run_to_branch`), deadline checks at
`eval.rs:151,175,201,248`.

Deadline checks live in the scheduler loops, *between* calls to
`run_to_branch`. But `run_to_branch` drives deterministic steps in a tight loop
and only returns at a branch point or completion. A deterministic divergent
recursion (`loop n = loop (S n)`) produces only `Step::Continue`, never yields,
so the timeout never fires: the process spins at 100% CPU and the bump arena
grows without bound. (This is the case that exhausted memory during review; it
was confirmed by the verifiers but not re-run here.) **Fix:** check the deadline
(every N steps) *inside* `run_to_branch` and bail with a sentinel.

### B10 — Pair patterns / arguments are unimplemented despite type-checker support `[medium]`
**`translate.rs:476`** (`todo!()`), **`:288`** (`_ => todo!()`),
**`parse.rs:377`** (`panic!("bad case pattern")`).

`bind_arg` type-checks pair destructuring (`type_check.rs:71-79`), but
`translate_func` rejects any non-`Ident` arg, lambda pair-args are `todo!()`,
and tuple patterns in `case` panic the parser. Products are a first-class
`ValueType` with `MValue::Pair`, yet there is no working way to destructure one.
**Fix:** lower pair args/patterns by binding two fresh variables and projecting;
make malformed tuple patterns a clean parse error, not a panic.

### B11 — `Int` type-checks but panics during translation ✅ `[medium]`
**`type_check.rs:432-435`** accepts `"Int"`; **`translate.rs:317-331`** has no
`Int` case → `panic!` at `:324`.

```
$ echo 'exists n :: Int. n.' | gweek /dev/stdin
thread 'main' panicked at src/machine/translate.rs:324:27:
cannot translate type Int
```

The checker and translator disagree on the type alphabet. **Fix:** drop `"Int"`
from the accepted set (clean type error), or add an `Int` representation.

### B12 — Numeric literal in a `case` pattern panics the parser ✅ `[low]`
**`src/parser/parse.rs:334-382`**, panic at `:377`.

`cases_parser` recognises only `Z`/`S`/`[]`/`(x:xs)`. A literal pattern like
`case n of 0 -> … | S m -> …` produces `Expr::Nat(0)` and hits
`panic!("bad case pattern")` — natural for users to write, given the dual `Nat`
representation. **Fix:** normalise `Nat(0)`→`Zero`, `Nat(k)`→nested `Succ`, or
emit a recoverable parse error instead of `panic!`.

### B13 — `--no-occurs-check` overflows the stack on cyclic terms instead of failing gracefully `[low]`
**`src/machine/vclosure.rs:51-117`**, flag at `main.rs:22,44`.

With the occurs check off, `x =:= S x` installs a cyclic binding; rendering the
answer drives `close` into unbounded recursion (`x → Succ(x) → …`) and aborts
the whole process. The flag is documented as unsound, but an abort on *output*
is harsher than necessary. **Fix:** bound the recursion depth in `close` and
report an error / refuse to print infinite terms.

---

## 2. Simplicity & cleanliness

### C1 — `step.rs`: ~33 hand-rolled `Machine { … done: false }` rebuilds `[high]`
**`src/machine/step.rs:84-606`.** The `step` function is almost entirely
7–8-line `Step::Continue(Machine { arena, cclos: (...), stack, lenv, senv,
done: false })` literals that restate five unchanged fields each time; the arms
typically vary only `cclos` (and sometimes `stack`). This buries the transition
rules under boilerplate.

**Fix:** stop destructuring `self` at `:85`; add consuming helpers, e.g.
```rust
fn goto(mut self, cclos: CClosure<'a>) -> Step<'a> { self.cclos = cclos; Step::Continue(self) }
fn goto_stack(mut self, cclos: CClosure<'a>, stack: Stack<'a>) -> Step<'a> { … }
```
Arms that change `lenv`/`senv` mutate `self.lenv`/`self.senv` first, then
`goto`. Each literal becomes one line (`self.goto((cont, new_env))`). Removes
~150–180 lines from a 607-line file; behaviour-preserving (pure field
restating).

### C2 — `step.rs`: the suspension-reschedule block is copied in 5 arms `[medium]`
**`step.rs:188-198, 300-310, 318-328, 414-423, 503-512`** (Force / Equate / Ifz
/ Match / Case). All five handle `close_head` returning `Err(a)` with identical
code (push `StkFrame::Set(a.ident, comp)`, continue at `a.cclos`). **Fix:** one
`fn reschedule(self, a: SuspAt, comp, env) -> Step` method; each arm becomes
`Err(a) => self.reschedule(a, comp, env)`. (The 6th occurrence at `:93` is a
genuinely different scheduler path — leave it.)

### C3 — Dead code hidden by `[lints.rust] unused = "allow"` `[medium]`
**`Cargo.toml:25-26`** silences `dead_code` crate-wide. Re-enabling the lint
surfaces only ~6 warnings, but all are real: `check_expr`
(`type_check.rs:387-404`) and `resolve_return_type` (`:455-457`) are never
called; `synth_expr`’s `Lambda` arm binds unused `arg`/`body` (`:377`); there is
an unused `SuspAt` import in `step.rs:7`. **Fix:** delete the blanket allow
(this is research code with no compat constraint), remove the two dead
functions and the import, `_`-prefix the unused params. Annotate any
intentionally-kept unused public items individually.

### C4 — `count_nodes` is dead outside the `opt-stats` feature `[low]`
**`mterms.rs:140-174`.** All call sites are `#[cfg(feature = "opt-stats")]`, but
the two `count_nodes` impls (~35 lines) are not gated, so a default build keeps
them only via the blanket allow. **Fix:** gate them with
`#[cfg(feature = "opt-stats")]`, matching `Env::count_nodes` (already gated).

### C5 — `optimize.rs`: `resolve_val` is a pure pass-through wrapper `[low]`
**`optimize.rs:431-433`** forwards verbatim to `deep_resolve`. Delete it and
call `deep_resolve` directly at its six call sites (−3 lines, one fewer
indirection).

### C6 — `eval.rs`: timeout-tick boilerplate duplicated across all four strategies `[low]`
**`eval.rs:147/150-151, 172/174-175, 195/200-201, 243/248`.** Each strategy
repeats `iters += 1; if iters & 1023 == 0 && Instant::now() >= deadline { … }`.
**Fix:** a tiny `Clock { iters, deadline }` with `fn tick(&mut self) -> bool`.
(The scheduling loops themselves are genuinely different — do *not* merge them.)

### C7 — The 4.4 GB untracked `benchmark/` directory `[low]`
`benchmark/` (third-party PAKCS/KiCS2 distributions) is neither tracked nor
git-ignored — it sits in every `git status` and is one `git add .` from being
committed. **Fix:** add `/benchmark/` to `.gitignore` (and document how to fetch
it), or move the few generated inputs that matter out and ignore the bulk.

*(C2/C3-related smaller items — eval_iddfs’s duplicated solution-recording
block, the duplicated 3600 s fallback + timeout-summary formatting, and the
three repetitive logic-var instantiation blocks in `step.rs` — fold naturally
into C1/C2 and the architecture items below.)*

---

## 3. Architecture

### A1 — `optimize.rs`: three byte-identical binder-aware traversals `[high]`
**`optimize.rs:113-188` (shift), `:194-268` (subst), `:329-397` (swap).**
`shift_comp`/`subst_comp`/`swap_comp` each rebuild the full 11-arm
`MComputation` tree with *identical* per-binder depth bookkeeping (`cont`/
`Lambda`/`Exists`/`Rec`/`Ifz sk`/`Case` at +1, `Match consk` at +2); only the
`Var` leaf action and the carried scalar differ. That’s ~270 lines of triplicated
traversal — every new `MComputation` variant must be added in five places, and a
depth mistake in one copy silently diverges.

**Fix:** one generic binder-aware `map_comp`/`map_val` parameterised by a leaf
closure `f(binders_crossed, &Var) -> &MValue`, with the depth table written
once. `shift`/`subst`/`swap` become 3–5-line calls. (Leave `has_free_var_comp`,
a different-typed fold, and `opt_subterms`, which threads an env, out of scope.)
Eliminates ~200 lines and makes the binder rules single-source.

### A2 — Runtime config is split between a thread-local global and explicit args `[high]`
**`config.rs:10-43`, `eval.rs:80-116`, read in `step.rs:146`, `unify.rs:36,44`,
`eval.rs:131-141`.** `Config`/`DEADLINE` live in a thread-local `Cell` and are
read ad hoc deep in the machine, *but* `run()` (the test entry point) takes
`strategy` explicitly and computes its own deadline without calling
`config::init`. So a test running `Strategy::Dfs` still has `config().strategy ==
Bfs`, and `strict`/`occurs_check`/`first_only` come from whatever a previous
`init()` left on the thread. Two sources of truth, a reentrancy/testability
hazard, and the duplicated 3600 s fallback.

**Fix:** thread a single immutable `&Config` (carrying the deadline as an
absolute `Instant`) through `run_internal`/`eval_*`/`step`/`unify`/
`record_solution`, and delete the thread-local entirely.

### A3 — `MValue::Zero` is dead at runtime yet forces a mixed-representation case explosion `[medium]`
**`mterms.rs:12-24`, `unify.rs:61-97`, `step.rs:330-360`, `vclosure.rs:73-82`.**
Every runtime site produces `Nat(u64)`, never `Zero` (the translator emits
`Nat(0)`, logic-var splits emit `Nat(0)`/`Succ`, and `close` normalises
`Zero`→`Nat(0)`). Yet the dual representation costs eight reconciliation arms in
`unify`, three `Ifz` cases, and dual folds in `to_nat`/`close`. `Nat(u64)` earns
its keep; the *`Zero` variant* is pure overhead.

**Fix:** keep `Nat(u64)` and `Succ` (the symbolic successor is needed for
logic-var `Ifz` splits and `S e`), drop `MValue::Zero`, and fold its arms into
the `Nat(0)` cases. Deletes ~⅓ of the arithmetic unify arms without changing
behaviour.

### A4 — Pervasive `panic!`/`unreachable!`/`todo!` (38 sites) as the error channel `[medium]`
25 `panic!`, 9 `unreachable!`, 4 `todo!` across `src/`. Some are legitimate
invariant assertions; many encode *user-reachable* conditions (boolean exprs,
pair args, occurs-on-suspension, malformed case sets) — making a compiler bug
indistinguishable from user error and forcing the WASM playground to surface
them only via the panic hook. **Fix:** keep `panic!`/`unreachable!` for true
machine invariants (documented); route user-reachable conditions through typed
errors (`TypeError` / a new `MachineError` / `Simple::custom`). Prioritise the
`todo!()` sites — they abort on otherwise-valid programs.

### A5 — `Ident = usize` aliases two disjoint namespaces `[low]`
**`mod.rs:20`.** The same `Ident` indexes both `LogicEnv` (logic vars) and
`SuspEnv` (suspensions); nothing stops passing one to the other’s `lookup`.
**Fix:** distinct newtypes (`LVar(usize)`, `SuspId(usize)`) so the confusion
becomes a compile error. Mechanical, zero runtime cost.

---

## 4. Performance

Ordered by leverage. The first is free; the big structural win is P3/A-state.

### P1 — No `[profile.release]` tuning (measured 28–43 % speedup, zero behaviour change) `[high]`
The interpreter is one tight inner loop hammering bumpalo and `Rc` from another
crate; the default release profile (`lto=false`, `codegen-units=16`) can’t
inline across crate boundaries or keep the hot loop in one codegen unit.
**Fix:**
```toml
[profile.release]
lto = true
codegen-units = 1
# panic = "abort"   # optional: the machine never unwinds usefully
```
Build time ~10 s → ~24 s; a worthwhile trade for the runtime cut.

### P2 — Backtracking state is copy-on-write `Rc<Vec>` → O(N²) on deep search `[high]`
**`lvar.rs:24-25,36,44`, `senv.rs:38,55`, `union_find.rs`, shared by clones in
`step.rs:255-256,367,457,546`.** Every branch clones `lenv`/`senv` (cheap
refcount bump), but the *first* subsequent write on any branch hits
`Rc::make_mut`, which deep-copies the **entire** `Vec` (and `UnionFind` array)
because the refcount is shared. A path that accumulates N variables pays O(N)
per binding → O(N²) per path; on `magic4` (16 `exists` + recursive lazy binds)
this dominates.

**Fix:** replace COW with a **trail/undo log** — one mutable env plus a log of
`(ident, old_value)`; branch points record the trail length, backtrack pops to
it. Makes a binding O(1) and backtracking O(changes). BFS (many simultaneous
live frontiers) is the one strategy that genuinely needs persistent state — for
it a persistent/HAMT map keyed by `ident` gives sharing without full-`Vec`
copies. ~1–2 days, gated by the test suite (which pins the solution multiset).

### P3 — Per-step arena allocations are never reclaimed; memory ∝ total work `[high]`
**`eval.rs:29,44,67,81` + every `step`.** A single `Bump` lives for the whole
search and bumpalo never frees individual allocations, so peak memory is
proportional to *total steps executed*, not the live working set — this is what
makes long searches exhaust RAM (and shows as large system time). **Fix (larger
redesign — flag, don’t apply blindly):** either make `Env`/`Stack` nodes `Rc`
instead of arena-allocated (keeps O(1) clone, frees dead branches), or
periodically compact live machines into a fresh arena. At minimum, document the
unbounded-memory characteristic. (Closely related to B9.)

### P4 — `eval_iddfs` re-explores every round and keeps every solution string forever `[medium]`
**`eval.rs:191-235.`** Iterative deepening restarts from scratch with a doubling
limit and dedups via an ever-growing `HashSet<String>`. The re-exploration is
inherent, but the constant factor is high. **Fix:** only emit/explore nodes
between `limit/2` and `limit` each round; and prefer/recommend `--fair` (also
complete, DFS-speed, no dedup) over `--iddfs`.

### P5 — `config()`/`deadline()` route through the macOS thread-local accessor on the inner loop `[low]`
**`config.rs:37-43`, read at `step.rs:146` (every `Bind`), `unify.rs:36,44`.**
On macOS these aren’t inlined — each call is a real `_tlv_get_addr` call.
~1 % of samples, but pure overhead on the hottest line. **Fix:** read `Config`
once per run and thread the booleans + deadline down as fields/params (folds
into A2). `Config` is `Copy` and never changes mid-run.

### Steering (don’t-optimize) notes
- **occurs-check is not hot** — leave it on; conditionally skipping it would
  risk soundness for no measurable gain.
- **`Env::extend_val`’s eager Var-chain resolution is load-bearing** (the chosen
  default). The addressable cost is the cons-list’s O(n) random access; only
  switch `Env` to a vector/RRB representation if profiling on a *deeper*
  workload shows `lookup` dominating (today it’s secondary to P2/P3).
- **BFS materializing the whole frontier** is inherent; the real memory issue is
  the arena (P3). Recommend `--fair` over `--bfs` as the default complete
  strategy in docs/CLI help.

---

## 5. Verified non-issues

These were raised and then **rejected** under adversarial verification — recorded
so the effort isn’t spent again:

- **`todo!()`/`unreachable!` arms in `occurs_lvar`/`unify` for suspensions** —
  the reviewers’ own analysis shows these are unreachable (`close_head` never
  returns `Ok(Susp)`); latent fragility, not a live bug.
- **`close()`’s `expect("unexpected suspension")`** — cannot fire today
  (Done-ness requires all suspensions drained); no triggering program exists.
- **Optimizer soundness** — `-o` vs no-`-o` produce identical solution multisets
  on every terminating example, across BFS/DFS/Fair; the de Bruijn increments in
  shift/subst/swap were checked and are correct.
- **Mixed `Nat(u64)`/`Zero`/`Succ` unify arms** — audited as exhaustive and
  correct (the `if *n > 0` guards bind `n` in both `|` alternatives).

(These overlap with A3/A4: the arms are *correct*, just *redundant* — clean them
up for simplicity, not correctness.)

---

## Suggested order of attack

1. **B1** (soundness) and **P1** (`[profile.release]`) — small, high-value, do now.
2. The reachable panics: **B2, B3, B11, B12, B10** — and reclassify A4’s
   user-reachable `panic!`/`todo!` to typed errors as you go.
3. **B4/B5** (make polymorphism and lambda arguments actually work) and **B6**
   (type-parser precedence) — these unbreak documented language features.
4. **C1 + C3** (collapse the `step.rs` boilerplate; turn the dead-code lint back
   on) and **A1** (one binder traversal) — the big readability wins.
5. **B7, B8, B9** (search-strategy correctness: residual answers, IDDFS
   counting, divergent-loop timeout) and **A2** (thread `Config`).
6. **P2/P3** (trail-based backtracking; arena reclamation) — the real scaling
   work, gated by the test suite + an `-o`/strategy solution-multiset diff test.
