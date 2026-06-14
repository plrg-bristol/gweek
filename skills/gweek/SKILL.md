---
name: gweek
description: Use the gweek functional-logic language to enumerate or invert over SMALL, FINITE, first-order structural problems — e.g. enumerate all inputs a forward predicate accepts (validator-as-generator), or run a recursive function backwards to find inputs producing a given output (inversion). Narrow scope: NOT for numeric/arithmetic-heavy, optimization, string, or large problems, and NOT for checking real production code — prefer property-based testing (proptest/Hypothesis), an SMT solver (Z3), or a model finder (Alloy) for those.
---

# gweek

gweek is a functional-logic language with sound, complete search over first-order
data (`Nat`, lists, pairs, sums, `Bool`). You write ordinary functions; the engine
runs them forwards *or backwards* and enumerates every value satisfying a set of
constraints. Build with `cargo build`; the binary is `target/debug/gweek`.

## When this is the right tool

Only when the problem is **small, finite, structural, and first-order**, and one fits:

- **Validator → generator** — write a forward predicate, get all (small) inputs it accepts.
- **Inversion** — have a recursive function, find inputs that produce a given output.
- **Enumeration / counterexample** — get all witnesses of a constraint, or one, deterministically.

## When NOT to use it (reach for something else)

- **Numeric / arithmetic-heavy**, or numbers past a few hundred — naturals are unary (Peano). → **Z3 / MiniZinc**.
- **Optimization** (best, not just any solution) — gweek finds solutions, not optima. → **OR-Tools / MiniZinc**.
- **Strings, floats, I/O** — unsupported.
- **Checking real production code** — gweek runs your *re-transcription*, not the real function, so a faithful encoding is on you. → **property-based testing** (proptest / Hypothesis / fast-check), or **Alloy / Kani**.
- **Large search spaces** — keep bounds small.

If a mainstream tool fits, use it. gweek's only genuine edge is running ordinary
functional code *backwards* without hand-rewriting it as a relation.

## Invoke (CLI + heredoc)

```sh
target/debug/gweek --fair [--first] --timeout 5 /dev/stdin <<'EOF'
... program ...
EOF
```

Rules of thumb: **always `--fair`** (complete + lean; never `--bfs` unattended) ·
**always an explicit short `--timeout`** · add **`--first`** when one witness suffices.

## Read the result — the `>>>` line is the whole signal

- `> <value>` — one solution, printed in source syntax.
- `>>> N solutions` — search **finished**: these are *all* solutions (sound, up to whatever bound you imposed).
- `>>> timed out after Ns, M solutions found` — **inconclusive**: more may exist.
- Parse / type errors print to **stderr**, exit code **1**.
- A finished run and a timeout **both exit 0** — so you must read the `>>>` line; never infer "complete vs. gave up" from the exit code.

## Pattern 1 — validator as generator

Write the check forward, enumerate the inputs it accepts. (`<>` is non-deterministic choice.)

```sh
target/debug/gweek --fair --timeout 5 /dev/stdin <<'EOF'
color :: Nat
color = 0 <> 1 <> 2.

valid :: Nat -> Nat -> Nat -> Bool
valid a b c = (a != b) && (b != c).

let a = color in
let b = color in
let c = color in
if valid a b c then [a, b, c] else fail.
EOF
```

→ the 12 proper 3-colorings of a 3-node path (no two adjacent equal).

## Pattern 2 — inversion (run a function backwards)

```sh
target/debug/gweek --fair --timeout 5 /dev/stdin <<'EOF'
add :: Nat -> Nat -> Nat
add n m = case m of Z -> n | S z -> S (add n z).
exists a :: Nat. exists b :: Nat. add a b =:= 5. (a, b).
EOF
```

→ `(5,0) (4,1) (3,2) (2,3) (1,4) (0,5)` — every way to sum to 5, by running `add` backward.

## Syntax gotchas

- Every declaration and statement ends with `.` (a period).
- `<>` is **non-deterministic choice**, not append / `mappend`.
- `=:=` is **unification** (constrain two terms equal); `==` `!=` `&&` `||` are boolean ops.
- `exists x :: T. rest` introduces a logic variable to search over; `fail` prunes a branch (`if cond then result else fail` filters).
- `case` matches **only** `Z`/`0`, `S n`, `[]`, `(x:xs)` — no other literals, no pair/sum patterns. Destructure a pair in a function arg instead: `f (x, y) = ...`.
- Types: `Nat` (with `Z`, `S`, literals), `[a]`, `(a, b)`, `Bool`. Keep numbers small (unary naturals).
- **Bound the search**, or it may not terminate: constrain a length/value (`length xs =:= 7.`), or use `--first` / `--timeout`. An unbounded `exists` over lists or naturals runs forever.

Full grammar: `docs/reference/grammar.md`. More examples: `examples/`.
