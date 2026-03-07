# Performance Notes: Forcing and Constraint Ordering

Gweek suspends non-trivial computations in `let` bindings. The suspension is
forced when the bound variable is used in a position that inspects its value
(a `case` scrutinee, or a `=:=` operand). If the variable is never used, the
suspension is only drained after the machine finishes. This has two practical
consequences for writing efficient programs.

## Issue 1: Unused let bindings are never forced during search

A `let` binding whose variable is never referenced will not be forced until the
machine drains remaining suspensions at the very end. If the binding was meant
to prune failing branches (via `absurd`), the pruning never happens during
search.

### Example: N-Queens (broken version)

```
safe :: Nat -> Nat -> [Nat] -> Nat
safe q d rest = case rest of
    [] -> 0
  | (r:rs) -> let c1 = neq (add q d) r in
               let c2 = neq (add r d) q in
               safe q (S d) rs.

queens :: [Nat] -> [Nat] -> [Nat] -> [Nat]
queens skipped rest placed = case rest of
    [] -> (case skipped of
        [] -> placed
      | (y:ys) -> absurdl 0)
  | (q:qs) ->
      (let c = safe q 1 placed in
       let remaining = revappend skipped qs in
       case remaining of
         [] -> (q : placed)
       | (y:ys) -> queens [] remaining (q : placed))
      <>
      (queens (q : skipped) qs placed).
```

`c`, `c1`, and `c2` are never used in their respective bodies. The `neq`
checks (which call `absurd` on conflict) are suspended and never forced. The
search explores all 8! = 40,320 permutations without pruning, causing it to
hang.

### Fix: use `case` to force the result

Replacing `let c = expr in body` with `case expr of Z -> body | S n -> absurd 0`
forces the computation immediately, because `case` needs to inspect the
scrutinee's head form, which triggers suspension forcing.

```
safe :: Nat -> Nat -> [Nat] -> Nat
safe q d rest = case rest of
    [] -> 0
  | (r:rs) -> case neq (add q d) r of
        Z -> (case neq (add r d) q of
            Z -> safe q (S d) rs
          | S n -> absurd 0)
      | S n -> absurd 0.

queens :: [Nat] -> [Nat] -> [Nat] -> [Nat]
queens skipped rest placed = case rest of
    [] -> (case skipped of
        [] -> placed
      | (y:ys) -> absurdl 0)
  | (q:qs) ->
      (case safe q 1 placed of
         Z -> (let remaining = revappend skipped qs in
               case remaining of
                 [] -> (q : placed)
               | (y:ys) -> queens [] remaining (q : placed))
       | S n -> absurdl 0)
      <>
      (queens (q : skipped) qs placed).
```

Now conflicting placements are pruned immediately. The 8-queens problem finds
all 92 solutions in seconds.

## Issue 2: Monolithic generation before constraint checking

Even when constraints are properly forced (via `=:=`), generating all
candidates as a single nondeterministic computation before checking any
constraints means every candidate is fully built before any pruning occurs.

### Example: Magic Square (slow version)

```
let sq = perm [1,2,3,4,5,6,7,8,9] in
exists a :: Nat. exists b :: Nat. exists c :: Nat.
exists d :: Nat. exists e :: Nat. exists f :: Nat.
exists g :: Nat. exists h :: Nat. exists i :: Nat.
sq =:= [a, b, c, d, e, f, g, h, i].
add3 a b c =:= 15.
add3 d e f =:= 15.
add3 g h i =:= 15.
add3 a d g =:= 15.
add3 b e h =:= 15.
add3 c f i =:= 15.
add3 a e i =:= 15.
add3 c e g =:= 15.
sq.
```

Here `=:=` does force eagerly, so this is not Issue 1. The problem is that
`perm` generates all 9! = 362,880 permutations. Each one is fully constructed
before `sq =:= [a,b,c,...]` binds the logic variables and the sum constraints
can run. No pruning happens until a complete permutation exists.

### Fix: interleave selection and constraint checking

Replace the monolithic `perm` with incremental element selection using `pick`,
and check row-sum constraints as soon as each row of 3 is complete:

```
pick :: [Nat] -> [Nat] -> [Nat]
pick skipped rest = case rest of
    [] -> absurdl 0
  | (x:xs) -> (x : revappend skipped xs)
              <> (pick (x : skipped) xs).

exists a :: Nat. exists b :: Nat. exists c :: Nat.
exists d :: Nat. exists e :: Nat. exists f :: Nat.
exists g :: Nat. exists h :: Nat. exists i :: Nat.
case pick [] [1,2,3,4,5,6,7,8,9] of [] -> absurdl 0 | (a1:r1) ->
a1 =:= a.
case pick [] r1 of [] -> absurdl 0 | (b1:r2) ->
b1 =:= b.
case pick [] r2 of [] -> absurdl 0 | (c1:r3) ->
c1 =:= c.
add3 a b c =:= 15.
case pick [] r3 of [] -> absurdl 0 | (d1:r4) ->
d1 =:= d.
case pick [] r4 of [] -> absurdl 0 | (e1:r5) ->
e1 =:= e.
case pick [] r5 of [] -> absurdl 0 | (f1:r6) ->
f1 =:= f.
add3 d e f =:= 15.
case pick [] r6 of [] -> absurdl 0 | (g1:r7) ->
g1 =:= g.
case pick [] r7 of [] -> absurdl 0 | (h1:r8) ->
h1 =:= h.
case pick [] r8 of [] -> absurdl 0 | (i1:r9) ->
i1 =:= i.
add3 g h i =:= 15.
add3 a d g =:= 15.
add3 b e h =:= 15.
add3 c f i =:= 15.
add3 a e i =:= 15.
add3 c e g =:= 15.
[a, b, c, d, e, f, g, h, i].
```

After picking a, b, c, the check `add3 a b c =:= 15` runs immediately and
prunes the vast majority of branches before d, e, f are ever chosen. The slow
version takes 30+ seconds; the fast version completes instantly.

## Summary

| Pattern | Problem | Fix |
|---------|---------|-----|
| `let c = side_effect in body` (c unused) | Suspension never forced | Use `case side_effect of ...` |
| Generate all candidates, then filter | Constraints applied too late | Interleave generation and checking |
