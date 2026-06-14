---
title: De Bruijn indices
tags: [concept]
---

# De Bruijn indices

gweek has no variable *names* at runtime. A variable is `MValue::Var(usize)`
([[mterms]], `mterms.rs:13`) — a **de Bruijn index** counting binders outward from the use
site: `Var(0)` is the most recently bound variable, `Var(1)` the one before, and so on. This
removes the need for capture-avoiding substitution and makes environments simple stacks.

## Established at translation

[[translate|`translate`]] converts surface names to indices. It threads a name stack
`TEnv` (`translate.rs:10`); `find(v)` returns the index of the *last* binding of `v`,
measured from the end (`translate.rs:31-36`):

```rust
self.env.iter().rev().position(|x| x == v)   // distance from the end
```

Every binder in the lowering pushes a name before translating its body and pops it after, so
indices stay consistent. Note that *intermediate* `Bind`s introduced by lowering also occupy
slots — that is why compound forms bind a placeholder for each sub-result. Getting these
push/pop counts right is the whole correctness burden of the translator.

## Consumed at runtime

The runtime [[env|environment]] `Env` is a persistent cons-list of [[vclosure|`VClosure`]]s
backed by the arena (`env.rs`). `lookup(i)` walks `i` cells down the list (`env.rs:27`). A
binder step extends the list at the head — e.g. `Bind`'s continuation runs in
`env.extend_val(arena, v, env)`, `Match`'s cons-branch pushes head then tail ([[step]]).
Because `Env` is just a pointer to its head cell, cloning it (at a [[nondeterminism|branch]])
is O(1).

A subtlety in `extend_val` (`env.rs:44-50`): if the value being pushed is itself a `Var`, the
environment **dealiases** it — following the variable chain through the given env rather than
stacking another layer of indirection. This keeps lookup chains short and is the eager
variable-resolution behaviour made default in commit `da38763`.

## The same scheme in the optimizer

The [[optimizer]] rewrites CBPV terms, so it must respect de Bruijn binding too. It does this
through a **single** generic binder-aware traversal — `map_val`/`map_comp` (`optimize.rs:116`,
`:140`) — that carries a `binders` depth and increments it at exactly the binding forms. The
`shift` / `subst` / `swap` passes are now thin callbacks over it (`:207`, `:225`, `:297`), so
the depth bookkeeping is written once instead of triplicated ([[deep-review]] §A1, fixed in
commit `fe70c5d`).

Related: [[translate]], [[env]], [[optimizer]], [[cbpv]].
