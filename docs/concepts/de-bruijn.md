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
measured from the top (`translate.rs:27-33`):

```rust
self.env.iter().rev().position(|x| x == v)   // distance from the end
```

Every binder in the lowering pushes a name (`bind`) before translating its body and pops it
after (`unbind`), so indices stay consistent. Note that *intermediate* `Bind`s introduced by
lowering also occupy slots — that is why compound forms bind a placeholder `"_"` for each
sub-result (e.g. `Cons` at `translate.rs:455-466`, application at `:478-489`). Getting these
push/pop counts right is the whole correctness burden of the translator.

## Consumed at runtime

The runtime [[env|environment]] `Env` is a persistent cons-list of [[vclosure|`VClosure`]]s
backed by the arena (`env.rs`). `lookup(i)` walks `i` cells down the list (`env.rs:27`). A
binder step extends the list at the head — e.g. `Bind`'s continuation runs in
`env.extend_val(arena, v, env)` (`step.rs:109,136`), `Match`'s cons-branch pushes head then
tail (`step.rs:435-437`). Because `Env` is just a pointer to its head cell, cloning it (at a
[[nondeterminism|branch]]) is O(1).

A subtlety in `extend_val` (`env.rs`): if the value being pushed is itself a `Var`, the
environment **dealiases** it — following the variable chain through the given env rather than
stacking another layer of indirection. This keeps lookup chains short and is the eager
variable-resolution behaviour made default in commit `da38763`.

## The same scheme in the optimizer

The [[optimizer]] rewrites CBPV terms, so it must respect de Bruijn binding too. Its
`shift` / `subst` / `swap` passes (`optimize.rs`) each walk the term incrementing a binder
depth at exactly the binding forms (`Bind.cont`, `Lambda`, `Exists`, `Rec`, `Ifz.sk`,
`Case`, `Match.consk` at +2). [[deep-review]] §A1 notes these three traversals are
byte-identical and should share one generic walker — a depth mistake in any copy would
silently corrupt indices.

Related: [[translate]], [[env]], [[optimizer]], [[cbpv]].
