---
title: The source-to-CBPV translation
tags: [concept]
---

# The source-to-CBPV translation

[[cbpv|CBPV]] describes the *target* language — values, computations, and the forms the machine
steps. This page describes the **translation** itself: how the type-checked surface AST becomes a
CBPV computation, written out rule by rule. The translation is performed by `elaborate_expr` (and
its top-level helpers `elaborate_func` / `elaborate_group`), which also replaces names by
[[de-bruijn|de Bruijn indices]]; below we keep the names, for readability.

## The slogan

> gweek's elaboration is **Levy's call-by-value translation into CBPV, with the strict bind `to`
> replaced everywhere by the by-need bind `need`** — and `let strict` the sole place `to` survives.

That one line fixes everything else. The translation is *not* the call-by-name translation made
lazy (see [below](#why-call-by-value-and-not-call-by-name)); it is the call-by-value skeleton —
every subterm sequenced, a variable is `return x`, a function is a thunk of a lambda — with
laziness pushed entirely into the bind rather than the type structure.

## Values, computations, and the two binds

Every source expression `e : A` maps to a **computation** `⟦e⟧ : F Aᵛ` — a *returner* of a value
of `A`'s translated type. The bridge back to a value is `return`; sequencing one computation's
result into another is the bind, and gweek has two (see [[cbpv]]):

```
M need x. N    by-need sequencing  — the elaborator's `seq`, emitting Need.  gweek's default.
M to   x. N    strict  sequencing  — Bind. Reached only from `let strict`.
```

In `M need x. N`, if `M` is literally `return v` then `x` is bound to `v` directly; otherwise `M`
is frozen as a **memoised suspension** and `x` is bound to that ([[suspensions-and-forcing]]).
Either way `x` denotes the *value* `M` returns — it is not a thunk you must force. An eliminator
forces the suspension on demand when it [[suspensions-and-forcing|head-closes]] its scrutinee, and
that on-demand forcing is what lets narrowing prune the search.

## Types

On types the call-by-value translation `·ᵛ` sends a function type to a thunk of a CBPV arrow:

```
(A → B)ᵛ  =  U (Aᵛ → F Bᵛ)
```

so a gweek function is a **value** (a thunk), and `⟦e : A⟧ : F Aᵛ`. Ground types translate to the
obvious value types: `Nat`, lists, products as themselves, and `Bool` as `Sum(Unit, Unit)` with
`true = inl ⟨⟩`, `false = inr ⟨⟩` (`elaborate_vtype`).

## Notation

```
⟦e⟧                       the computation translating source expression e   (type F A)
return v                  Return                  { M } / force v            Thunk / Force
λx. M   /   M v           Lambda  /  App          rec f. M                   Rec
M need x. N  /  M to x. N  by-need / strict bind   (Need / Bind)
ifz v { M } { x. N }                              Nat eliminator   (Ifz)
match v { M } { x xs. N }                         list eliminator  (Match)
case v { inl a. M } { inr b. N }                  sum eliminator   (Case)
∃ x:τ. M                  Exists      v =:= w. M  Equate-then-M
M₁ <> … <> Mₙ             Choice      fail        the empty Choice
```

## The translation

**Variables and literals.** A plain variable returns its value; a nullary (CAF) function is a
thunk that must be forced; a member of a mutually-recursive group is reached through the group's
selector (see [Top-level declarations](#top-level-declarations)).

```
⟦x⟧        = return x                  -- ordinary variable
⟦f⟧        = force f                   -- f a nullary function
⟦fᵢ⟧       = (force bundle) i          -- fᵢ a member of a mutual group
⟦Z⟧ / ⟦n⟧  = return n
⟦[]⟧       = return nil
⟦true⟧     = return (inl ⟨⟩)
⟦false⟧    = return (inr ⟨⟩)
```

**Data constructors.** Each argument is sequenced by-need, left to right, so constructors are
lazy in their components.

```
⟦S e⟧        = ⟦e⟧  need x. return (S x)
⟦e₁ : e₂⟧    = ⟦e₁⟧ need h. ⟦e₂⟧ need t. return (h :: t)
⟦(e₁, e₂)⟧   = ⟦e₁⟧ need a. ⟦e₂⟧ need b. return (a, b)
⟦[e₁,…,eₙ]⟧  = ⟦e₁ : … : eₙ : []⟧     -- list sugar: nested cons
```

**Functions and application.** A lambda is a *value* (a thunk); application sequences both sides
by-need and forces the function before applying.

```
⟦\x. e⟧      = return { λx. ⟦e⟧ }
⟦e₁ e₂⟧      = ⟦e₁⟧ need f. ⟦e₂⟧ need a. (force f) a
```

**`let` (by-need) versus `let strict` (the sole strict construct).**

```
⟦let x = e₁ in e₂⟧         = ⟦e₁⟧ need x. ⟦e₂⟧     -- Expr::Let
⟦let strict x = e₁ in e₂⟧  = ⟦e₁⟧ to   x. ⟦e₂⟧     -- Expr::LetStrict
```

**Control.** The scrutinee is sequenced by-need, then eliminated. `if` is a `case` on the `Bool`
sum, discarding the unit payload.

```
⟦if e₁ then e₂ else e₃⟧
        = ⟦e₁⟧ need b. case b { inl _. ⟦e₂⟧ } { inr _. ⟦e₃⟧ }

⟦case e of Z → e₀ | S n → e₁⟧
        = ⟦e⟧ need s. ifz s { ⟦e₀⟧ } { n. ⟦e₁⟧ }

⟦case e of [] → e₀ | x:xs → e₁⟧
        = ⟦e⟧ need s. match s { ⟦e₀⟧ } { x xs. ⟦e₁⟧ }
```

**Logic core** ([[logic-variables]], [[unification]], [[nondeterminism]]). The `=:=` form unifies
its two operands against the constraint store and then runs the body; `a` and `b` stay in scope in
`e₃`. The unification binds no fresh value of its own.

```
⟦exists x::τ. e⟧  = ∃ x:τ. ⟦e⟧
⟦e₁ =:= e₂. e₃⟧   = ⟦e₁⟧ need a. ⟦e₂⟧ need b. (a =:= b. ⟦e₃⟧)
⟦fail⟧            = fail                       -- the empty Choice
⟦e₁ <> … <> eₙ⟧   = ⟦e₁⟧ <> … <> ⟦eₙ⟧
```

**Booleans.** Equality is Nat-only and uses a fixed closed recursive thunk `eqℕ` (built by
`nat_eq_thunk`, applied by `nat_eq_comp`); `&&` and `||` short-circuit by casing on the left
operand.

```
neg M        = M need b. case b { inl _. return false } { inr _. return true }
⟦e₁ == e₂⟧   = ⟦e₁⟧ need a. ⟦e₂⟧ need b. (force eqℕ) a b
⟦e₁ != e₂⟧   = neg ⟦e₁ == e₂⟧
⟦!e⟧         = neg ⟦e⟧
⟦e₁ && e₂⟧   = ⟦e₁⟧ need b. case b { inl _. ⟦e₂⟧ }       { inr _. return false }
⟦e₁ || e₂⟧   = ⟦e₁⟧ need b. case b { inl _. return true } { inr _. ⟦e₂⟧ }
```

A fully-literal boolean or arithmetic operand is constant-folded first (`const_bool`), but that is
an optimisation layered on these rules, not part of the semantics.

## Top-level declarations

A function definition becomes a **thunk of a `rec`** over a curried lambda chain; currying
re-thunks every non-final stage (`build_args` / `curry`):

```
⟦f x₁ … xₙ = e⟧ᵈ  = { rec f. λx₁. return { λx₂. return { … λxₙ. ⟦e⟧ } } }
⟦f = e⟧ᵈ          = { rec f. ⟦e⟧ }     -- nullary (CAF); used via `force f`
```

The machine's `Rec` binds a single self-reference, so a genuinely **mutually-recursive group**
cannot be tied with a per-function `rec`. The group instead collapses to one selector-dispatched
fixpoint (`elaborate_group`):

```
bundleᵈ = { rec self. λsel. ifz sel { return {f₀} } { _. ifz · { return {f₁} } … } }
```

Every reference to member `i` — from a sibling, from itself, or from an outside caller — goes
through `(force bundle) i`, which returns member `i`'s thunk; that shared `self` is what makes the
recursion genuinely mutual. The groups are found and dependency-ordered by Tarjan's SCC algorithm
before elaboration.

## Why call-by-value and not call-by-name

There are two lazy translations into CBPV, on *different* skeletons. The discriminator is
application:

```
gweek (CBV skeleton, to:=need):  ⟦e₁ e₂⟧ = ⟦e₁⟧ need f. ⟦e₂⟧ need a. (force f) a
Levy CBN:                        (e₁ e₂)ⁿ = e₁ⁿ { e₂ⁿ }
```

In the call-by-name translation there is **no `to` to replace**: the argument is thunked and
pushed unevaluated, the function runs directly as a computation, variables are `force x`, and types
go `(A → B)ⁿ = U Aⁿ → Bⁿ`. You make *that* lazy-with-sharing by giving thunks memoisation — not by
inserting a `need`. gweek does the opposite throughout: `⟦x⟧ = return x`, functions are
`U(Aᵛ → F Bᵛ)`, every subterm sequenced — the pure call-by-value skeleton — with laziness living
in the bind.

"Call-by-value skeleton + by-need bind" is itself a standard presentation of call-by-need (the
"call-by-need = call-by-value with a non-strict, sharing `let`" view). So gweek *is* a call-by-need
translation; what it is **not** is the call-by-name translation made lazy.

The choice is forced by the logic-programming side, not incidental. Narrowing and
[[unification]] need data to be inert, first-order **values** ([[logic-variables|`MValue`]]
`Zero`/`Succ`/`Cons`/…) that can sit in the union-find store and be inspected. The call-by-name
translation represents everything as thunked computations `U Aⁿ`, with nothing first-order to
unify. gweek therefore keeps the call-by-value value representation and recovers laziness through
the bind discipline.

## Why the bind discipline matters

Because the term skeletons for `to` and `need` are identical, the *only* semantic content of the
choice is which bind sits at each sequencing point — and that is exactly the subject of
[[powerdomains-and-binding]]. By-need discharges the **right-zero** law (it never starts `M` when
the continuation fails) but loses **left-zero**; strict `Bind` is the mirror image. Defaulting to
`need` prunes the search cheaply and validates right-zero termination-sensitively; `let strict` is
the one knob that hands the strict `to` back, validating left-zero on the bound failure before the
body runs. Neither is "more correct" under gweek's [[powerdomains-and-binding|lower-powerdomain]]
reading — both are adequate, provided the [[search-strategies|search is complete]].

Related: [[cbpv]] (the target term language), [[suspensions-and-forcing]] (how `need` memoises),
[[powerdomains-and-binding]] (the `to`-vs-`need` law trade-off), [[de-bruijn]] (the index
representation this page suppresses), [[grammar]] (the surface syntax on the left of each rule).
