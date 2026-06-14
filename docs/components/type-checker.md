---
title: type_check.rs — the type checker
tags: [component]
source: src/type_check.rs
commit: 6ec7c97
---

# `type_check.rs`

A two-pass bidirectional type checker with Hindley–Milner-style instantiation.
`type_check(&ast) -> Result<(), Vec<TypeError>>` (`type_check.rs:254`) collects function
signatures into `ctx.funcs` first (`:259-263`), then checks each `Func` body and bare `Stmt`
(`:266-282`), accumulating every `TypeError` rather than stopping at the first. The conceptual
treatment is in [[type-system]].

## Errors and context

- `TypeError { msg }` (`:15`) with a `Display` impl (`:19`), and `TResult<T = Type>`
  (`:25`) — the typed error channel; `err(msg)` (`:27`) is the constructor.
- `Ctx` (`:31`) holds `vars` (a stack of local `(name, Type)`), `funcs` (the global signature
  map), and `subst` (the metavariable substitution, a `Vec<Option<Type>>` indexed by metavar
  id). Metavariables are encoded as `Type::Ident("?<id>")` — a name the lexer can never produce
  (`:34-37`), so they cannot clash with user type variables.

## Unification

- `unify(expected, actual)` (`:211`) is Robinson unification: it `resolve`s both heads
  (`:167`), short-circuits on `Type::Any` (the wildcard), binds an unbound metavar to the other
  side, and recurses structurally over `List`/`Product`/`Arrow`.
- `bind_meta` (`:198`) performs the occurs check via `occurs` (`:179`), rejecting infinite
  types ("cannot construct infinite type").
- `peel_arrows(ty, n)` (`:238`) splits a function type into its first `n` argument types and the
  return type, for checking a function against its arity.

## Polymorphism by instantiation

`instantiate` (`:83`) / `instantiate_with` (`:88`) replace each distinct *signature* type
variable (a lowercase-initial `Ident`, per `is_type_var` `:42`) with a fresh metavar from
`fresh_meta` (`:74`), consistently within one use, so `a -> a` becomes `?0 -> ?0`. Only global
functions are generalized: `lookup` (`:107`) returns local bindings monomorphically but
instantiates `funcs` entries at every use site (`:117-120`). This is real instantiation, not
string equality.

## Bidirectional checking

- **Synthesis**: `synth_stmt` (`:318`) and `synth_expr` (`:444`) compute a term's type bottom-up.
  `synth_case` (`:374`) handles `Nat`/`List` scrutinees and unifies the branch result types.
- **Checking**: `check_expr` (`:510`) / `check_stmt` (`:542`) push an expected type down. The
  `App` case of `synth_expr` (`:488-498`) resolves the operator type and **checks** the
  argument against the parameter type (`check_expr(ctx, arg, &param)`, `:492`), which is how a
  lambda — otherwise un-synthesisable (`:500-502`) — gets a type. `check_expr` peels a
  parenthesising `Expr::Stmt` (`:530`) so a parenthesised lambda is still checked.
- `resolve_type` (`:580`) validates a surface type written in `exists`/signatures: only `Nat`,
  `Bool`, lists, and products of those are admitted; any other `Ident` (e.g. `Int`) is rejected.

## Findings now resolved ([[deep-review]])

- **B4** — real polymorphism: `instantiate` (`:83`) gives each use of a signature fresh
  metavars, so `id :: a -> a` applies at any concrete type (tests `:632-640`), while
  `bad :: a -> b` rejects `bad x = x` (test `:644-647`).
- **B5** — `check_expr` is called from `App`'s argument position (`:492`), so a lambda passed as
  an argument is checked against the known parameter type (tests `:649-658`).
- **B11** — `resolve_type` rejects `Int` as an unknown type (`:585`) instead of letting it slip
  through to a panic in [[translate|translation]] (test `:660-664`).
- **A4** — conditions that used to type-check and then panic downstream are now clean type
  errors: `==`/`!=` are Nat-only (`synth_bexpr` `:554-564`; test `:668-672`), and pair-pattern
  *lambda* arguments are rejected (`:519`) because translation has no annotation for them
  (tests `:674-684`). Pair-pattern *function* arguments are accepted (`bind_arg` `:131`), but
  only at concrete component types (`is_concrete_value_type` `:56`), matching what
  [[translate]] can lower.
- **C3** — the blanket `unused = "allow"` is gone and the checking functions are live.

Related: [[type-system]], [[pipeline]], [[parser]], [[translate]], [[value-type]].
