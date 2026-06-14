---
title: type_check.rs — the type checker
tags: [component, stub]
source: src/type_check.rs
commit: d83302b
---

# `type_check.rs` *(stub — expand on demand)*

A two-pass bidirectional type checker with Hindley–Milner-style instantiation.
`type_check(&ast) -> Result<(), Vec<TypeError>>` (`type_check.rs:254`) collects function
signatures first (`:259-263`), then checks each body and bare statement (`:266-282`). The
conceptual treatment is in [[type-system]].

**Key pieces:**

- `TypeError` (`:15`) and `TResult<T> = Result<T, TypeError>` (`:25`) — the typed error channel.
- `Ctx` (`:31`) — locals `vars`, global `funcs`, and `subst` (the metavariable substitution).
- `unify(expected, actual)` (`:211`) — Robinson unification over metavariables, with an occurs
  check (`:204-209`).
- `instantiate` (`:83`) / `fresh_meta` (`:74`) — give each *use* of a polymorphic signature
  fresh metavariables (`?0`, `?1`, …).
- `synth_stmt` / `synth_expr` — synthesis; `check_expr` (`:510`) / `check_stmt` (`:542`) —
  checking; `resolve_type` (`:580`).

**Findings now resolved** ([[deep-review]]):

- **B4** — real polymorphism: `instantiate` (`:83`) maps each signature type variable to a
  fresh metavariable per use, so `id :: a -> a` applies at concrete types. Not string equality.
- **B5** — `check_expr` is now called from `App`'s argument position (`:492`), so a lambda
  passed as an argument is checked against the known parameter type (tests `:651-657`).
- **B11** — `resolve_type` rejects `Int` as unknown (`:585`); it no longer slips through to
  panic in [[translate|translation]].
- **C3** — the blanket `unused = "allow"` is gone and the formerly-dead checking functions are
  live.

Related: [[type-system]], [[pipeline]], [[parser]], [[translate]], [[value-type]].
