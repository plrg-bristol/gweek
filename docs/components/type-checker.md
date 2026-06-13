---
title: type_check.rs — the type checker
tags: [component, stub]
source: src/type_check.rs
updated: 7972077
---

# `type_check.rs` *(stub — expand on demand)*

A two-pass bidirectional type checker. `type_check(&ast) -> Result<(), Vec<TypeError>>`
(`type_check.rs:129`) collects function signatures first (`:134-138`), then checks each body
and bare statement (`:141-158`). The conceptual treatment, including the system's gaps, is in
[[type-system]].

**Key pieces:**

- `Ctx` (`:31`) — locals stack `vars` + global `funcs` map; `bind`/`unbind`/`bind_arg`.
- `unify(expected, actual)` (`:95`) — structural equality; `Type::Any` matches anything.
- `peel_arrows(ty, n)` (`:113`) — split a function type into *n* args + return.
- `synth_stmt` (`:193`) / `synth_expr` (`:319`) — synthesis; `check_expr` (`:387`) — checking
  (currently dead, [[deep-review]] §B5); `synth_case` (`:249`); `synth_bexpr` (`:406`);
  `resolve_type` (`:429`).

> **Known issues.** No real polymorphism (string-equal type vars, §B4); `check_expr`/
> `resolve_return_type` are dead, so lambda arguments are rejected (§B5); `Int` and boolean
> expressions pass here but panic in [[translate|translation]] (§B11, §B2).

Related: [[type-system]], [[pipeline]], [[parser]], [[translate]], [[value-type]].
