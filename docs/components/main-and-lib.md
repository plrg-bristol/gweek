---
title: main.rs & lib.rs — entry points
tags: [component, stub]
source: src/main.rs
updated: 7972077
---

# `main.rs` & `lib.rs` *(stub — expand on demand)*

The two ways to run gweek. Both run the same [[pipeline]].

**`main.rs` — the CLI.** Parses flags (`main.rs:28-72`) into a [[config|`Config`]], calls
`config::init`, reads the source file, then runs parse → type-check → translate → optionally
optimize → [[eval|`eval`]] (`:88-117`). Parse and type errors are rendered with the `ariadne`
crate and exit non-zero (`:120-159`). The user-facing flags are catalogued in [[cli]].
Integration tests at the bottom (`:162-236`) pin solution counts for `perm`, `find_list`,
`nqueens`.

**`lib.rs` — library + WASM.** Re-exports `machine`, `parser`, `type_check`. The generic
`run_with` (`lib.rs:12-67`) wires the pipeline for the web build; two `#[wasm_bindgen]`
exports drive it: `run_gweek` (`:102`) streams solutions to a JS callback via
[[eval|`eval_streaming`]], `run_gweek_batch` (`:130`) returns them in one string via
`eval_collect`. The browser [[examples|playground]] in `web/` calls these.

Related: [[cli]], [[pipeline]], [[config]], [[eval]], [[parser]], [[type-checker]].
