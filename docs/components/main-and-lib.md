---
title: main.rs & lib.rs — entry points
tags: [component]
source: src/main.rs
commit: 6ec7c97
---

# `main.rs` & `lib.rs`

The two ways to run gweek. Both run the same [[pipeline]].

**`main.rs` — the CLI.** Parses flags (`main.rs:27-72`) and **constructs a [[config|`Config`]]**
(`:79-86`) — passed by value into the pipeline, no thread-local ([[deep-review]] §A2). Then
parse → type-check → translate → optionally optimize → [[eval|`eval`]] (`:88-117`). Parse and
type errors are rendered with the `ariadne` crate and exit non-zero (`report_errors`,
`:120-159`). The user-facing flags are catalogued in [[cli]]. Integration tests at the bottom
pin solution counts for `perm`, `find_list`, `nqueens`.

**`lib.rs` — library + WASM.** Re-exports `machine`, `parser`, `type_check`. The generic
`run_with` (`lib.rs:14-69`) builds a `Config` (`:36-43`) and wires the pipeline for the web
build; two `#[wasm_bindgen]` exports drive it: `run_gweek` (`:104`) streams solutions to a JS
callback via [[eval|`eval_streaming`]], `run_gweek_batch` (`:132`) returns them in one string
via `eval_collect`. `format_parse_errors` (`:72`) renders parse errors for the browser. The
playground in `web/` calls these.

Related: [[cli]], [[pipeline]], [[config]], [[eval]], [[parser]], [[type-checker]].
