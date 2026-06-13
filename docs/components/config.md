---
title: config.rs — runtime configuration
tags: [component, stub]
source: src/machine/config.rs
updated: 7972077
---

# `config.rs` *(stub — expand on demand)*

`Config` (`config.rs:23`) holds the run-time knobs: `strategy` ([[search-strategies|`Strategy`]]),
`optimize`, `timeout_secs`, `occurs_check`, `strict`, `first_only` — the in-memory form of the
[[cli|CLI flags]]. It lives in a **thread-local** `Cell` alongside a computed `DEADLINE`
(`:11-19`); `init(cfg)` (`:32`) sets both, `config()` (`:37`) and `deadline()` (`:41`) read
them. On WASM it uses `web_time::Instant`.

> **Architecture note.** Config is split between this thread-local global and explicit args to
> [[eval|`run`]], giving two sources of truth and a testability hazard; the thread-local
> accessor is also a non-inlined call on the hot path on macOS. [[deep-review]] §A2 and §P5
> recommend threading one immutable `&Config` (with an absolute-`Instant` deadline) and
> deleting the thread-local.

Related: [[cli]], [[eval]], [[search-strategies]], [[main-and-lib]].
