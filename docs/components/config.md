---
title: config.rs — runtime configuration
tags: [component]
source: src/machine/config.rs
commit: 6ec7c97
---

# `config.rs`

`Config` (`config.rs:3-11`) holds the run-time knobs: `strategy`
([[search-strategies|`Strategy`]]), `optimize`, `timeout_secs`, `occurs_check`, `strict`,
`first_only` — the in-memory form of the [[cli|CLI flags]]. It is a **plain struct passed by
reference**: [[eval|`eval`/`run`]], [[step|`run_to_branch`/`step`]] and [[unify|`unify`]] all
take `cfg: &Config` explicitly, and the deadline is computed once
([[eval|`deadline_from`]]) and threaded down as an absolute `Instant`.

> **History.** This used to be a thread-local `Cell<Config>` with `init`/`config`/`deadline`
> accessors read ad-hoc deep in the machine — two sources of truth, a test hazard, and a
> non-inlined TLS call on the hottest line. Threading `&Config` and deleting the thread-local
> resolved [[deep-review]] §A2 and §P5. (This page was re-synced to that change.)

Related: [[cli]], [[eval]], [[search-strategies]], [[main-and-lib]].
