---
title: Wiki log
tags: [meta]
---

# Log

Append-only record of wiki activity. Each entry starts with `## [date] kind | summary`
so the log is greppable: `grep "^## \[" log.md | tail -5`.

## [2026-06-13] bootstrap | initial spine

Created the wiki against commit `7972077` (spine-first scope).

- Schema [[AGENTS]], home [[index]], this log.
- Architecture: [[overview]], [[pipeline]].
- Concepts: [[cbpv]], [[logic-variables]], [[unification]], [[nondeterminism]],
  [[de-bruijn]], [[type-system]]; folded existing `notes.md` → [[suspensions-and-forcing]]
  and `search-strategies.md` → [[search-strategies]].
- Full component pages: [[mterms]], [[step]], [[eval]], [[unify]], [[translate]].
- Stubs (one paragraph + `source:` + links): [[parser]], [[type-checker]], [[optimizer]],
  [[lvar]], [[union-find]], [[senv]], [[env]], [[vclosure]], [[value-type]], [[config]],
  [[main-and-lib]].
- Reference: [[cli]], [[examples]]; [[grammar]] stub.
- Moved the standing audit to [[deep-review]]. Noted **B1 is fixed** as of `0f34f45`
  (union-find now canonicalizes through `Root`).

Built on branch `docs/llm-wiki` in a worktree, because a refactor was in flight on `main`.
The component pages' `file:line` anchors are pinned to `7972077` and will need a **sync**
pass once that refactor lands.
