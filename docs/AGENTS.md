---
title: Wiki schema (read me first)
tags: [meta]
---

# How this wiki works

This directory is an **LLM-maintained wiki** documenting the `gweek` interpreter.
It follows the [llm-wiki](https://github.com/...) pattern, adapted for a codebase:
instead of ingesting external articles, the wiki tracks **source code**.

A human curates and asks questions; the LLM does the bookkeeping — writing pages,
keeping cross-references current, and **re-syncing pages when the code changes**.
You (the LLM) are a disciplined wiki maintainer, not a generic chatbot. Follow the
conventions and workflows below.

## Three layers

| Layer | Where | Who owns it |
|---|---|---|
| **Sources** | `../src`, `../examples`, `../web` | The code. Read-only from here. The source of truth. |
| **The wiki** | this `docs/` tree | The LLM writes it; humans read it. |
| **The schema** | this file (`AGENTS.md`) | Co-evolved by human + LLM. |

The one adaptation of the pattern that matters: **sources here mutate.** A codebase
changes under the wiki. So every page records *which code it describes*, and the
headline operation is **sync-to-code**, not "ingest a source." The enemy is drift.

## Conventions

**Frontmatter.** Every page starts with YAML:

```yaml
---
title: Human-readable title
tags: [component, machine]          # see taxonomy below
source: src/machine/step.rs         # the code this page tracks (omit for pure-concept pages)
commit: d83302b                     # short commit hash the page was last verified against
---
```

`source` + `commit` are what make drift detectable: if `git log -1 --format=%h -- <source>`
is newer than `commit`, the page is suspect. Pure-concept pages (e.g. [[cbpv]]) omit `source`.

**Wikilinks.** Link liberally with `[[basename]]` or `[[basename|display text]]`.
Basenames are unique across the wiki, so `[[step]]`, `[[unify]]`, `[[cbpv]]` all resolve.
A `[[link]]` to a page that doesn't exist yet is fine — it marks a page worth writing.

**`file:line` anchors.** Ground every concrete claim in a reference like
`step.rs:288` (the `Equate` arm) or `translate.rs:518` (`translate_bexpr`). These are
the single most important discipline: they let a reader jump to the code, and they let
the next sync pass find what moved. Prefer line *ranges* for blocks.

**Voice.** Describe what the code *does*, in present tense, concisely. Match the existing
pages. Don't editorialize; cross-link known problems instead (see below).

## Taxonomy (tags + folders)

| Folder | `tags` | Contents |
|---|---|---|
| `architecture/` | `architecture` | The big picture: [[overview]], [[pipeline]]. |
| `concepts/` | `concept` | Ideas, not files: [[cbpv]], [[logic-variables]], [[unification]], [[de-bruijn]], [[type-system]], [[nondeterminism]], [[search-strategies]], [[suspensions-and-forcing]]. |
| `components/` | `component` | One page per source module, each with a `source:` anchor. |
| `reference/` | `reference` | User-facing: [[cli]], [[grammar]], [[examples]]. |
| `review/` | `review` | Audits and findings: [[deep-review]]. Pages cross-link here for "known issues". |

## Workflows

**Document** (new page). Read the relevant source first-hand. Write the page with
frontmatter, `file:line` anchors, and wikilinks to related pages. Add a one-line entry
to [[index]] under the right category. Append to [[log]].

**Sync** (code changed). This is the main job. Given a commit or a changed file:
1. `git diff <range> -- <file>` to see what moved.
2. Re-read the changed regions.
3. Update every page whose `source:` points at that file — fix prose, fix `file:line`
   anchors, bump `commit:` to the new hash.
4. Check pages that *link to* the changed page for stale claims.
5. Append a `sync` entry to [[log]] naming the commit and the pages touched.

**Lint** (health check). Look for: pages whose `commit:` is behind their `source`'s last
commit; `file:line` anchors that no longer point where the prose claims; orphan pages with
no inbound links; concepts mentioned but lacking a page; contradictions between pages;
[[deep-review]] findings that have since been fixed (as of `d83302b`, **most have** — see the
banner on [[deep-review]]; only §P2, §P3, §A3 remain open).

## Known-issues convention

Pages describe current behaviour. Where a [[deep-review]] finding still reproduces against
current code, add a short callout linking the finding, e.g.:

> **Known issue.** Backtracking state is copy-on-write `Rc<UnionFind>`, so the first write on a
> shared clone deep-copies the whole store → O(N²) on deep search. See [[deep-review]] §P2.

Before adding such a callout, **verify the finding against current code** — the review is a
historical snapshot and most of its findings are already fixed.
