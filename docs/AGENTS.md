---
title: Wiki schema (read me first)
tags: [meta]
---

# How this wiki works

This directory is an **LLM-maintained wiki** documenting the `gweek` interpreter.
It follows the [llm-wiki](https://github.com/...) pattern, adapted for a codebase:
instead of ingesting external articles, the wiki tracks **source code**.

A human curates and asks questions; the LLM does the bookkeeping — writing pages
and keeping cross-references current. You (the LLM) are a disciplined wiki
maintainer, not a generic chatbot. Follow the conventions and workflows below.

## Scope: what belongs here, what doesn't

The codebase is small (~6,800 lines) and now carries **module-level rustdoc** — a
`//!` header on every module explaining what it is and how it fits. That is the
canonical per-module reference. Read it with:

```
cargo doc --no-deps --document-private-items --open
```

So **this wiki does not mirror the source module-by-module.** Per-file write-ups
drift the moment the code moves (every line shifts), and they duplicate what the
rustdoc already says next to the code. We deleted the old `components/` pages for
exactly this reason — their job is the rustdoc's now.

The wiki covers what reading the code *won't* readily give you:

- **Concepts** — the ideas the implementation rests on (CBPV, logic variables,
  unification, de Bruijn, …). These are durable; they don't move with the code.
- **Architecture** — the one-screen picture of how the parts fit.
- **Reference** — user-facing material (CLI, grammar, examples).
- **Review** — the standing audit ([[deep-review]]).

If you're tempted to write a page that restates one source file, write or improve
the rustdoc `//!` header instead.

## Three layers

| Layer | Where | Who owns it |
|---|---|---|
| **Sources** | `../src`, `../examples`, `../web` | The code (+ its rustdoc). Read-only from here. The source of truth. |
| **The wiki** | this `docs/` tree | The LLM writes it; humans read it. |
| **The schema** | this file (`AGENTS.md`) | Co-evolved by human + LLM. |

## Conventions

**Frontmatter.** Every page starts with YAML:

```yaml
---
title: Human-readable title
tags: [concept]                     # see taxonomy below
---
```

Pages no longer carry `source:` / `commit:` pins — those existed to track per-file
drift, which is no longer our problem. The one exception is [[deep-review]], a
**frozen historical snapshot** that keeps its commit pin (see below).

**No line citations.** Refer to code by **name** — a function, type, or module
(`run_to_branch`, `MComputation`, `machine::unify`) — never by line number.
Line numbers go stale the instant anything above them changes (a refactor, even
adding a doc comment, silently invalidates every citation below it). If a reader
wants the exact code, the name takes them there and the rustdoc is one hop away.
This replaces the old `file:line` anchor discipline, which cost more in churn than
it ever returned.

**Wikilinks.** Link liberally with `[[basename]]` or `[[basename|display text]]`.
Basenames are unique across the wiki, so `[[cbpv]]`, `[[unification]]`,
`[[search-strategies]]` all resolve. A `[[link]]` to a page that doesn't exist yet
is fine — it marks a page worth writing. Do **not** link to a former `components/`
page (`[[step]]`, `[[eval]]`, …); name the symbol in prose and let the rustdoc carry
the detail.

**Voice.** Describe what the code *does*, in present tense, concisely. Match the
existing pages. Don't editorialize; cross-link known problems instead (see below).

## Taxonomy (tags + folders)

| Folder | `tags` | Contents |
|---|---|---|
| `architecture/` | `architecture` | The big picture: [[overview]]. |
| `concepts/` | `concept` | Ideas, not files: [[cbpv]], [[logic-variables]], [[unification]], [[de-bruijn]], [[type-system]], [[nondeterminism]], [[search-strategies]], [[suspensions-and-forcing]]. |
| `reference/` | `reference` | User-facing: [[cli]], [[grammar]], [[examples]]. |
| `review/` | `review` | Audits and findings: [[deep-review]]. Pages cross-link here for "known issues". |

## Workflows

**Document** (new page). Write only when the topic is conceptual, architectural,
user-facing, or an audit — not a per-module restatement. Read the relevant source
first-hand, write the page with frontmatter and wikilinks, and append to [[log]].
(There is no hand-maintained index — Obsidian's file explorer and graph view are
the index.)

**Sync** (code changed). Much lighter than it used to be, because there are no
`file:line` anchors or `source:` pins to chase. Concept pages rarely move with the
code; check them only when a *semantic* change lands (a new search strategy, a
changed evaluation order), and update prose, not line numbers. Append a `sync`
entry to [[log]] naming the commit and pages touched.

**Lint** (health check). Look for: orphan pages with no inbound links; concepts
mentioned but lacking a page; contradictions between pages; stray `file:line`
citations that crept back in (there should be none); links to deleted
`components/` pages; and [[deep-review]] findings that have since been fixed.

## Known-issues convention

Pages describe current behaviour. Where a [[deep-review]] finding still reproduces
against current code, add a short callout linking the finding, e.g.:

> **Known issue.** Backtracking state is copy-on-write `Rc<UnionFind>`, so the first
> write on a shared clone deep-copies the whole store → O(N²) on deep search. See
> [[deep-review]] §P2.

Before adding such a callout, **verify the finding against current code** — the
review is a historical snapshot and most of its findings are already fixed.

## The one pinned page

[[deep-review]] is a **frozen audit**, point-in-time evidence of what the code looked
like when it was written. It keeps its `commit:` pin, and its internal references are
historical record as of that commit — leave them as they are. It is the only page
exempt from the no-line-citation rule. Don't re-sync it; if its findings are stale,
note the fix in the page that describes the current behaviour, not here.
