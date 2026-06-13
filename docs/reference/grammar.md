---
title: Grammar
tags: [reference, stub]
source: src/parser/parse.rs
updated: 7972077
---

# Grammar *(stub — expand on demand)*

The surface syntax accepted by the [[parser]]. This page is a placeholder; the authoritative
grammar is the chumsky combinator definitions in `parse.rs` (`:100-382`). A full reference
would lay out the BNF for declarations, statements, expressions, types, and case patterns,
with the operator precedence table.

## Sketch

```
program     ::= declaration*
declaration ::= name "::" type "."            -- function signature
              | name arg* "=" stmt "."        -- function definition
              | stmt "."                       -- bare (top-level query)

stmt        ::= "if" stmt "then" stmt "else" stmt
              | "let" var "=" stmt "in" stmt
              | "exists" var "::" type "." stmt
              | expr "=:=" expr "." stmt       -- unification constraint
              | "case" expr "of" cases
              | "fail"
              | expr ("<>" expr)*              -- choice

expr        ::= "S" expr | "\" arg "." stmt    -- successor, lambda
              | expr ":" expr                  -- cons (right-assoc)
              | expr expr                       -- application (left-assoc)
              | atom
atom        ::= Z | nat | "[]" | "[" expr,* "]" | "(" expr "," expr ")"
              | "true" | "false" | ident | "(" stmt ")"

type        ::= type "->" type | type "*" type | "[" type "]" | ident
```

> The sketch elides exact precedence. Known parser issues: `*`/`->` share precedence
> ([[deep-review]] §B6); numeric and tuple `case` patterns panic (§B12, §B10). The AST node
> types these productions build are listed in [[parser]].

Related: [[parser]], [[type-system]], [[pipeline]].
