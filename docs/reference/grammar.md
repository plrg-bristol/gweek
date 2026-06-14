---
title: Grammar
tags: [reference, stub]
source: src/parser/parse.rs
commit: d83302b
---

# Grammar *(stub — expand on demand)*

The surface syntax accepted by the [[parser]]. This page is a placeholder; the authoritative
grammar is the chumsky combinator definitions in `parse.rs` (`:105-387`). A full reference
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

type        ::= product ("->" type)?            -- arrow, right-assoc, loosest
product     ::= atom ("*" atom)*                -- product, binds tighter than arrow
atom        ::= "[" type "]" | ident | "(" type ")"
```

> The sketch elides some precedence detail; the type layering (`*` tighter than `->`) is now
> correct (`A * B -> C` parses as `(A*B) -> C` — was [[deep-review]] §B6). Numeric and tuple
> `case` patterns are now clean parse **errors**, not panics (§B12, §B10). The AST node types
> these productions build are listed in [[parser]].

Related: [[parser]], [[type-system]], [[pipeline]].
