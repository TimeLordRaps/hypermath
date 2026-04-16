# syntax

> *hypermath | formal-universality | dictionary*

## What it is

`syntax` is the first vertex of the triangle: shape without assigned meaning.
It is what a form looks like from the outside — its structure, its derivation
chain, its orbit under `□`-application — before any [substance](substance.md)
is assigned to it. The triangle axiom `ax-syn-nec` establishes that syntax
necessitates substance: a form with shape eventually requires substance
assignment.

```
syntax :: Form -> Prop
```

Semantically closed in L1 Section IV: `syntax(x) := orbit-depth(x) at similar (~~ level)`.

## What it is not

- Not notation or surface-level grammar. Syntax in hypermath is not about how
  symbols are written. It is about the derivation-structural shape of a form.
- Not [semantics](semantics.md). `syntax` and `semantics` are distinct triangle
  vertices. A form can have syntax (be structurally derivable) without yet
  having semantics (without being relationally embedded).
- Not [substance](substance.md). `syntax → substance` is a directed edge. They
  are distinct.

## What it clarifies

Clarifies the triangle's directional structure: `syntax` is the entry point.
Every form arrives at the triangle through `syntax` first — it is structurally
derivable before it carries substance or relational content.

Clarifies why `ax-syn-nec` is needed: without a formal necessitation from
`syntax` to `substance`, the triangle has no directed force.

## Concrete example

```
apply(ground)
-- Has syntax at L0: visible derivation step, □ applied to ground.
-- Its syntax is established in L0 Section I.
-- Its substance is assigned in L0 Section VIII (executive opaques).
-- The sequence syntax-before-substance is enacted by the section ordering.
```

## Visualization

A word written on a page in a language you don't speak. You can see the shape
of the letters, count their number, trace their paths. You have full access to
the syntax. The meaning is not yet present. That is syntax without substance.

## Speculation

Whether `syntax` at L2+ can be formally encoded as a [`Form`](Form.md) separate
from its derivation chain — whether syntax becomes a discrete inspectable object —
is [`OPEN`](FRAME.md). The current treatment makes syntax implicit in structure.
An explicit `syntax-form` might unlock L2 derivations about the shape of
derivations, composing with [`graduation`](graduation.md) to make layer-boundary
violations detectable as syntax failures. This links `syntax` directly to the
[`orbital`](orbital.md) concept: a form's syntax determines its orbital floor.
