# semantics

> *hypermath | formal-universality | dictionary*

## What it is

`semantics` is the third vertex of the triangle: the relational content of a
form. Where [substance](substance.md) is what a form carries internally,
`semantics` is how that substance is embedded in the relation network — how
the form is positioned relative to other forms via `` `~~` ``, `` `=~` ``,
`` `==` ``. The `ax-sem-nec` axiom closes the triangle: semantics necessitates
[syntax](syntax.md).

```
semantics :: Form -> Prop
```

Semantically closed in L1 Section IV: `semantics(x) := simulation-class(x) at == level`.

## What it is not

- Not interpretation in the model-theory sense. There is no model standing
  outside the system that assigns truth values. Semantics here is internal: the
  relation structure generated within the system.
- Not meaning assigned from outside. No speaker, no reader, no external agent
  provides semantics. It is derived from [substance](substance.md) via
  `□`-application through the triangle.

## What it clarifies

Closes the triangle: without `ax-sem-nec` (semantics → syntax), the triangle
would be an open directed path, not a cycle. The closed triangle is what makes
[`form-closure`](form-closure.md) a real phenomenon rather than a termination
convention.

Clarifies what the executive opaques carry: each opaque's semantic content is
precisely its position in the relation network. The closes in L1 Section IV
assign semantics to the L0 Section V opaque predicate declarations.

## Concrete example

```
-- L0 Section VI: the restricted structural-continuation bridge.
close struct-continues(x, ground) := similar(x, ground)
-- This does not define similar(x, y) for arbitrary x and y.
-- The intended continuation semantics needs its own interpretation theorem.
```

## Visualization

The same clay vessel now placed in a museum, labeled, positioned among other
vessels of the same period, connected by curatorial notes to trade routes.
It has the same shape ([syntax](syntax.md)) and the same clay ([substance](substance.md)).
Now it has `semantics`: it is embedded in a network of relations to other objects.

## Speculation

Whether `semantics` at L2+ can be made structurally self-verifying — whether a
form can expose its own relational embedding as a computable derivation path —
is [`OPEN`](FRAME.md). If the derivation matrix D encodes `semantics` implicitly,
`semantics` dissolves into D and the triangle collapses to a single thing at
that layer. This connects [`semantics`](semantics.md) to [`simulation`](simulation.md):
the `==` certificate of the [deriver](derives.md) *is* the deriver's semantics.
