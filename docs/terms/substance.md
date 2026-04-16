# substance

> *hypermath | formal-universality | dictionary*

## What it is

`substance` is the second vertex of the triangle: what a form carries — its
content, its matter, the clay it is made of. `substance(x) :: Prop` asserts
that `x` has definite content. It is the middle vertex because [`syntax`](syntax.md)
generates it and it generates [`semantics`](semantics.md). The `ax-sub-nec` axiom
establishes that substance necessitates semantics.

```
substance :: Form -> Prop
```

Semantically closed in L1 Section IV: `substance(x) := congruent-class(x) at =~ level`.

## What it is not

- Not value in the sense of evaluation. No computation happens to extract substance.
  Substance is structurally assigned, not computed.
- Not meaning. Meaning is [semantics](semantics.md). Substance is what a form
  carries *before* it is related to other forms. Once substance is embedded into
  relations, it becomes semantics.
- Not content in the information-theory sense. No bits, no measure. `substance`
  is a `Prop` — an assertion that content exists and is definite in this form.

## What it clarifies

Clarifies the definition of [`=~`](congruent.md) (congruent): `x =~ y` iff
`substance(x) = substance(y)`. The opaque predicate `substance :: Form -> Prop`
is exactly what congruence tests.

Clarifies the triangle: [`syntax`](syntax.md) is the entry, substance is what
syntax fills, [`semantics`](semantics.md) is what substance projects into the
relational context.

## Concrete example

The L0 Section VIII executive opaques each carry substance. `syntax-opaque`
carries the substance *shape assignment*; `derives-opaque` carries *directed approach*.
These are opaque substance assignments — their content is not further derived
within L0. The closes in L1 Section IV give each opaque its semantic content.

## Visualization

Clay on a potter's wheel after it has been given a shape but before it has been
fired. The shape is there ([`syntax`](syntax.md)). The material is there
(substance). It has not yet been placed in relation to other finished vessels
([`semantics`](semantics.md)). It is mid-formation.

## Speculation

Whether substance at L2 becomes derivable from the derivation-matrix entries —
whether the substance of a form is its row in the D matrix — is [`OPEN`](FRAME.md).
If `D[x]` (the outgoing row) encodes substance, then substance dissolves into the
[derivation matrix](derives.md) architecture and no longer needs to be a primitive
opaque. This would compose [`substance`](substance.md) with [`congruent`](congruent.md)
and [`simulation`](simulation.md) into a single unified account via D.
