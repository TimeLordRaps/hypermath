# struct-distinct

> *hypermath | formal-universality | dictionary*

## What it is

`struct-distinct(x, y) :: Prop` asserts that `x` and `y` are not in the same
[`simulation`](simulation.md) (`` `==` ``) class: there is no mutual path
reproduction between them. Semantically closed in L0 Section VI via:

```
struct-distinct(x, y) ≡ not(x == y)
```

The foundational instance: `struct-distinct(apply(ground), ground)` — the
generated form and its generator are structurally distinct.

## What it is not

- Not inequality. Inequality is a predicate on values or propositions in logic.
  `struct-distinct` is a predicate on generative position: `x` and `y` cannot
  mutually reproduce each other's paths.
- Not disjointness. `struct-distinct(x, y)` does not mean `x` and `y` have
  nothing in common. They can be [`similar`](similar.md) (`` `~~` ``) and still
  be `struct-distinct`. Different path structure, shared generator.

## What it clarifies

Grounds `ax-diff`: the fourth axiom, that distinct forms exist, is formally
instantiated by `struct-distinct(apply(ground), ground)`. Without `struct-distinct`,
`ax-diff` would be an assertion with no formal witness.

## Concrete example

```
struct-distinct(apply(ground), ground)
-- FORM. L0 Section IV derive: apply-ground-is-distinct.
-- Establishes that the generative act produces something new.
```

## Visualization

A shadow and the person casting it. They share an origin — the light source
and the person — but they are structurally distinct: one has mass, one does not.
You cannot reproduce the shadow's path using the person, or vice versa. Yet
both `struct-continue` the same generative situation.

## Speculation

Whether `struct-distinct` can be derived from the relation structure rather than
taken as an opaque — whether `not(x == y)` is derivable from the
[`struct-continues`](struct-continues.md) and orbit structure without a separate
opaque predicate — is an open minimality question. If derivable, `struct-distinct`
becomes a theorem rather than a primitive close, which would reduce L0's opaque
count. Composing with [`struct-orbits`](struct-orbits.md): the three structural
predicates may reduce to two or one in a more compact axiom system.
