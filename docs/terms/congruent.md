# congruent

> *hypermath | formal-universality | dictionary*

## What it is

`congruent` (written `` `=~` ``) is the middle relation: `x =~ y` iff `x` and `y`
produce the same [substance](substance.md) regardless of path. Where
[`` `~~` ``](similar.md) requires shared origin, `` `=~` `` requires that the
end-state substance coincides. Path is discarded. Only the landing matters.
Generated from `` `~~` `` by one further `□`-application. `` `=~` `` is
symmetric, reflexive, and transitive.

```
congruent :: Form -> Form -> Prop
```

## What it is not

- Not [`simulation`](simulation.md) (`` `==` ``). `` `=~` `` does not require paths
  to match, only outcomes. Two forms may take entirely different derivation routes
  and arrive at the same substance — that is `` `=~` ``. If their paths also
  mutually reproduce, that is `` `==` ``.
- Not `` `~~` `` ([similar](similar.md)). `` `=~` `` is strictly stronger:
  `x =~ y` implies `x ~~ y`, but not the reverse.
- Not value equality. `` `=~` `` is about the substance landing, not some numeric
  measure. *Same landing* is structural, not quantitative.

## What it clarifies

Clarifies the definition of [substance](substance.md): `substance :: Form -> Prop`
tracks what a form carries. Two forms are `` `=~` `` iff
`substance(x) = substance(y)`.

Clarifies why the triangle needs a distinct middle vertex: without [substance](substance.md)
as a concept distinct from [semantics](semantics.md), `` `=~` `` and `` `==` ``
would collapse.

## Concrete example

The filtration theorem at L1 establishes `x == y → x =~ y`. Any form pair that
satisfies `` `==` `` is a concrete `` `=~` `` example by implication. The
asymmetry is: `` `=~` `` is achievable without `` `==` `` — two forms can have
the same substance while taking structurally different paths.

## Visualization

Two people take completely different routes to the same address. They both arrive
at the same door. The paths diverged — different roads, different timing. But
the landing is the same. That is `` `=~` ``.

## Speculation

Whether `` `=~` `` can be expressed purely in terms of [substance](substance.md)
without the [`struct-continues`](struct-continues.md) machinery is [`OPEN`](FRAME.md).
If [substance](substance.md) is closed well enough at L1, `` `=~` `` may become
a theorem derived from substance-equality rather than a primitive relation
declaration. This would compress the three-relation hierarchy — `` `~~` ``,
`` `=~` ``, `` `==` `` — into two primitive relations plus a derived one, which
links to the [layer](layer.md) minimization goals of the [deriver](derives.md).
