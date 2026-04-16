# form-closure

> *hypermath | formal-universality | dictionary*

## What it is

`form-closure` is the event by which the syntax-substance-semantics triangle
completes its cycle for a given form: [`syntax`](syntax.md) is assigned,
[`substance`](substance.md) is carried, [`semantics`](semantics.md) is embedded
in the relation network, and the semantics-to-syntax arc closes back.
`form-closure :: Form -> Prop`.

```
-- Closed in L1 Section IV:
-- form-closure(x) := syntax(x) and substance(x) and semantics(x)
--   and simulation-class(x) derives orbit-depth(x)
```

## What it is not

- Not the same as `CLOSED` (the status label). `CLOSED` labels a derivation
  block. `form-closure` is a property of an individual form within a derivation
  block.
- Not completion in a temporal sense. `form-closure` is structural. It is a
  property of the form's position in the derivation graph.

## What it clarifies

Clarifies why the triangle axioms are 3-cycle rather than linear: `form-closure`
requires the cycle. A linear chain (`syntax → substance → semantics`) with no
closing arc would make semantics a dead end. The arc from semantics back to
syntax (`ax-sem-nec`) is what enables `form-closure`.

Clarifies the difference between a [`FRAME`](FRAME.md) form and a form with
`form-closure`: a `FRAME` form has syntax and substance but its arc back to
syntax from its relational embedding is deferred.

## Concrete example

[`ground`](ground.md) achieves `form-closure`:
- syntax: the primitive marker
- substance: the fixed-point property (`apply(ground) struct-orbits ground`)
- semantics: position as the base of all `` `~~` `` relations
- The triangle cycle closes. `ground` is `form-closed`.

## Visualization

A word that is also its own definition: *"self" means "the one referring."*
The syntax (the word), the substance (the referential act), and the semantics
(the relation "referring to itself") close in a loop. That is `form-closure`.

## Speculation

Whether `form-closure` is the correct proof obligation for the deriver's
self-closure — whether the [deriver](derives.md) achieves terminal state exactly
when it achieves `form-closure` — is the core architectural question of the
telos. If `form-closure(deriver)` is equivalent to `deriver-cycle-is-closed`
(L3), then the triangle is the [simulation](simulation.md) certificate, and
[`graduation`](graduation.md) at L3 collapses into `form-closure`. This would
make `form-closure` the single proof obligation for self-derivation.
