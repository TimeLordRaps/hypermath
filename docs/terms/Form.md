# Form

> *hypermath | formal-universality | dictionary*

## What it is

`Form` is the ground type of hypermath — the type to which every entity in the
system belongs. A `Form` is any structural object that can be produced by the
sole primitive operation: [`apply`](apply.md). `Form :: Type` means `Form` is a
first-class object in the type universe, not a metalanguage category imposed
from outside.

## What it is not

- Not a set. `Form` does not presuppose membership axioms.
- Not a class in the ZFC/NBG sense. No containment hierarchy.
- Not a shape or geometric figure. Structure here means: *generated-by-apply*.
- Not a data type in the programming language sense. `Form` has no constructors
  beyond `apply`. It carries no payload. It is not parameterized.

## What it clarifies

Clarifies why the system has no imports: `Form` is the floor. Everything else
is a `Form` or a [`Prop`](Prop.md) or an operation on `Form`s. No prior universe
is required.

Clarifies why `apply` has domain `Form` and codomain `Form`: the only objects
that exist are `Form`s, so the only things you can apply to are `Form`s, and
the result is always a `Form`. The system is closed at the type level.

## Concrete example

```
ground :: Form          -- primitive declaration, L0 Section I
apply(ground) :: Form   -- first generated Form; ax-sim keeps it in class
```

## Visualization

Every object you will ever work with in this system has one label on it: `Form`.
Not `Int`, not `String`, not `Bool`. One label. The system is monotyped at the
ground. The richness of what `Form`s can *be* is generated entirely by
[`apply`](apply.md) acting on them. Think of `Form` as the material: clay.
`apply` is the only tool. Every shape is clay.

## Speculation

At higher layers, `Form` may need to be stratified into `Form-at-level-k` to
accommodate the [orbital](orbital.md) structure. Whether this requires a universe
hierarchy or whether a single `Form` type suffices for all layers is not yet
determined. The [deriver](derives.md) may require `Form` to carry a [layer](layer.md) tag —
at which point `Form` would compose with [`graduation`](graduation.md) to produce
a typed layer boundary at the type level rather than as a rule.
