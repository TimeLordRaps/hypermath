# ground

> *hypermath | formal-universality | dictionary*

## What it is

`ground` is the primitive [`Form`](Form.md) declared as the base of the system —
the fixed point of `□`-application. Written also as `□`. Ground plays three
structural roles simultaneously:

- **(a) generative base** — all `Form`s derive via [`apply`](apply.md) from `ground`
- **(b) the closure act** — the operation that closes a derivation *is* ground acting on the derivation
- **(c) the fixed point** — `apply(apply(x))` returns to ground's structural class for every `x` (ax-box)

These are not three separate things. They are three angles on one primitive.

## What it is not

- Not zero. Zero is an arithmetic identity. Ground has no arithmetic.
- Not the empty set. The empty set has elements (zero of them). Ground has no membership relation.
- Not a base case in the induction sense. Induction presupposes a successor
  operation and a natural number structure. Ground precedes those.
- Not a starting state in a state machine. State machines presuppose transitions
  defined independently of states. Ground itself *is* the transition act.

## What it clarifies

Clarifies why there is no "second primitive": `ground` and `apply` are not two
separate things. `apply` IS `ground` acting on a `Form`. There is one primitive —
`ground` — and one thing it does — act on `Form`s.

Clarifies ax-ground-self: `ground` [`struct-continues`](struct-continues.md) from
itself because `ground` IS the generative base. It cannot fail to be in its own class.

## Concrete example

```
ground :: Form                              -- L0 Section I, primitive declaration
struct-continues(ground, ground)            -- ax-ground-self. Ground is in its own class.
apply(ground) :: Form                       -- first generated Form (distinct by ax-diff)
```

## Visualization

Imagine a spring. The water comes from the spring. The spring is also water.
When you trace any stream back far enough, you reach the spring. The spring does
not come from anywhere else. That is `ground`. `□` is both the source and the act
of sourcing.

## Speculation

Whether `ground` is the *unique* fixed point of [`apply`](apply.md), or whether
other fixed points exist, is not established at L0. `ax-box` establishes
orbit-return for all `Form`s but does not assert `ground` is the only
fixed-orbit element. Establishing uniqueness may be the first theorem for the
[deriver](derives.md) at L1, using the [`similar`](similar.md) and
[`simulation`](simulation.md) relation structure to show no other `Form` can
sit at `ground`'s relational position.
