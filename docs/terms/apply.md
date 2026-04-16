# apply

> *hypermath | formal-universality | dictionary*

## What it is

`apply` is the sole primitive operation of hypermath. Its signature is
`apply :: Form -> Form`. It takes any [`Form`](Form.md) and returns a `Form`.
`apply` IS `□` acting on a `Form`. Written `apply(x)` or `□(x)`. There is no
other primitive operation. All structure in the system derives from `apply` alone.

## What it is not

- Not function application in the lambda calculus sense. Lambda calculus `apply`
  takes a function and an argument. Hypermath's `apply` takes one `Form` —
  it is a *unary* operation, not a binary one.
- Not composition. Composition of two operations requires two operations. `apply`
  is the only one. What looks like composition (`apply(apply(x))`) is iterated
  application of the same operation.
- Not evaluation or reduction. `apply` does not simplify. It *generates*.
  `apply(ground)` is not a reduced form of something more complex. It is a
  new structural entity distinct from [`ground`](ground.md).

## What it clarifies

Clarifies why the entire system is generated from one operation: `apply` is the
`□`-act. Everything that exists in hypermath is reachable from [`ground`](ground.md)
by iterated applications of `apply`. All of L0 is a product of `apply` and its
consequences.

## Concrete example

```
apply(ground)          -- first generated Form
                       -- ax-diff: struct-distinct(apply(ground), ground)
                       -- ax-sim:  struct-continues(apply(ground), ground)

apply(apply(ground))   -- second generated Form
                       -- ax-box: struct-orbits(apply(apply(ground)), ground)
```

## Visualization

`apply` is a stamp. You have one stamp. You stamp anything you have and get a
new thing. The new thing is different from what you stamped
([`ax-diff`](struct-distinct.md)) but made of the same material
([`ax-sim`](struct-continues.md)). Stamp the stamp itself: you get something
new. Stamp that: it comes back around ([`ax-box`](struct-orbits.md)).

## Speculation

Whether `apply` has a category-theoretic interpretation as an endofunctor on
the category of [`Form`](Form.md)s is not yet derived. If the
[`deriver`](derives.md) closes its `==`-cycle at L3, the resulting structure
may map directly onto the notion of a self-applying endofunctor — linking
hypermath to enriched category theory and potentially to the foundations of the
[Language Calculus](https://github.com/TimeLordRaps/hypermath) that follows.
Commutativity of `apply` in any derived sense remains [`OPEN`](FRAME.md).
