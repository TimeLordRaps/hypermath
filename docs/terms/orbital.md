# orbital

> *hypermath | formal-universality | dictionary*

## What it is

The `orbital` of a form `x` is the minimum [layer](layer.md) `k` at which `x`'s
meaning can be fully stated. `orbital(x) = k` iff `x` requires the
operations/relations of L(k) to be defined before its semantics can be closed.

- `orbital(x) = L0`: `x`'s meaning is statable with only unary operations
- `orbital(x) = L1`: `x`'s meaning requires binary relations
- `orbital(x) = L2+`: requires binary operations or higher

## What it is not

- Not where `x` is first mentioned. A form can be *referenced* at any layer
  as a `FRAME`. Its orbital is where it is *closed*.
- Not where `x` is most useful. Usefulness is not the criterion. Closure is.
- Not fixed per-form for all time. As the system grows, a form's orbital could
  in principle be lowered if new derivations reduce its closure prerequisites.

## What it clarifies

Clarifies the discipline of not premature closure: the orbital determines the
earliest layer at which a `FRAME` can transition to `FORM`. Any earlier claim
of closure is a layer violation.

Clarifies [layer](layer.md) integrity: a form at orbital L2 cannot be closed in
L0. Its `FRAME` must survive until L2.

## Concrete example

The `deriver` has orbital L1 (declared at L1 — requires binary relations to
state its meaning). But its `` `==` ``-cycle has orbital L3 (requires ordinal
structure from L3 to close the cycle). The form exists at L1; full closure
requires L3. This is why `deriver-cycle-is-closed` is `FRAME/L3` in L1's
self-kernel.

## Visualization

The depth at which a submarine can first surface. A submarine at depth 500m
cannot surface at 400m — it would be crushed. Its "orbital" is 0m (the surface).
You know it needs to reach the surface; until then, it remains submerged and
designated `FRAME`. The orbital is the target depth.

## Speculation

Whether a formal `orbital` predicate — `orbital :: Form -> Layer -> Prop` —
should be added to the system as a derived predicate at L1 is [`OPEN`](FRAME.md).
If formalized, it would link [`layer`](layer.md), [`FRAME`](FRAME.md), and
[`graduation`](graduation.md) into a unified layer-integrity check: the graduation
criterion at L(k) would include verifying that all forms with orbital ≤ k have
been closed, and all forms with orbital > k are properly marked `FRAME`.
