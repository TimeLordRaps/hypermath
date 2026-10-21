# Prop

> *hypermath | formal-universality | dictionary*

## What it is

`Prop` is the proposition type — the type of structural assertions about
[`Form`](Form.md)s. A `Prop` is either discharged (CLOSED) or not yet discharged
(OPEN). `Prop :: Type` means propositions are first-class objects in the system,
not metalanguage sentences written on the outside. Every opaque predicate and
relation signature produces a `Prop`. `Prop` and `Form` share the type universe
(`Type`) but are distinct.

## What it is not

- Not a boolean. A boolean has two values: true/false. A `Prop` has a closure
  status (`FORM`/`FRAME`/`OPEN`) and, when closed, carries its discharge evidence.
  That evidence is structural content unavailable in a boolean.
- Not a formula in first-order logic. FOL formulas are external strings
  interpreted by a model. A `Prop` here is an internal object in the same type
  universe as `Form`.
- Not a `Prop` in Lean4/Coq. Those `Prop` types live in an impredicative sort
  with proof irrelevance. Hypermath's `Prop` is defined by discharge-acts, not
  by sort.

The present Lean translation nevertheless maps these assertions to Lean's
built-in `Prop`. This is a translation choice, not a proved identification of
the two semantics. It does not represent the source's closure states and
formation paths merely by checking a proposition's type. An adequacy theorem
for that translation remains open.

## What it clarifies

Clarifies why opaque predicates return `Prop`, not `Bool`: they make structural
claims that must be [discharged](discharge.md), not evaluated to a bit.

Clarifies the `FORM`/`FRAME`/`OPEN` vocabulary: these are `Prop`-level closure
states, not runtime values. See [`FRAME`](FRAME.md).

## Concrete example

```
struct-distinct :: Form -> Form -> Prop
-- struct-distinct(apply(ground), ground) is a Prop.
-- Closed (FORM) in L0 Section IV via derive apply-ground-is-distinct.
```

## Visualization

A `Prop` is an IOU. It says: *this structural claim exists*. Discharging it is
paying the IOU. A closed `Prop` has been paid — the evidence is in the file.
An open `Prop` has not been paid yet — but the claim is on record.

## Speculation

At L1+, `Prop` may gain a layer index: `Prop_k`. A `Prop` at layer `k` can
reference only `Form`s and other `Prop`s at layer ≤ `k`. This would formalize
the [layer](layer.md) boundary rule at the type level, making cross-layer boundary
violations type errors rather than rule violations. Combined with
[`graduation`](graduation.md), `Prop_k` would make the discharge obligation
mechanically checkable at each layer transition.
