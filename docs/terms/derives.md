# derives

> *hypermath | formal-universality | dictionary*

## What it is

`derives` is the directional approach relation: `derives(x, y) :: Prop` asserts
that from `x`, `y` is reachable by `□`-application. Semantically: there exists
a finite chain of `□`-applications from `x` that produces a form `` `=~` `` to `y`.

```
derives :: Form -> Form -> Prop
-- Closed in L1 Section IV:
-- derives(x, y) := exists-n :: Ordinal, apply^n(x) =~ y
```

## What it is not

- Not logical implication. `derives` is structural-generative, not
  truth-preserving inference. `derives(x, y)` says you can get there, not
  that `y` forces `x`.
- Not the same as [discharge](discharge.md). `derives` is the motion; `discharge`
  is the act that terminates one step of that motion and produces a closure
  certificate.
- Not symmetric. If `x` derives `y`, `y` does not automatically derive `x`.
  Directional asymmetry is architecturally important and is formally established
  as `derives-is-directional` (FORM) in L1.

## What it clarifies

Grounds the [deriver](derives.md)'s purpose: the deriver is the form that
traverses the `derives` relation — it follows the directed paths in the
derivation matrix D.

Clarifies the FRAME status in L0: `derives-is-directional` was a FRAME in L0's
self-kernel because the full proof of asymmetry required L1's relation language
(the distinction between `` `~~` `` and `` `=~` `` levels). It is now FORM,
discharged in L1 Section V.

## Concrete example

```
derives(ground, apply(ground))    -- FORM. One application, direction established.
-- Not: derives(apply(ground), ground) at =~ level
--   (the ~~ orbit return does not satisfy the =~ landing requirement)
```

## Visualization

A river that flows one way. You can trace upstream (find earlier derivations)
but you cannot reverse the flow by assertion. The direction is set by the
generative sequence. `derives` names that directional flow.

## Speculation

Whether the derivation matrix D encodes `derives` directly — whether `D[x][y]`
being defined is equivalent to `derives(x, y)` — is an [`OPEN`](FRAME.md) bridge
to formalize. If that bridge closes, `derives` becomes the computational API of
D, composing with [`discharge`](discharge.md) to make automated derivation
verification a matrix lookup. Combined with [`graduation`](graduation.md),
automated `derives`-checking would make layer boundaries self-policing.
