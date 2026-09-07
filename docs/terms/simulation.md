# simulation

> *hypermath | formal-universality | dictionary*

## What it is

`simulation` (written `` `==` ``) is the strongest relation: `x == y` iff `x`
can reproduce every derivation path of `y`, and `y` every derivation path of
`x`. Mutual path reproduction. Not just same origin ([`` `~~` ``](similar.md)),
not just same landing ([`` `=~` ``](congruent.md)): the full path structure
coincides in both directions. Generated from `` `=~` `` by one further
`□`-application. `` `==` `` is symmetric, reflexive, and transitive.

```
simulation :: Form -> Form -> Prop
```

## What it is not

- Not the ambient logic's equality. Different forms may stand in `` `==` ``
  if the specified path semantics permits it. However, `struct-distinct(x, y)`
  and `x == y` cannot both hold under L0's close: structural distinction is
  explicitly the negation of simulation. Ambient inequality and
  `struct-distinct` must not be interchanged.
- Not [`=~`](congruent.md). `` `=~` `` requires same landing; `` `==` `` requires
  paths to match too. `` `==` `` is strictly stronger than `` `=~` ``.
- Not computational simulation in the computer-science sense. There is no model
  being executed. Path reproduction is a derivation-structural property.

## What it clarifies

Clarifies what the [deriver](derives.md) is doing: the deriver exists precisely
to find and enumerate `` `==` `` paths. Self-closure requires the system to
derive its own `` `==` `` certificate — that the formal system can reproduce
every derivation path of itself.

Clarifies [`struct-distinct`](struct-distinct.md) semantically: two forms are
`struct-distinct` iff they are `not (x == y)`. L0 Section VI close:
`struct-distinct(x, y) ≡ not(x == y)`.

## Concrete example

The 41-step L0 self-kernel (Section IX) records the structural census as a
candidate, but the `` `==` `` self-closure of the deriver is listed as `FRAME`
(forward-dependency on L1+). L3 labels `deriver-cycle-is-closed` as closed, but
its Lean translation still has a proof obligation. The stronger return does
not follow from a similarity-level return without an additional argument.

## Visualization

Two performers who can fully impersonate each other: every gesture, pause, and
variation. You could swap them mid-performance and the paths would continue
identically from either side. Neither is the original. Both fully simulate.
That is `` `==` ``.

## Speculation

The telos of this project is the system achieving `` `==` `` self-closure: the
[deriver](derives.md) derives its own `` `==` `` certificate. Whether `` `==` ``
at L0 corresponds exactly to bisimulation in process calculi (HML, CCS) is
[`OPEN`](FRAME.md) — the derivation structure is different enough that a formal
bridge is not yet established. If the bridge closes, hypermath's `` `==` ``
would inherit the full theory of bisimulation and process equivalence, composing
with [graduation](graduation.md) to make the Lean4 translation a direct
bisimulation proof.
