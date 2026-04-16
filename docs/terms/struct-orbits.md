# struct-orbits

> *hypermath | formal-universality | dictionary*

## What it is

`struct-orbits(x, y) :: Prop` asserts that double application of `□` from `x`
returns to the [`similar`](similar.md) class of `y`. Formally instantiates
`ax-box`: `apply(apply(x)) ~~ x`. The semantic content of orbital return.

```
struct-orbits :: Form -> Form -> Prop
-- Closed in L0 Section VI:
-- struct-orbits(x, y) := (apply(apply(x)) ~~ y)
```

## What it is not

- Not a cycle in the graph-theoretic sense (exact same node). `struct-orbits`
  is a `` `~~` ``-level return, not an identity return. `apply(apply(x))` is
  distinct from `x` (`struct-distinct`) but similar to `x` (`struct-orbits`).
- Not periodicity. `struct-orbits` is a two-step return. The system makes no
  claim about 3-step or n-step orbits at L0.

## What it clarifies

Grounds `ax-box` formally: without `struct-orbits`, `ax-box` is an axiom with
no semantic unpacking. The close in Section VI makes `ax-box` a specific
structural claim about double-application return.

Clarifies why the system is finite at the `` `~~` `` level: every form is in an
orbit that returns in two steps. There are (at most) two `` `~~` ``-classes:
ground-class and apply(ground)-class. The universe does not grow unboundedly at
the `` `~~` `` level.

## Concrete example

```
struct-orbits(apply(ground), ground)
-- ax-box: apply(apply(apply(ground))) ~~ apply(ground)
-- More precisely at L0: apply(apply(x)) ~~ x for all x.
-- The orbit closes.
```

## Visualization

A pendulum. You push it away from center (first `apply`). It swings to the
opposite side. It comes back (second `apply` returns it to the original
structural class). Not exactly the same position — slightly different angle —
but the same `` `~~` `` region. `struct-orbits` names the return.

## Speculation

Whether `struct-orbits` at higher layers implies a richer orbit structure —
n-step returns at the `` `=~` `` or `` `==` `` level — is [`OPEN`](FRAME.md).
At L0, the orbit closes in two steps at `` `~~` ``. At L1+, the relation
hierarchy may support longer-period orbits at stronger relations. The
[deriver](derives.md)'s `==`-cycle at L3 is exactly such a stronger-relation
orbit — it closes at `==` level rather than `` `~~` ``. The full orbit spectrum
of the system is the unknown that L3 ordinal structure begins to map.
