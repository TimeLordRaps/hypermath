# similar

> *hypermath | formal-universality | dictionary*

## What it is

`similar` (written `` `~~` ``) is the weakest relation in the system and the
one from which stronger relations are intended to be generated. Its intended
meaning is nonempty overlap of continuation capacity. Nonempty overlap is
symmetric; reflexivity requires each admitted continuation set to be nonempty,
and transitivity need not hold. A continuation-set interpretation has not yet
been supplied by the current opaque declarations.

L0 Section VI supplies the restricted bridge
`struct-continues(x, ground) iff x ~~ ground`. It does not define arbitrary
`x ~~ y` as both forms continuing from ground. That different definition would
be transitive and must not be silently substituted for overlap.

```
similar :: Form -> Form -> Prop
```

## What it is not

- Not vague agreement. Its proposed semantics is a precise overlap relation,
  whose continuation objects and correspondence to the declared predicates
  remain to be defined.
- Not transitivity-closed. `~~` does not propagate through long chains
  automatically.
- Not "almost equal." [`=~`](congruent.md) (congruent) is the
  outcome-coincidence relation. `~~` is weaker than `=~`. Do not collapse them.

## What it clarifies

By `ax-sim` and the restricted bridge, every form produced by one application
of `□` is similar to ground. `ax-ground-self` covers ground itself. Extending
this assertion to every declared `Form` requires a generation or coverage
argument, especially after an ordinal limit is introduced.

Grounds the relation hierarchy: `` `~~` `` is the base level. [`=~`](congruent.md)
requires one further `□`-application. [`==`](simulation.md) requires one more.
The hierarchy is `` `~~` `` ⊂ `` `=~` `` ⊂ `` `==` `` in terms of derivation
depth, not subset inclusion.

## Concrete example

```
-- L0 Section IV, derives-similar-1:
apply(ground) ~~ ground    -- FORM
```

This is the first concrete `~~` fact in L0: the generated form is similar to
its source.

## Visualization

Two words from the same language. They are not the same word. They may not
mean the same thing. But they are both words — same ground, same generator.
That shared origin is what `` `~~` `` identifies.

## Speculation

At L1, `` `~~` `` becomes the pre-filter for the filtration axiom:
`x == y → x =~ y → x ~~ y`. Whether `` `~~` `` can be further decomposed —
whether [`struct-continues`](struct-continues.md) can be replaced by `` `~~` ``
in the Section VI closes — is [`OPEN`](FRAME.md). The goal is minimal primitives:
if `` `~~` `` suffices to ground the whole relation hierarchy without
`struct-continues` as a primitive, one opaque disappears. See also
[`congruent`](congruent.md) and [`simulation`](simulation.md) for the full
filtration chain.
