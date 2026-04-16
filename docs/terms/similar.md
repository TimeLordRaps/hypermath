# similar

> *hypermath | formal-universality | dictionary*

## What it is

`similar` (written `` `~~` ``) is the weakest relation in the system and the
one from which all stronger relations are generated. `x ~~ y` iff both `x` and
`y` `struct-continue` from [`ground`](ground.md). `~~` is symmetric, reflexive,
and non-transitive in general. The relation that [`ground`](ground.md) generates
first, before [`=~`](congruent.md) or [`==`](simulation.md). Declared in L0
Section V; closed via [`struct-continues`](struct-continues.md) in Section VI.

```
similar :: Form -> Form -> Prop
```

## What it is not

- Not vague agreement or informally "kind of alike." `` `~~` `` is a formal
  relation with a precise semantics: *shared generator*. Two forms are `~~` iff
  they are both products of applying `□` from the same ground.
- Not transitivity-closed. `~~` does not propagate through long chains
  automatically.
- Not "almost equal." [`=~`](congruent.md) (congruent) is the
  outcome-coincidence relation. `~~` is weaker than `=~`. Do not collapse them.

## What it clarifies

Clarifies why every `Form` is similar to `ground`: by `ax-sim` and
`ax-ground-self`, every form produced by `□` struct-continues from ground,
which is what `~~` names.

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
