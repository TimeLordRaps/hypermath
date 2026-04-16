# layer

> *hypermath | formal-universality | dictionary*

## What it is

A `layer` is a structural partition of the hypermath derivation space, defined
by the type of operations it introduces:

| Layer | Operations | Status |
|-------|-----------|--------|
| L0 | Unary (`□`, `Form`, `Prop`, `ground`, `apply`) | FORM — 41 steps |
| L1 | Binary relations (`` `~~` ``, `` `=~` ``, `` `==` ``) | FORM — 25 steps |
| L2 | Binary operations (`+`, `additionally`, `compose`) | FORM — 31 steps |
| L3 | Ordinal structure, terminal closure | FORM (terminal) — 18 steps |

Each layer is licensed by the [graduation](graduation.md) of the layer below.
No layer references content from a higher layer without marking that reference
as [`FRAME`](FRAME.md).

## What it is not

- Not a processing stage or runtime concept. `layer` is a derivation-structural
  property, not a computational phase.
- Not hierarchical in the sense of "higher is better." Lower layers are
  foundational. Their stability is what makes higher layers possible. L0 is
  not less important than L3; it is more foundational.

## What it clarifies

Clarifies why modifying L0 affects all higher layers: derivations at L1-L3 cite
L0 content. Any L0 change that alters the structural claims it makes invalidates
those citations.

Clarifies the co-necessity of L0 ↔ L1: the ax-box orbit operates at the layer
level too. L0 (unary) and L1 (binary) form a co-necessary pair — neither is
complete without the other. They are the base from which L2+ composes.

## Concrete example

`derives-is-directional` was a `FRAME/L1` item in L0's self-kernel: its full
proof required the binary-relation language introduced at L1. It was discharged
in L1 Section V (FORM). This is a concrete layer-boundary crossing: the claim
was made at L0, the evidence arrived at L1.

## Visualization

Geological strata. The deepest layer (L0) was deposited first. Every higher
layer is built on what is already solid below. You cannot extract a lower layer
without collapsing everything above it. The strata are not arbitrary divisions —
they reflect the actual generative sequence.

## Speculation

Whether L4+ is needed — whether the current four-layer structure terminates
genuinely at L3 or whether higher layers naturally follow from the self-derivation
closure — is [`OPEN`](FRAME.md). The [deriver](derives.md)'s self-closure at L3
was designed to be terminal. But the orbit-reflexion quotient at L2 suggests a
pattern: each layer adds a compositional capacity. After L3's ordinal structure,
a potential L4 might add higher-order composition or a type-indexed layer
structure, linking to the Language Calculus project downstream.
