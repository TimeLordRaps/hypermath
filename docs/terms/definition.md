# definition

> *hypermath | formal-universality | dictionary*

## What it is

`definition` is the anchoring act that makes a form derivable by name. To define
a form is to assign it a name-path within the derivation structure such that
subsequent [`derives`](derives.md)-calls can reference that name instead of the
full derivation sequence.

```
definition :: Form -> Form -> Prop
-- First Form: the name anchor. Second Form: the form being named.
-- Closed in L1 Section IV:
-- definition(n, x) := derives(n, x).status == FORM
```

## What it is not

- Not meaning assignment. A `definition` does not grant [semantics](semantics.md) —
  that is the triangle's job. `definition` grants *navigability*: you can refer
  to this form by name without restating its full derivation.
- Not an axiom. An axiom establishes what is true without derivation. A
  `definition` establishes what a name refers to within an already-established
  derivation.
- Not synthesis. You cannot define into existence a form that cannot be derived.
  `definition` names what is reachable; it does not extend reachability.

## What it clarifies

Clarifies why the dictionary itself is a formal act within the system: each
dictionary entry is an instance of `definition` — it names and anchors a form
that was already structurally derivable.

Clarifies the role of [`derives`](derives.md): `definition` makes a form reachable
by name-path in the derivation matrix D. `D[name][y]` is valid only if `name`
has been defined.

## Concrete example

```
primitive ground : Form    -- L0 Section I
-- This IS a definition: the name "ground" is anchored to the primitive Form □.
-- Without this, subsequent uses of "ground" in axioms would have no referent.
```

## Visualization

A street address. The building exists independently of the address. The address
does not create the building — it makes the building *findable by name* from
anywhere in the city. `definition` is assigning an address to a form that already
exists in the derivation structure.

## Speculation

Whether `definition` can itself be auto-generated from the derivation matrix —
whether the [deriver](derives.md) can discover a canonical minimal name-path for
each form and emit definitions without human authoring — is [`OPEN`](FRAME.md).
Auto-definition would make this dictionary a derivable artifact of the matrix D,
not a manual one. Composing `definition` with [`discharge`](discharge.md): a
definition is complete when it is dischargeable — when `derives(name, x)` can be
verified by D-lookup. This links `definition` to the goal of a fully
self-documenting formal system.
