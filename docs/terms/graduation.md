# graduation

> *hypermath | formal-universality | dictionary*

## What it is

`graduation` is the formal criterion that must be discharged before the next
layer is licensed to proceed. Each layer file contains a graduation block that:

1. Lists all necessity constraints (NCs) — conditions that must be FORM before
   the next layer may proceed
2. Lists all dispensability constraints (DCs) — conditions whose absence is
   acceptable at this layer
3. Provides a formal derivation that all NCs are satisfied
4. Emits a `graduation` claim that, when closed, licenses L(k+1)

## What it is not

- Not optional. The graduation is not advisory. A higher layer that builds on
  unmet NCs violates the foundational contract of the system.
- Not the same as completing all work. Graduation requires all NCs to be FORM.
  Additional open work (`FRAME` items with known higher-layer dependencies) does
  not block graduation — that work belongs to the higher layers.

## What it clarifies

Clarifies why layer files contain self-contained verification machinery: the
graduation is not checked by an external tool. It is derived from within the
file itself. The file IS its own graduation checker.

Clarifies the [layer](layer.md) co-necessity structure: L0 ↔ L1 form a
co-necessary pair because their graduation criteria are mutually grounding.
L0 cannot fully close without L1, and L1 requires L0 to be graduated first.

## Concrete example

```
-- L0 graduation (Section VII):
graduation L0 -> L1:
  NC 1: form-is-derivable      FORM
  NC 2: prop-is-derivable      FORM
  NC 3: apply-is-defined       FORM
  NC 4: ground-is-defined      FORM
  close: graduation(L0 -> L1)  FORM
-- All 4 NCs present. L1 is licensed.
```

## Visualization

A bridge-building inspection. Before the bridge can carry traffic, inspectors
verify structural minimums: load capacity, foundation depth, material grade.
Graduation is the inspection sign-off. The bridge does not open on a promise.
It opens on a closed derivation.

## Speculation

Whether graduation can be automated — whether the [deriver](derives.md) can
synthesize the graduation block from the accumulated derivation state — is
[`OPEN`](FRAME.md). Automated graduation would mean the layer structure is
self-maintaining: no human needs to manually author the transition. Composing
`graduation` with [`discharge`](discharge.md) and the derivation matrix D:
graduation at layer k is a batch-discharge over all NCs of layer k, verifiable
as a column-completeness check on D. This would make graduation a decidable
property.
