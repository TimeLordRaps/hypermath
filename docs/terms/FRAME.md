# FRAME

> *hypermath | formal-universality | dictionary*

## What it is

`FRAME` is a closure-status label applied to a derivation block or a necessity
criterion (NC) when the claim is structurally present but not yet closable at
the current layer. A FRAME item has:

- **A named dependency**: exactly what content from a higher layer is needed
- **A named layer**: the layer at which the dependency is expected to close
- **A cite back**: the item in the current layer that established the FRAME

`FRAME` is not failure. It is a deferred citation — an honest forward dependency.

## What it is not

- Not OPEN. OPEN is a metasystem status (bookkeeping). `FRAME` is a formal
  within-system status: the item exists in the layer file, carries its dependency
  explicitly, and has a named closure target.
- Not wrong. A `FRAME` derivation is structurally valid at its layer. It is just
  not closable yet because it needs content from above.
- Not a placeholder. A `FRAME` block is a complete derivation attempt — it
  reaches exactly as far as the current layer supports and honestly names where
  it stops.

## What it clarifies

Clarifies why every layer has known forward dependencies: the `FRAME` labels are
the dependency graph. Reading all `FRAME` items in a file gives the full set of
obligations that higher layers must discharge.

Clarifies [`discharge`](discharge.md): every `FRAME` requires a discharge
sequence at its named layer. The layer that fails to discharge a `FRAME` cannot
graduate.

## Concrete example

```
-- L1 self-kernel:
-- step 22: opaque(D) — derivation matrix. FORM (schema). FRAME/L3 (content).
-- step 25: derive(deriver-is-in-D) — D[deriver][deriver] entry exists. FORM.
--          content at == level: FRAME/L3.
-- These are honest FRAME items: the schema exists at L1;
-- the ==-level content requires L3's ordinal structure to close.
```

## Visualization

A loan paper. The debt is acknowledged. The value is present on record. The
repayment is named and dated. The loan paper is not the money — but it is a
real document with real obligations attached. A `FRAME` is a loan paper in the
derivation structure.

## Speculation

Whether `FRAME` can be automatically propagated — whether the [deriver](derives.md)
can walk the FRAME dependency graph and sequentially discharge items in
[weakest-frame-first](derives.md) order — is exactly the goal of the autonomous
derivation runs. Composing `FRAME` with [`graduation`](graduation.md): all `FRAME`
items in a layer must be discharged before graduation proceeds. A fully automated
deriver turns the FRAME graph into its own work queue. See also
[`discharge`](discharge.md) for the closure act.
