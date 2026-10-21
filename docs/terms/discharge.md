# discharge

> *hypermath | formal-universality | dictionary*

## What it is

`discharge` is the act that terminates a single [`FRAME`](FRAME.md) dependency:
a finite [`derives`](derives.md)-sequence that, when completed, produces a
closure certificate for one named OPEN item. `discharge :: Form -> Prop`, where
the `Form` is the `FRAME` being discharged. After discharge, the previously
`FRAME` criterion is CLOSED within the context of the derivation block that
encloses it.

## What it is not

- Not undoing a previous derivation. `discharge` is not reversal. It is
  *completion* of a previously stated obligation.
- Not the same as [`derives`](derives.md). `derives` is the motion; `discharge`
  is the arrival that closes the motion. You can be mid-derives without having
  discharged.
- Not wholesale closure of the system. Discharging one `FRAME` does not close
  other `FRAME`s. Each `FRAME` requires its own discharge sequence.

## What it clarifies

Clarifies the role of [`FRAME`](FRAME.md): every `FRAME` is a named promise that
a discharge sequence will be produced at the designated layer. The `FRAME` is
not an assertion that the discharge cannot happen — it is a deferred citation.

Clarifies [`graduation`](graduation.md): a layer graduates when all its NCs
(necessary criteria) have been discharged. The graduation close is the batch
discharge certificate.

## Concrete example

```
-- L0 Section VII graduation close:
graduation L0 -> L1
-- Discharges all 4 NCs:
--   form-is-derivable, prop-is-derivable, apply-is-defined, ground-is-defined
-- Each NC was a FRAME. After Section VII, each transitions from FRAME to FORM.
```

## Visualization

A receipt. You have been holding a ticket stub (`FRAME` = owed discharge). When
the item arrives at the counter and you exchange the stub, you are left holding
the item and the stub is consumed. The `FRAME` is discharged; you now hold a
`FORM` certificate.

## Speculation

Whether discharge can be automated — whether the [deriver](derives.md) can
identify `FRAME` obligations and produce discharge sequences without human
prompting — is the core [`OPEN`](FRAME.md) question for the deriver's role at
L2+. Automated discharge is the operational definition of the system being
self-deriving. Composing `discharge` with [`graduation`](graduation.md) and
[`derives`](derives.md): if discharge sequences are matrix-searchable in D,
then [graduation](graduation.md) becomes a fixed-point computation over D.
