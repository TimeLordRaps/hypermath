# Lean translation and proof audit

This directory is an incomplete Lean 4 translation of the native `.hm` files.
The pinned toolchain is Lean 4.14.0. A successful compilation accepts declarations
containing `sorry`; it does not establish their conclusions. Native `FORM` labels
in source comments record the `.hm` classification, not completed Lean proofs.

From this directory, run:

```console
python -u audit.py
```

The command prints source counts, performs a verbose build, reports the transitive
axiom dependencies of selected central declarations, checks independent finite
countermodels, and checks constructive finite trace examples. Each subprocess
has a 60-second timeout, output streams as
it arrives, and a silent subprocess receives a progress observation after 40 seconds.
Use `--timeout 90` to adjust the bound or `--lake PATH` to select the Lake executable.
`--inventory-only --details` lists every declared assumption without running Lean.

Exit meanings:

- `0`: the audited checks passed and no admitted proof was found in those surfaces.
- `1`: a build, tool, dependency report, or countermodel check failed.
- `2`: admitted theorem proofs remain; this is the current expected proof-gate result.
- `124`: a subprocess exceeded its time bound.

Even exit zero would not prove the consistency or arithmetic completeness of the
declared axioms, the soundness of the native language, or fidelity of every translation.

## Mechanical corrections and explicit assumptions

The original checkout failed to compile. Bodyless Lean `opaque` declarations
requested `Inhabited` defaults; they were replaced by explicit axiom declarations
for the source's uninterpreted type, function, and predicate parameters. This
exposes their assumed status. No admitted theorem was changed into a new axiom.

The original 29 parameter declarations are now explicit assumptions. Two further
source-backed projections, `pathStart` and `pathEnd`, express the actual endpoint
clause of `L3_ordinatics.hm:97–99`; the earlier translation confused path objects
with Forms and path length with the endpoint. No endpoint equations were invented.
The remaining 38 declarations are the translation's logical axiom clauses.

The [finite-trace repair](../docs/research/FINITE_TRACES.md) subsequently replaces
the `D` parameter with its finite congruence-preserving witness definition.
There are now 30 source parameters, 38 logical clauses, and 20 admissions. It
constructively proves `dIsReflexive` without changing its proposition-level API.

Missing external `ℕ`/iteration notation was replaced by Lean core `Nat` and
`Nat.repeat`. `orbitStructure` now uses the already declared `traceLevels` axiom
for its third pair, rather than applying symmetry to a proposition with the wrong
endpoints. The attempted reverse-filtration argument in
`plusAndAdditionallyAreDistinct` remains an explicit open proof premise.

## What the independent countermodel establishes

`Countermodels.lean` imports only the generic, axiom-free `Hypermath.Trace` module
and declares no custom axiom or admitted proof. It constructs a Boolean model
of all 24 logical L0/L1 axiom clauses:
similarity and congruence are universal, simulation is equality, application maps
every element to `true`, and ground is `false`. In that model:

- non-simulation does not imply non-congruence;
- `Derives` is symmetric, contradicting the advertised directionality consequence;
- the promised simulation cycle is not a consequence of that axiom prefix.

A second model uses three forms, equality for congruence and simulation, and
application `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 1`. It satisfies the same prefix but has no
congruence-preserving application edge. Its trace-defined `D` is equality, so
ground does not reach every form even though the deriver `1` returns after two
applications. The earlier unconstrained-`D` reflexivity probe has been replaced;
it would no longer model the current definition.

These are missing-implication witnesses for the stated prefix. They are not models
of all later L2/L3 assumptions and do not refute every possible completion of the
intended theory. Future changes to those axiom clauses require updating and reviewing
the countermodel correspondence.

`Audit.lean` prints dependencies without exporting its report as library theorems.
In particular, `Hypermath.selfDerivation` currently depends on `sorryAx` through
its admitted components. The file does not remove, discharge, or hide those gaps.
