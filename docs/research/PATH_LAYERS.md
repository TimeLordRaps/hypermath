# Finite layers over witnessed native derivation paths

[`PathLayers.lean`](../../lean4/Hypermath/PathLayers.lean) connects finite
representation layers to the existing derivation-path witnesses. It starts
from a supplied path carrying evidence for each edge. At the next layer an
atom retains that entire lower representation, with its start and end still
present in the type.

This is representation infrastructure built in Lean. The native specialization
uses the existing `DEntry` (derivation-entry) type; it does not postulate new
native edges or identify its atom constructor with primitive forming.

## The source geometry being preserved

In the existing source formalization, `DStep x y` means
`y = f2f x` together with `Congruent y x`. A `DEntry x y` retains a finite
sequence of such witnessed steps. `D x y` states only that some such entry
exists. The new layers carry the entry value itself, rather than replacing
it with that existence proposition.

`NativeSurface n x y` is a layer-`n` representation over these entries.
Composition requires matching endpoints: a representation from `x` to `y`
can precede one from `y` to `z`. The next atom retains the complete lower
representation; it is not asserted to fit into one unchanged native `Form`.

`native_composition_lift_preserves` proves exact recovery of a composed
representation after any finite number of lifts. Expanding it produces
exactly the existing `dEntryCompose` of the original witnessed paths.
The generic results also preserve the ordered endpoint pairs and the sum of
the actual edge counts. Counts are dimensionless natural numbers, not ordinal
truth ranks.

`native_endpoint_preserved` connects the expanded path to source forming:
applying `f2f` the recorded number of times takes its start to its end. This
uses the existing `dEntryEndpointIteration` theorem; no new application or
ordinal law is assumed.

Exact recovery is equality of Lean values, retaining path structure and
grouping. Individual edge proofs live in propositions and are subject to
Lean's proof irrelevance; this is not a serialization of distinct proof-term
syntax or a new parser for untrusted evidence. The separate
[submitted-frame protocol](RETAINED_EXECUTION.md) handles retained raw
execution records and rejection. These are distinct checking surfaces.

## Where the monoid applies

All paths retain their endpoint constraints. Paths from one fixed object back
to that same object form the `loopSequencing` instance of the common monoid
interface. Composition is associative and has an identity under equality of
expanded witnessed paths. At the base, its identity is the existing zero-step
self-read. The kernel's self-derivation is not identified with this identity.
`loopLiftMap` preserves those laws across adjacent representation layers.

The source's proposed cycle closes by **simulation**, not by an equality of
its endpoint indices. Its path runs from `deriver` to `f2f(f2f(deriver))` and
carries a simulation closure between them. It therefore cannot automatically
be supplied as a strict loop at `deriver`. Reusing it as such would need a
justified transport or composition rule for those relational boundaries.
The source relation is preserved as simulation; it is not replaced by
similarity, congruence, or equality.

## Retaining the stronger cycle certificate

`CycleSurface n` retains a layer representation of the original
simulation-preserving path, its two-edge length, and its simulation closure.
`recoverCycle_reifyCycle` proves exact recovery of a supplied
`DriverCycleWitness`, including its closure field, at every finite layer.

The cycle constructors are marked `noncomputable` because they depend on the
uninterpreted native `deriver` and forming parameters. They are formal
constructions, not an executable native verification engine. The generic
path-layer code has an executable two-step natural-number probe.

The separate `cycle_witness_length_preserved` result uses the existing
simulation-to-congruence filtration to obtain a derivation entry and retain
its two edges. That weaker projection is not substituted for the full cycle
certificate: `CycleSurface` retains the original stronger path and closure.

## Wrapping cannot supply missing base evidence

`nonempty_iff_base` proves that a layer path between two endpoints exists
exactly when a base witnessed path between those endpoints exists.
`native_reachability_iff` specializes this to the existing `D` relation.
`native_without_steps` shows that, if there are no admissible native steps,
every expanded representation still has zero edges and identical endpoints.

Likewise, `cycle_surface_iff_witness` proves that a cycle surface exists
exactly when the stronger cycle witness exists. No inhabitant of that witness
is constructed. Representational nesting can retain a certificate; it cannot
provide evidence missing at its base merely by introducing more layers.

This leaves the existing full-clause countermodels and cycle obstructions
intact. It does not claim that every possible richer next-layer logic has the
same reachability restriction; the theorem concerns this precise path grammar.

## Proof dependencies and remaining bridge

The required layer audit adds 27 exact reports: 19 theorems, four law-carrying
or cycle constructions, and four regression results. Ten have no axiom
dependencies and eight use only propositional extensionality. Nine native
specializations use explicitly recorded existing source parameters; the
simulation-to-congruence length result additionally uses the existing
`filtrationSimCong` clause. No new native assumptions or admitted proofs are
introduced, and earlier report dependencies are preserved.

The remaining bridge is to derive generation and checking of these
representations from the intended native verification geometry, including the
cycle's actual edge evidence and any transport required by relational
closure. The Python graph protocol is unchanged. Ordinal interpretation,
transfinite reuse, arithmetic truth coverage, and novelty remain unresolved.

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/path-layers-audit.json
python -u -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```
