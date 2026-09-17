# Reproducing paths across related boundaries

`lean4/Hypermath/PathTransport.lean` gives a conditional construction for
composition across distinct, related endpoints. The premise is an explicit
operation that reproduces each step while preserving a specified relation.
The construction retains the original path, its reproduced copy, and evidence
of correspondence at every vertex. It does not define native simulation,
construct the kernel's self-derivation, or establish an ordinal interpretation.

## Why reproduction is different from a connector

Suppose a first path runs from `a` to `b`, and a second from `c` to `d`.
Ordinary trace concatenation requires `b = c`. A relation between `c` and `b`
does not supply this equality, or a derivation path connecting them.

Instead, a reproduction operation can copy the second path starting at `b`.
Its new endpoint `d'` is related to `d`. The result runs from `a` through `b`
to `d'`. Both `c -> d` and `b -> d'` are retained. The output endpoint is
explicitly `d'`; it is never relabeled `d`.

The checked example has two disconnected successor chains. Their states are
pairs `(height, component)`, with dimensionless natural-number height and a
Boolean component label. A step increases height by one and preserves the
component. Equal heights are related across components. The path
`(1, true) -> (2, true)` reproduces from `(1, false)` as
`(1, false) -> (2, false)`. No path connects the two starting points.
`related_without_connector` proves that distinction.

This is an independently specified transition example, not a model of all
38 native logical clauses. It demonstrates that path reproduction and boundary
connection are different proof obligations.

## Constructive interface and preservation

`StepTransfer Step Related` takes a witnessed step `x -> y` and evidence that
`x` is related to `copyStart`. It returns a particular `copyEnd`, a witnessed
step `copyStart -> copyEnd`, and evidence that `y` is related to `copyEnd`.
The supplied function chooses the actual next object; the implementation does
not extract choices from existential propositions.

`reproduce` extends that operation to any finite trace by induction.
`Alignment` records the relation at every vertex, including the sole vertex
of an empty trace. Its theorems establish related starting and ending points,
equal edge counts, and preservation of correspondence under concatenation.
Counts and layer indices are dimensionless natural numbers.

`reproduce_compose` proves coherence for one fixed step operation: reproducing
a concatenation gives the same reproduction value as reproducing the first
path and then the second from its copied endpoint. It does not assert that
different choices of step operation produce equal copies.

`Composition` stores the first path, original second path, and reproduction
certificate. `composeAcross` constructs that value using a supplied boundary
relation in the direction `Related c b`. Symmetry is not needed or assumed.
The combined path has the sum of the original edge counts. Its edges are
the first path's edges followed by the copied edges, while the original
second path remains separately recoverable.

`Layer` retains this whole certificate beside a
[path-layer representation](PATH_LAYERS.md) of its combined path. `raise`
preserves the certificate and exact expanded path through any finite number
of layers; `raise_recovers_surface` also recovers the original grouped
representation. This is a Lean data construction, not a serialization format
or a parser for untrusted evidence. Lean proof irrelevance applies to the
propositional evidence fields. Distinct proof-term syntax is not preserved.

## The exact native obligation

Native `DStep x y` means `y = f2f x` together with `Congruent y x`.
Here `f2f` is primitive forming, `Congruent` is congruence (`=~`), and
`Simulation` is the source's simulation relation (`==`). They remain distinct
from equality and from similarity (`~~`).

For this deterministic, guarded step definition, `NativeOneStepLaw` says:

```text
Simulation x x' and Congruent (f2f x) x
  imply
Congruent (f2f x') x' and Simulation (f2f x) (f2f x').
```

`native_law_iff_transfer` proves that this proposition is equivalent to the
existence of a `StepTransfer DStep Simulation`. The forward construction
chooses `f2f x'`; the reverse direction uses the defining equality of a
native step. `nativeTransfer` is noncomputable because native forming remains
an uninterpreted source parameter. Neither construction adds a native axiom.

The law is **not entailed by the current 38 clauses**, even with the original
self-derivation proposition and its stronger cycle witness. The subsequently
checked [native transport countermodel](NATIVE_TRANSPORT_OBLIGATION.md) satisfies
all those conditions while ruling out even a finite reproduced subpath for
one related boundary. This identifies missing operational content in the
declared simulation relation. The conditional equivalence remains valid;
filtration alone is not presented as a derivation of its premise.

This interface reproduces exactly one step per step. Source descriptions of
mutual continuation reproduction do not yet settle whether every intended
reproduction must have this form. Reproduction using multiple steps or
stuttering needs a different interface and corresponding preservation laws.
The two-Boolean-state example `relation_alone_insufficient` proves that merely
declaring relatedness, even a universal equivalence, does not supply a step
operation. It makes no native-model claim.

## Checking and research boundary

The default Lean build imports the module. The layer reporter requires 23 new
dependency records, including the conditional native equivalence, constructors,
composition theorem, layer recovery, and counterexamples. Only the two native
records depend on `Form`, `f2f`, `Congruent`, and `Simulation`; they use no
additional native logical clause. One generic recovery theorem uses Lean's
propositional extensionality; the other 20 records report no axioms.
The audit binds the exact source and rejects missing or altered reports.

The existing Python/Verifier graph still handles its established record
protocol. It does not serialize or execute these path-transport certificates.
Next obligations are native derivation of a suitable reproduction law,
native generation and checking of the retained representation, and the
separate ordinal and arithmetic-truth interpretation. Choice-independent
composition through equivalence classes also needs its own laws.

One-step simulation and its extension to transition sequences have established
precedents; see CompCert's primary
[Smallstep formalization](https://compcert.org/doc/html/compcert.common.Smallstep.html),
especially `SIMULATION_STEP` and `simulation_star`. This construction makes
no novelty claim for that general pattern. Its present research role is to
isolate Hypermath's missing native law while retaining path evidence across
composition and finite representation layers.
