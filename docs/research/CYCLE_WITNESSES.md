# A cycle certificate must retain its intermediate steps

The source's deriver cycle requires more than the original four-conjunct
`selfDerivation` target. It requires a nonzero apply path whose intermediate
steps preserve simulation. The six-form model satisfies every current logical
clause and the original target while having no nonzero preserving derivation
path at all. Thus even proving that target would leave a source correspondence
obligation about the cycle's actual execution.

The new certificate and lemmas in `lean4/Hypermath/L3Ordinatics.lean` expose
this distinction. They preserve the original target and add no native axiom.
They do not claim an inhabitant of the stronger certificate type.

## Source requirements

The relevant source files are preserved unchanged:

- `L1_relations.hm`, section VII, requires a finite deriver cycle with simulation
  retained at every step. It separately defines `D` by traces preserving at
  least congruence and distinguishes a zero-step self-read from its proposed
  nonzero cycle content.
- `L3_ordinatics.hm`, section VI, step 3, compares a two-step path record with
  the zero-step record. Steps 4–6 then assert a nonzero cycle and preservation
  at every intermediate step. Endpoint closure alone supplies neither of those
  edge proofs. Literal equality of retained zero- and two-step records would
  also erase their different lengths.
- `L3_ordinatics.hm`, section II, gives the finite successor equation
  `ordinal_succ(apply^n(ground)) = apply^(n+1)(ground)`. Section III requires
  successor not to simulate its input. Their consequence for a proposed
  simulation-preserving apply path is proved below, with the equation kept
  as an explicit hypothesis.

Here simulation is the source relation `Simulation`; it is not silently
replaced by equality, congruence, or similarity. Length counts retained edges
and has no physical unit. A path's endpoint relation and its intermediate-edge
relations are distinct propositions.

## Constructive certificate interface

`SimulationStep(x,y)` means both `y = f2f(x)` and `Simulation(y,x)`.
`SimulationEntry(x,y)` is a finite `Trace` of those witnessed edges.
`simulationEntryToDEntry` uses the existing filtration clause to turn each
simulation edge into a congruence-preserving edge. Its length theorem proves
that this conversion retains the number of steps.

`DriverCycleWitness` retains:

1. a `SimulationEntry` from `deriver` to `f2f(f2f(deriver))`;
2. a proof that this particular path has exactly two edges;
3. the endpoint closure `driverCycleClaim`.

`driverCycleWitnessOfSteps` constructs this certificate from proofs of both
specific simulation steps and endpoint closure. Its existence theorem checks
that the constructor actually produces an inhabitant from those premises.
The constructor is noncomputable because native forms and application remain
uninterpreted source parameters; this is not a newly executable native checker.

`witness_has_two_D_steps` derives a two-edge congruence-preserving trace from
the certificate. `selfDerivationOfWitness` derives the original target from
its closure field. The converse is not supplied and fails in the model below.
The weaker `driverInDAtSimulationOfCycle` interface remains available with its
original meaning: a zero-step self-read together with endpoint simulation.
It does not return this stronger certificate.

The type uses Lean's dependent types and inductive traces as infrastructure.
Encoding these witnesses as native forms and deriving their ranked acceptance
remain additional obligations; the existence of this type does not discharge
them.

## A target-satisfying model with no preserving steps

In `lean4/FiniteActionCountermodel.lean`, application has the cycles
`a1 -> a2 -> a1` and `b0 -> b1 -> b2 -> b0`, with `a0 -> a1`.
The deriver is `a1`, and simulation is equality. Consequently applying twice
returns the deriver to itself and the original target holds.

Congruence is equality of class labels. The respective labels of
`a0,a1,a2,b0,b1,b2` are `0,1,2,3,1,2`. Every apply edge changes its class
label. Therefore no apply edge preserves congruence, even though the deriver's
two-step endpoint returns to its original label and form.

The four added checked results establish:

| Declaration | Result |
| --- | --- |
| `no_preserving_step` | No pair of forms satisfies the interpreted `DStep` |
| `every_D_entry_is_empty` | Every interpreted `DEntry` has length zero |
| `no_nonzero_D_entry` | No positive-length interpreted `DEntry` exists |
| `full_clauses_and_target_without_nonzero_D` | All 38 clauses and the original self-derivation target hold together with that absence |

The first three results use Lean's propositional extensionality. The combined
result additionally uses quotient soundness through the existing model. None
uses an admission or adds a native logical clause. This is a result about the
current formalized clauses, not a refutation of every possible source-native
realization.

## The finite successor obstruction

Let `E(n) = finiteApplyPosition(n)`. The named proposition
`FiniteSuccessorAgreement` is

\[
\forall n\in\mathbb N,\quad
\operatorname{ordinalSucc}(E(n))=E(n+1).
\]

It is a proposed correspondence law, not an assumption added to the foundation.
If it holds and `x = E(n)`, then `ordinalSucc(x) = f2f(x)`. The existing
`axSuccExtends` clause gives `not Simulation(ordinalSucc(x),x)`, hence
`not Simulation(f2f(x),x)`.

`no_simulation_step_at_finite_of_successor_agreement` checks that argument.
`simulation_trace_from_finite_is_empty` extends it to every simulation trace
starting at a finite ground form: a nonempty trace would already require the
forbidden first edge. It follows that

\[
\operatorname{FiniteSuccessorAgreement}\ \land\
\operatorname{finiteApplyFromGround}(\operatorname{deriver})
\quad\Longrightarrow\quad
\neg\operatorname{Nonempty}(\operatorname{DriverCycleWitness}).
\]

`no_driver_cycle_witness_at_finite_successor` proves this implication. The
three obstruction lemmas use source parameters and `axSuccExtends`, with no
admitted proof, classical choice, or new logical clause. They do not establish
either antecedent from the current 38 clauses.

## Consequence for the intended architecture

A source-adequate construction must specify how arithmetic successor,
execution of the checker, and rank-changing representation act on their
respective objects. If they use the same apply operation on finite ground
forms with the successor equation above, its individual steps cannot also
preserve the source's strict simulation relation. Endpoint return after two
steps does not remove this obstruction.

A proposed separation by type, rank, or observation requires actual source
rules and a preservation theorem. Merely naming separate layers, weakening
simulation to similarity, or postulating acceptance does not supply that
construction. The remaining work is to derive the appropriate operational
rules, retain their records, and prove arithmetic soundness and truth coverage.

The audit now binds 45 production milestones and 22 finite-action model
reports, alongside the existing groups. The inventory remains 67 assumptions
and 11 admission sites. The strict original target, source adequacy, and
recursive arithmetic completeness gates remain unresolved.
