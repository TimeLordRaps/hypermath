# A cycle certificate must retain its intermediate steps

The source's deriver cycle requires more than the original four-conjunct
`selfDerivation` target. It requires a nonzero apply path whose intermediate
steps preserve simulation. That gap is now separated rather than argued:
`TargetAtLimitModel.target_does_not_yield_a_cycle_certificate` satisfies every
current logical clause, the target, and the cycle's endpoint closure, and
contains no inhabitant of the certificate type. The six-form model satisfies
every clause while having no nonzero preserving derivation path at all.

## How much more, exactly

"More than the target" was a comparison of fields until the certificate could be
read back out of its own trace. `Hypermath.driverCycleWitness_iff` now measures
it:

    Nonempty DriverCycleWitness  <->  Simulation (f2f deriver) deriver
                                   /\ Simulation (f2f (f2f deriver)) (f2f deriver)
                                   /\ driverCycleClaim

The third conjunct is the whole of the target, by
`selfDerivation_iff_driverCycleClaim`. So the gap is the first two conjuncts and
nothing else: the two apply edges at the deriver, each retaining simulation at
the edge rather than only across the pair. A structure carrying a trace, a
length and a closure turns out to carry exactly three propositions about
`Simulation`.

The equivalence uses no clause. Its report lists four source parameters ---
`Form`, `Simulation`, `deriver`, `f2f` --- and no axiom, because it is an
unfolding of the definitions rather than a consequence of the theory. That is
what makes it usable as a reading of the certificate: a reader who distrusts the
39 pre-closure clauses can still be held to it.

Getting it required an addition to the trace infrastructure, which is itself
worth recording. `Trace` could be built (`cons`, `compose`, `map`), measured
(`length`, `edges`) and transported, but never taken apart: nothing recovered an
edge's evidence from a trace, so every previous argument about a trace of a
stated length had to be made by induction over a trace with *variable*
endpoints. `Trace.uncons_of_length_succ` and `Trace.eq_of_length_zero` are the
missing eliminators, and with them a trace between two *named* forms can be
decomposed. The gap was not in the theory; it was in the reading equipment.

## The closure is the part the target already gives

`driverCycleWitness_iff_of_transitive` drops the third conjunct under a
hypothesis: if `Simulation` is transitive then the two edges compose into the
closure, and the certificate is exactly the two edges. Nothing in the
development asserts that transitivity --- `Simulation` is a declared parameter
and the clauses naming it relate it to other relations, never to itself --- so
it is a hypothesis here and not a clause. But both models of the independence
result satisfy it (`HypermathTargetAtLimitModel.simulation_is_transitive`, and
the transport countermodel's `simulation_is_equivalence`), and
`cycle_certificate_independent_under_transitivity` bundles that: **adding
transitivity to the 39 pre-closure clauses would not decide the certificate either.**

Which settles what the open question is about. It is not about the endpoint
closure; that is the conjunct the target supplies, and under transitivity it is
not even an independent demand. It is about whether the two intermediate steps
retain simulation --- and by
`no_driver_cycle_witness_of_successor_agreement`, whether they do is whether
apply is the ordinal successor.

This model used to satisfy the original target as well, and that pairing is
what the thesis above was read off: a model with the target and without the
preserved execution shows that proving the target leaves a correspondence
obligation behind. It no longer satisfies the target. Moving the deriver to the
limit put it on a three-step cycle while the target's fourth conjunct asks for
a two-step return, so `self_derivation_target_fails_at_limit` refutes it here
and only that conjunct is responsible. What this model separates is now the
stronger thing: every clause can hold while the target fails.

The thesis keeps a witness, in another file and in a different shape.
`Hypermath/TransportCountermodel.lean` interprets the same four conjuncts,
`self_derivation_holds` proves them, and
`full_model_with_cycle_without_reproduction` bundles them with all 39 pre-closure clauses
and a two-step `DriverCycleWitness` that genuinely exists there. So the target
is consistent with the clauses, and consistent with them together with a real
cycle --- and `native_one_step_law_fails` and `no_step_transfer` show the
correspondence obligation surviving all of that. That is a stronger statement
of the thesis than the one this note was built on, since it grants the cycle
rather than withholding it.

The exact pairing the paragraph above describes --- every clause, the target,
and no nonzero preserving path at all --- was for a while witnessed by neither.
`FiniteActionCountermodel` had it and lost the target; `TransportCountermodel`
has the target and an actual preserving path. Nothing ruled the pairing out:
the target's second conjunct asks only that every form has *some* `D`-entry to
itself, and the empty trace supplies that, so the target does not by itself
demand a nonzero path. What it demands is the two-step return, and the two-step
return is available at the limit --- the finite-action model gives up on it for
a reason of its own, not for one the declaration forces.

`TargetAtLimitModel.lean` is that model. Its limit sits on the two-cycle
`b0 -> b1 -> b0` with the deriver at its head, and
`full_clauses_and_target_without_nonzero_D` carries all 44 clauses, the original
target, and the absence of any positive-length `DEntry` together, at the
declared position and on `propext` alone. The congruence classes of the limit's
cycle are the interesting part: `axLimitIsLimit` makes anything derivable from
every finite position derivable from the limit, the finite tail `a1 -> a2 -> a1`
occupies two classes, and so the limit's cycle must occupy those same two. Two
forms, two classes, and therefore every apply edge across the whole model
changes class --- which is exactly the condition that leaves no preserving step
anywhere. The clause that constrains the limit is what supplies the absence.

The new certificate and lemmas in `lean4/Hypermath/L3Ordinatics.lean` expose
this distinction. They preserve the original target and add no native axiom.
They do not claim an inhabitant of the stronger certificate type.

## The certificate that existed was standing still

Both results above are about a pairing, and a pairing is only as strong as its
positive side. The positive side was `HypermathTransportCountermodel`, and
`transport_cycle_is_degenerate` records the fact nobody had looked at: apply
fixes its deriver. So its two-step trace is the deriver standing still twice,
and `driverCycleWitness_of_fixed_deriver` shows that needs nothing else ---
given `f2f deriver = deriver`, both retained edges and the closure are
instances of reflexivity of `Simulation` at the deriver. Even that reflexivity
is not a clause, which is why the lemma takes it as a hypothesis; but no model
has to work for it, because a model that fixes the deriver will have it for
free unless it goes out of its way.

For most of this development that was the only inhabited certificate anywhere.
The independence results were true as stated and are unaffected. What was
missing is that they were being read as *a cycle is consistent with the
clauses*, and a fixed point is not a cycle. The certificate type cannot tell
the difference --- `Trace` records the edges, and an edge from a form to itself
is an edge --- so the distinction had to be stated outside it.

`lean4/Hypermath/NondegenerateCycle.lean` is the model that states it. Seven
forms: a five-form finite tail `a0 -> a1 -> a2 -> a3 -> a4 -> a3` reachable
from ground, and a two-form limit cycle `l0 -> l1 -> l0` carrying the deriver
at `l0 == ordinalLimit`. `Simulation` is equality of semantic class, both cycle
forms share class three, and so the two retained edges hold across a step that
moves. `full_axioms_hold` carries all 39 pre-closure clauses,
`apply_moves_the_deriver` is `decide`, and
`nondegenerate_cycle_with_all_clauses` bundles the three. Pairing it against
the target-at-limit model, where apply also moves the deriver and no
certificate exists, gives
`cycle_certificate_independent_nondegenerately`: **the independence is not an
artefact of a fixed point.** It is not decided even among the models where the
cycle is real.

The shape of the new model is forced in the same way the target-at-limit one
was, and by the same clause. `axSuccExtends` denies
`Simulation (ordinalSucc x) x`, so a model with a certificate cannot let
`ordinalSucc` be apply at the deriver --- which is
`no_driver_cycle_witness_of_successor_agreement` read as a constraint on model
building rather than as an obstruction. Here `ordinalSucc` sends every form
outside the tail back to `a0`, and `f2f` sends `l0` to `l1`; they disagree at
exactly the point where a certificate needs them to. The two models of the
pairing differ in that one law and in nothing else that any clause mentions,
which is what
`certificate_tracks_successor_agreement` already said and this pair now says
without a fixed point anywhere in it.

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
the certificate. `selfDerivationOfWitness` derives the original target from its
closure field. **The converse is false.**
`TargetAtLimitModel.no_driver_cycle_witness` refutes it in a model of every
clause where the target holds, and what is missing there is only the path: the
certificate's `closes` field is available, since `driverCycleClaim` holds and is
what yields the target in the first place. Simulation is equality in that model
and apply fixes no form, so an edge asking for both `y = f2f x` and
`Simulation y x` asks for a fixed point, and `no_simulation_step` shows there is
none. Refuting the converse needs exactly that combination, which is why neither
of the other two models does it: `FiniteActionCountermodel` gives up the target,
and `TransportCountermodel` has `Nonempty DriverCycleWitness`, the conclusion.

So the certificate's claim about itself --- that it is stronger than the target
--- is a separation and not a reading of the definitions, and the obligation it
names survives any proof of the target.
The weaker `driverInDAtSimulationOfCycle` interface remains available with its
original meaning: a zero-step self-read together with endpoint simulation.
It does not return this stronger certificate.

The type uses Lean's dependent types and inductive traces as infrastructure.
Encoding these witnesses as native forms and deriving their ranked acceptance
remain additional obligations; the existence of this type does not discharge
them.

## A model with no preserving steps, where the target fails

In `lean4/FiniteActionCountermodel.lean`, application has the cycles
`a1 -> a2 -> a1` and `b0 -> b1 -> b2 -> b0`, with `a0 -> a1`.
Simulation is equality. The deriver is `b0`, which is also `ordinalLimit`, and
its cycle takes three applications to return; two applications reach `b2`. The
target's fourth conjunct asks for simulation between the two-step endpoint and
the deriver, so it fails here. Only that conjunct fails: the first three still
hold, which is what makes the failure a statement about the cycle's length
rather than about the model. When the deriver was `a1` --- on the two-step
cycle --- the fourth conjunct held too, and the target with it.

Congruence is equality of class labels. The respective labels of
`a0,a1,a2,b0,b1,b2` are `0,1,2,3,1,2`. Every apply edge changes its class
label. Therefore no apply edge preserves congruence. The `a1` cycle does return
to its label in two steps, which is why the deriver's earlier position there
carried the target; `b0` is labelled `3` and its two-step endpoint `b2` is
labelled `2`, so it returns to neither its label nor its form.

The four added checked results establish:

| Declaration | Result |
| --- | --- |
| `no_preserving_step` | No pair of forms satisfies the interpreted `DStep` |
| `every_D_entry_is_empty` | Every interpreted `DEntry` has length zero |
| `no_nonzero_D_entry` | No positive-length interpreted `DEntry` exists |
| `full_clauses_without_nonzero_D` | All 39 pre-closure clauses hold, the original self-derivation target fails, and that absence holds with them |

The first three results use Lean's propositional extensionality. The combined
result additionally uses quotient soundness through the existing model. None
uses an admission or adds a native logical clause. This is a result about the
current formalized clauses, not a refutation of every possible source-native
realization.

The fourth result was called `full_clauses_and_target_without_nonzero_D` while
the target held here, and this note went on describing that model after the
declaration of the deriver's position changed it. The theorem's own docstring
records the change --- the interpretation satisfied the target vacuously before
the deriver's position was declared and no longer does, which closes that route
to the target. A declaration table naming a theorem that no longer exists is now
a test failure rather than something a reader has to notice.

Reading the change off this file alone invites a second error, which is worth
naming because it was made here first: that no model satisfies the target at
all. `TransportCountermodel` does, under its own interpretation of the same
four conjuncts. A model file that refutes a proposition says nothing about the
other files, and this repository has several that interpret the same target
differently on purpose.

`TargetAtLimitModel.lean` carries the complementary results, in a namespace of
its own so that the two interpretations never share a declaration:

| Declaration | Result |
| --- | --- |
| `self_derivation_target_holds` | All four conjuncts hold at the declared deriver position |
| `no_preserving_step` | No pair of forms satisfies that model's interpreted `DStep` either |
| `full_clauses_and_target_without_nonzero_D` | All 44 clauses, the original target, and no positive-length `DEntry` |
| `deriver_is_not_finite` | The limit is outside the tower reachable from ground |
| `no_simulation_step` | No apply edge retains simulation, since apply fixes no form |
| `no_driver_cycle_witness` | The typed cycle certificate has no inhabitant there |
| `target_does_not_yield_a_cycle_certificate` | Every clause, the target, endpoint closure, and no certificate |

Those cost less than the six-form model's: `propext` alone, with
`self_derivation_target_holds` and `congruence_is_equivalence` depending on no
axiom at all. Nothing there reaches quotient soundness, because the clause
proofs are structural rather than simp-driven over a quotient.

Two models now interpret the same four conjuncts over a six- and a five-form
carrier and disagree about them, which is the intended shape: the clauses
decide neither way. What the pair adds over either alone is that the
disagreement is not about the clauses at all. Both satisfy all 39 pre-closure
clauses; they differ
in the length of the cycle at the deriver's position, and the clauses do not
mention it.

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
either antecedent from the current 44 clauses.

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

The audit now binds 76 production milestones and 22 finite-action model
reports, alongside the existing groups. The inventory is now 66 assumptions
and no admission sites. The strict original target, source adequacy, and
recursive arithmetic completeness gates remain unresolved.
