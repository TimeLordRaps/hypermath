# The self-derivation cycle is not entailed by the current clauses

The full-clause model in `lean4/FullAxiomModel.lean` satisfies all 44 current
logical clauses and refutes the proposed two-step simulation cycle. It also
refutes the nontrivial simulation-pair claim and the exact closed
`Hypermath.selfDerivation` target. These are results about the current Lean
translation, not a refutation of every possible source-adequate realization.

## Exact remaining obligation

Write `C` for the original four-conjunct self-derivation target and `S` for
`Simulation (f2f (f2f deriver)) deriver`. These are propositions, with no physical
unit. The first three conjuncts of `C` assert ground self-continuation,
reflexive finite self-reads, and the two path-composition identity laws.
The reviewed clauses prove those three conjuncts. Consequently:

\[
C\quad\Longleftrightarrow\quad S.
\]

`selfDerivationOfCycle` proves `S -> C`, and
`selfDerivation_iff_driverCycleClaim` proves the equivalence. Both use the
existing `axGroundSelf` and `axComposeIdentity` clauses together with source
parameters; neither uses an admission or a new native axiom. The cycle is an
explicit hypothesis in the first result. Neither theorem proves it.

## Checked counterexample

In the full model, forms are pairs `(n,b)` of a natural number and a Boolean.
Ground and deriver are `(0,false)`, application sends `(n,b)` to `(n+1,b)`,
and simulation is equality. Thus the claimed cycle would require
`(2,false) = (0,false)`, which is false. Also, simulation of two distinct forms
is impossible when simulation is equality, regardless of their similarity.

The reporter checks:

- `driver_cycle_claim_fails`;
- `nontrivial_simulation_claim_fails`;
- `self_derivation_target_fails`;
- `full_clauses_without_cycle_or_nontrivial_simulation`.

The first three proofs have no axiom dependencies. The combined model theorem
has exactly Lean's `propext`, `Classical.choice`, and `Quot.sound` dependencies,
inherited from the construction satisfying the full clauses. It has no
`sorryAx` dependency and uses no native logical assumptions as extra premises.
The complete model reporter now binds 30 dependency reports.

The six-form model in `lean4/FiniteActionCountermodel.lean` used to supply the
other half of that pairing, and this paragraph credited it with satisfying all
44 clauses **and** the same self-derivation target. It no longer satisfies the
target: declaring the deriver to be at the limit moved it onto a three-step
cycle, and `self_derivation_target_fails_at_limit` refutes it there.

This paragraph then drew the wrong conclusion from that for a while, and the
error is worth keeping visible because it is easy to repeat. It said the
conclusion survived with different witnesses, and named
`HypermathTransportCountermodel.self_derivation_holds` and
`HypermathTargetAtLimitModel.self_derivation_target_holds` --- two models that
both **satisfy** the target. Two satisfying models are satisfiability twice
over. Independence needs one of each, and the refuting one was sitting in the
same sentence, described as a loss.

`HypermathFiniteActionCountermodel.self_derivation_independent` is the pairing:
every clause with the target on the transport side, every clause without it
here, on `propext` and `Quot.sound`. So **the target is not decidable from the
declared clauses**, which is what this page had been claiming without a
declaration to carry it. Note what it does not say: the certificate pairing
below is a separate statement, because a model can refute the certificate while
satisfying the target and `HypermathTargetAtLimitModel` is one. The six-form
model also refutes the proposed arithmetic bridges. Accordingly, establishing
the cycle would still leave arithmetic interpretation and completeness to
prove.

The stronger question is settled the same way and is now a single checked
statement rather than a pairing a reader has to assemble:
`HypermathTargetAtLimitModel.cycle_certificate_independent` puts the two
verdicts on the typed cycle certificate side by side --- the transport model
satisfies every clause with an inhabited certificate, the target-at-limit model
satisfies every clause with none --- on `propext` alone. So the certificate is
not merely unproved: it is not decidable from the declared clauses, and neither
is it decidable from the target, which
`target_does_not_yield_a_cycle_certificate` shows holds in the model where the
certificate fails.

## Proof and interface correction

The unproved statements remain visible, with their original logical content:

| Previous declaration | Current surface |
| --- | --- |
| Admitted `simulationPairExists` theorem | Unproved `simulationPairExistsClaim : Prop` |
| Admitted `driverCycle_FRAME` and `driverCycleIsClosed` theorems | Unproved `driverCycleClaim : Prop` |
| `driverInDAtSimulation` using the admitted cycle | `driverInDAtSimulationOfCycle`, requiring the cycle explicitly |
| `selfDerivation` using the admitted cycle | `selfDerivation : Prop`, the exact original closed target |

This changes the Lean proof interface: a consumer can no longer use the target
as an available proof. Five admission sites were withdrawn, leaving 11. Their
removal records unsupported claims, not five newly proved results. The native
assumption inventory is 66 declarations: 26 source parameters and 40
logical axiom declarations, which the model structures enumerate as 44
clauses because the single `ordinatics` interface projects to five.
The audit now binds 76 production milestones, including the three conditional
assembly/equivalence results and seven results about explicit cycle witnesses.
The [cycle-witness account](CYCLE_WITNESSES.md) shows why endpoint closure
does not supply a nonzero preserving path and states the finite-successor
obstruction. It preserves this original target separately from the stronger
source-cycle certificate.

The audit accepts the exact proposition definition as an integrity observation,
while retaining `self_derivation=UNKNOWN` and `proof_admissibility=FAIL`.
The strict gate still requires a theorem of the exact original closed statement.
A weakened statement, an implication assuming the cycle, or forged summary
status cannot substitute for that proof. The named proposition's dependencies
describe its vocabulary; they do not certify its truth.

## Consequence for native acceptance

The `.hm` source proposals are preserved unchanged. A source-adequate account
of simulation and native generation must explain which rule excludes the
countermodel and why that rule follows from the intended source mechanism.
Adding the desired cycle as an axiom would assume the current remaining
obligation. Typed record acceptance, observation preservation, arithmetic
soundness, and transfinite truth coverage still require their own constructions.

For the proposed resolution architecture, see [Constructive Quine Synthesis
and Bisimulation Quotients](CONSTRUCTIVE_QUINE_SELF_CLOSURE.md). That document
is a specification, not a completed proof. It sets out how explicit
combinatorial Quine terms (Kleene's Second Recursion Theorem) and Accessible
Pointed Graph (APG) bisimulation quotients would exclude the rigid syntactic
countermodel and yield a machine-verified proof of self-closure. The Lean
construction it schedules, `lean4/Hypermath/ConstructiveQuine.lean`, does not
yet exist, so self-closure remains an open obligation.
