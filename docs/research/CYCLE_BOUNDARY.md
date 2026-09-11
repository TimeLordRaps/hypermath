# The self-derivation cycle is not entailed by the current clauses

The full-clause model in `lean4/FullAxiomModel.lean` satisfies all 38 current
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

The separate six-form model in `lean4/FiniteActionCountermodel.lean` satisfies
all 38 clauses **and** the same self-derivation target. Together, the two models
show that the target is independent of the current clauses in these
interpretations. That six-form model also refutes the proposed arithmetic
bridges. Accordingly, establishing the cycle would still leave arithmetic
interpretation and completeness to prove.

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
assumption inventory remains 67 declarations: 29 parameters and 38 clauses.
The audit now binds 38 production milestones, including the three conditional
assembly and equivalence results.

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
