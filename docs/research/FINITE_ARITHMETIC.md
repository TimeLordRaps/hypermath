# Finite closure, arithmetic observations, and action compatibility

The native specification describes finite forms as the least set containing
ground and closed under application (`L3_ordinatics.hm:123–128`). The Lean
translation now defines this set instead of assuming an unconstrained predicate:

\[
E(n)=\operatorname{f2f}^{n}(\mathrm{ground}),\qquad
\operatorname{finiteApplyFromGround}(x)\iff\exists n\in\mathbb N\;E(n)=x.
\]

`finiteApplyGround`, `finiteApplyClosed`, and `finiteApplyMinimal` prove the base,
closure, and leastness requirements. Here `E(n)` is an existing `Form`, not a new
tagged representation of a natural number. The index is part of Lean's host
infrastructure. Different indices are not assumed to produce different forms.

## The checked finite arithmetic bridge

For a witnessed path `p : DEntry x y`, `finiteTraceLength p` is `E(p.length)`.
The length is computed from actual edges. For composable paths `p` and `q`,

\[
E(|p\circ q|)=\operatorname{f2f}^{|q|}(E(|p|)).
\]

This is the finite repeated-application identity described in
`L3_ordinatics.hm:163–167`. The same observation is preserved by `TraceExpr`
expansion and sequencing. The 13 new finite construction and observation
theorems depend only on the relevant existing parameters `Form`, `f2f`,
`ground`, and, for preserving paths, `Congruent`. They add no logical axiom.

This does not yet identify the observation with opaque L2 `pathLength` or L3
`ordinalApply`, nor with Ordinatics' ordinal value type. Those correspondences
need separate proofs. The definitions involving abstract `f2f` are
noncomputable; they do not supply an executable native arithmetic evaluator.

## Finite-orbit arithmetic needs no new compatibility assumption

Define `FiniteNumeralEq m n` by `E(m) = E(n)`. Equal representations always
act equally on starting forms in the finite ground orbit:

\[
E(m)=E(n)\;\Longrightarrow\;
\operatorname{f2f}^{m}(E(k))=\operatorname{f2f}^{n}(E(k)).
\]

Iterates of the same function commute, so both sides can be written as
`f2f^k(E(m))` and `f2f^k(E(n))`. The checked
`finiteNumeralEq_action_on_finite_orbit` formalizes this argument, and
`finiteNumeralEq_add` and `finiteNumeralEq_mul` prove that equality of both
input representations implies equality of the representations of their sums
and products. Finite addition and multiplication therefore descend to
represented values unconditionally. Every witnessed finite-orbit Form also has
a natural-number representative. Under an explicit `FiniteOrbitInjective`
premise, the checked encode/decode laws form a two-sided correspondence and
equal numeral Forms act identically on every starting Form. The current clauses
do not prove that premise. Without it, numeral injectivity and action on all
Forms do not follow. Even with it, agreement with `ordinalApply` still requires
a separate bridge theorem.

## Application to every Form is a stronger obligation

An exact action depending only on the numeral form and satisfying
`A(E(n), x) = f2f^n(x)` for every Form `x` requires

\[
E(n)=E(m)\;\Longrightarrow\;
\forall x\;\operatorname{f2f}^{n}(x)=\operatorname{f2f}^{m}(x).
\]

`FiniteActionCompatible` states this obligation. In
`lean4/Hypermath/FiniteAction.lean`, `finiteActionCompatible_iff_exists_exact`
proves that it is equivalent to existence of such an exact action. The forward
construction, `hostFiniteAction`, uses classical choice of a representative
and defaults to identity outside the finite ground orbit. Its agreement is
conditional on compatibility. This is a noncomputable construction in Lean's
host foundations; it adds no native law and does not identify the action with
the existing `ordinalApply` parameter.

For action agreement through an explicitly supplied relation, the generic
`agreement_implies_relation_compatible` proves necessity of the corresponding
representative-independence condition when symmetry and transitivity are
provided. Those properties are premises of that result, not assumed facts
about native `Congruent`. The input condition still concerns exact equality
of numeral Forms; identifying merely congruent numeral inputs would require
a further substitution contract.

The source proposes zero and one application at congruence level in
`L3_ordinatics.hm:130–146`. Its successor statement also uses congruence,
while step 3 at line 154 strengthens the claim to `=`. The exact host-action
criterion makes that stronger reading explicit rather than treating the
relation levels as interchangeable. The ground-orbit addition identity at
lines 163–168 remains separate from application to every Form.

## Universal ground-spanning conflicts with the limit boundary

The source proposes `D[ground][y]` for every form (`L1_relations.hm:418–425`).
With the source's finite, congruence-preserving interpretation of `D`, the
current declared axioms refute that proposition:

1. At each `E(n)`, the trace-floor clause gives
   `Similar (E(n+1)) (E(n))`.
2. The syntax close and syntax/substance/semantics clauses give
   `Simulation (E(n)) (E(n))`.
3. `axLimitNotFinite` excludes `Simulation (E(n)) ordinalLimit`, so no `E(n)`
   equals `ordinalLimit`.
4. Any `DEntry ground ordinalLimit` would yield exactly that equality through
   `dEntryEndpointIteration`.

Lean checks `finiteApplyLimitExcluded`, `ordinalLimitNotInD`, and
`notGroundSpanningClaim` without admissions. Their dependencies explicitly
include the source logical clauses used above. They are distinct from the
parameter-only construction proofs.

The false admitted theorem `dSpansGround` has been withdrawn. Its exact
universal proposition remains as `groundSpanningClaim`, with a checked
negation in L3. The native proposal is retained unchanged for comparison;
it is not silently rewritten as a narrower theorem. This withdrawal records
a refuted claim, not a proof of it.

## An interpretation of all declared logical clauses

`FullAxiomModel.lean` checks an interpretation of all 38 logical axiom clauses,
with complete clause-type correspondence checked against the declaration
policy. Forms are pairs of a natural number and a Boolean, application advances
the natural coordinate, and ground and limit lie on different successor chains.
Similarity is universal; congruence and simulation are equality.

The model also instantiates the actual finite closure and finite `D`
definitions. Its finite numerals are injective and its limit is unreachable
from ground through `D`. Its `full_axioms_hold` theorem has only Lean's standard
logical dependencies: propositional extensionality, classical choice, and the
quotient equality principle. It has no custom axiom or admitted proof.

This interpretation exposes two specification gaps. `axLimitIsLimit` is only
an implication about common upper bounds; it holds here because none exists.
`axLimitDerives` only constrains opaque endpoint projections, so a path object
can satisfy it without carrying an infinite chain or its finite prefixes.
The model does not satisfy those stronger intended meanings. It demonstrates
compatibility of the actual declared clauses relative to Lean's foundations,
not consistency or adequacy of the complete intended Hypermath system.

## A six-form countermodel to uniform finite application

`lean4/FiniteActionCountermodel.lean` separately checks all 38 current logical
clauses. Its six Forms have application chains
`a0 -> a1 -> a2 -> a1` and `b0 -> b1 -> b2 -> b0`, with ground `a0`.
Similarity is universal, Simulation is literal equality, and Congruent is
equality of four explicit classes, hence an equivalence relation.

Here `E(1) = E(3) = a1`, but one and three applications to `b0` produce `b1`
and `b0`, which are not even congruent. The model therefore refutes both
the exact and congruence-valued compatibility conditions for actions on all
Forms, and proves that neither kind of action exists in this interpretation.
It leaves the unconditional finite-orbit addition and multiplication results
intact.

The same model satisfies the exact proposition currently exported as
`selfDerivation` while all of those global arithmetic bridges fail. The current
self-derivation theorem is therefore a structural closure result, not an
arithmetic interpretation theorem. Typed reification, transfinite generation,
and semantic preservation remain separate proof obligations.

The model also refutes each former admitted computation statement. Their
exact propositions, including the path-length operand order, are retained as
definitions in `L3Ordinatics.lean`:

| Former admitted theorem | Retained proposal |
| --- | --- |
| `ordinalZeroIdentity` | `ordinalZeroIdentityClaim` |
| `ordinalSuccApplies` | `ordinalSuccAppliesClaim` |
| `pathLengthArithmetic` | `pathLengthArithmeticClaim` |

This establishes non-entailment from the declared clauses, not impossibility
of every stronger intended theory. In particular, the countermodel does not
encode the unformalized native requirement that all Forms arise from the
ground (`L0_ground.hm:49–64`), or a coherent transfinite generation mechanism.
Neither the declarations nor the model supplies that missing correspondence.

The current translation has **16 admissions and 67 declared assumptions**
(29 source parameters and 38 logical clauses). The latest three removed
admissions were withdrawn after these counterexamples; they were not proved.
The audit binds 35 proved production milestone declarations, including eleven
finite-orbit/action results. The classical existence results disclose their Lean
foundation dependencies; no new native axiom was added.

## Information that recursive reuse must retain

`Observation.endpoints_eq_of_step` proves that an observation invariant on every
edge remains invariant across a finite path. Two further theorems establish
that no function of endpoints alone can recover unequal lengths of two paths
with those same endpoints. The concrete check uses an empty path and a two-step
closed path, with lengths zero and two; retaining the paths retains both values.
Reusing the closed path twice preserves its computed length four.

The original 13 observation construction/check reports have no axiom dependencies. This
is an explicit obstruction to forgetting path information, not an impossibility
claim about fractal representations that retain it. It motivates the intended
retention of formation history in a reusable atom.

The observation module now also proves decoder factorization and uniqueness,
preservation under every finite sequence of encoding-compatible reuse
operations, and the necessity of injectivity when all equality queries are
observed. Its 24 reports contain 22 axiom-free results and two explicit uses of
classical choice for decoder existence. These are host-level results with stated
premises, not a constructed native rule checker.

Specializing to the existing native numerals gives
`finiteNumeralEqualityExact_iff_injective`. In the six-form model, equality of
`E(1)` and `E(3)` prevents a record-only decoder from correctly answering both
"is the original count 1?" queries. This obstruction holds even though finite
addition and multiplication respect equality of represented values. The native
arithmetic interpretation therefore needs more than those operation laws.

An observation that treats congruent forms as the same numeral cannot also
count each congruence-preserving edge as a change of numeral. Path observations
and vertex observations therefore need an explicit relationship. The uniform
action countermodel adds a second boundary: forgetting an iteration witness
can prevent a numeral Form from determining its action on other Forms.

These obligations preserve the intended full arithmetic objective. Finite
closure alone establishes neither arithmetic soundness nor completeness, and
the self-representation and effectiveness obligations in
[the governing research target](FRACTAL_COMPLETENESS.md) remain open.

## Checking the result

The [bounded audit](../verification.md) runs the library build, declaration
report, prefix countermodels, finite traces, observation checks, full axiom
model, and the required `finite_action` countermodel process. Its policy binds
definition bodies, theorem statements, exact per-theorem
dependencies, and probe source bytes. Missing or failed probes invalidate an
execution report and its required Verifier replay. The overall mathematical
gate remains unsatisfied while the remaining admissions and bridges are open.
