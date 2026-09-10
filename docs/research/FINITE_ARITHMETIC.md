# Finite closure, arithmetic observations, and a refuted claim

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
it is not silently rewritten as a narrower theorem. The current translation
has **19 admissions and 67 declared assumptions** (29 parameters and 38 logical
clauses). This admission decrease records withdrawal of a refuted claim,
not a proof of it.

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

## Information that recursive reuse must retain

`Observation.endpoints_eq_of_step` proves that an observation invariant on every
edge remains invariant across a finite path. Two further theorems establish
that no function of endpoints alone can recover unequal lengths of two paths
with those same endpoints. The concrete check uses an empty path and a two-step
closed path, with lengths zero and two; retaining the paths retains both values.
Reusing the closed path twice preserves its computed length four.

All 13 observation construction/check reports have no axiom dependencies. This
is an explicit obstruction to forgetting path information, not an impossibility
claim about fractal representations that retain it. It motivates the intended
retention of formation history in a reusable atom.

The next native-operation obligation is precise. An exact action depending only
on the numeral form and satisfying `A(E(n), x) = f2f^n(x)` requires

\[
E(n)=E(m)\;\Longrightarrow\;
\forall x\;\operatorname{f2f}^{n}(x)=\operatorname{f2f}^{m}(x).
\]

A congruence-valued action additionally needs explicit relation and representative
independence laws; congruence is currently an abstract relation. Likewise, an
observation that treats congruent forms as the same numeral cannot also count
each congruence-preserving edge as a change of numeral. Path observations and
vertex observations therefore need an explicit relationship.

These obligations preserve the intended full arithmetic objective. Finite
closure alone establishes neither arithmetic soundness nor completeness, and
the self-representation and effectiveness obligations in
[the governing research target](FRACTAL_COMPLETENESS.md) remain open.

## Checking the result

The [bounded audit](../verification.md) runs the library build, declaration
report, prefix countermodels, finite traces, observation checks, and full axiom
model. Its policy binds definition bodies, theorem statements, exact per-theorem
dependencies, and probe source bytes. Missing or failed probes invalidate an
execution report and its required Verifier replay. The overall mathematical
gate remains unsatisfied while the remaining admissions and bridges are open.
