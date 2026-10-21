# Eight admissions, all eight classified, and the structure behind them

The Lean layer stack carries eight admitted `sorry` obligations. Until now the
prose beside them said "FORM proof sketch" or "pending mechanization", which
reads as *unfinished work*. For most of them that reading was wrong. They are
not unfinished; they are underivable, and no amount of further mechanization
will close them. This note records which is which, with the machine-checked
witness for each.

The method is the same one already used for the self-derivation cycle in
[CYCLE_BOUNDARY.md](CYCLE_BOUNDARY.md): exhibit two models of the declared
clauses that disagree about the statement. A statement true in one model of the
clauses and false in another is independent of them. Independence is a fact
about the current declarations, not a claim that no source-adequate realization
could settle the statement.

## The clause sets

Two structures enumerate the declarations, and every witness below instantiates
one of them.

| Structure | Where | Clauses | Scope |
| --- | --- | --- | --- |
| `PrefixAxioms` | `lean4/Countermodels.lean` | 24 | L0 and L1 |
| `FullAxioms` | `lean4/FullAxiomModel.lean` | 44 | L0 through L3 |
| `FullAxiomsWith cp` | `lean4/FullAxiomModel.lean` | 44 | as above, with `congruentPath` left open |
| `PreClosureAxiomsWith cp` | `lean4/FullAxiomModel.lean` | 39 | the 39 that precede the closing clauses |
| `FullAxioms` | `lean4/Hypermath/TransportCountermodel.lean` | 39 | the same 39, over one model's definitions |

`lean4/Hypermath/` declares 66 axioms: 26 source parameters and 40 logical
axiom declarations. The clause count is larger than the declaration count
because the single `ordinatics` interface declaration projects to five ordinal
clauses, which the structures list separately. `tests/test_declared_counts.py`
measures all of this and fails if the prose and the sources disagree.

## Status of each admission

| Admission | Status | Witness |
| --- | --- | --- |
| `L0Ground.derivesIsDirectional_FRAME` | independent | `directionality_independent` |
| `L0Ground.definitionOfGround` | closed one layer later | `definitionOfGround_L1` |
| `L1Relations.similarReflexive` | independent | `IrreflexiveSimilar.similar_reflexivity_independent` |
| `L1Relations.similarSymmetric` | independent | `IrreflexiveSimilar.similar_symmetry_independent` |
| `L1Relations.derivesIsDirectional` | independent | the same declaration as the L0 entry |
| `L2Operations.plusAndAdditionallyAreDistinct` | independent | `distinct_operations_independent` |
| `L2Operations.orbitReflexionQuotient` | underivable | `IrreflexiveSimilar.column_quotient_claim_fails` |
| `L3Ordinatics.congruentPathInternals` | independent | `congruentPath_symmetry_independent` |

Two of those statuses have a second, sharper witness. `congruentPathInternals`
is independent even after `congruentPath` is *defined* the way the source
intends, because the definition inherits its symmetry from `=~` and `=~` is not
symmetric either: `AsymmetricCongruent.congruent_symmetry_independent`.

Every `independent` row names a single declaration, and that is a change made on
2026-09-21 rather than a formatting preference. Four of these rows named the
refuting model alone --- `similar_reflexive_claim_fails` is a countermodel, and
a countermodel is half of an independence result. Two named both halves with a
slash between them, which leaves the conjunction to the reader and to this
table. Nothing checked that the reader did it, or that the two halves still
concerned the same statement, or that both models still existed. So the four
pairings now exist as declarations of the shape

```
(ModelA.Axioms ∧ P_A) ∧ (ModelB.Axioms ∧ ¬ P_B)
```

in `lean4/Countermodels.lean` and `lean4/FullAxiomModel.lean`, and the Witness
column names them. Two of the four moved up in strength while being written:
`directionality_independent` and `distinct_operations_independent` pair against
`HypermathTransportCountermodel`, which satisfies all **39** of the pre-closure clauses, so both
statements are now independent of the full clause set rather than of the 24
clauses of the L0/L1 prefix.

The slash notation is what made the defect invisible. `A / B` reads as a pair
when both sides are there and reads as a citation when only one is, and the
table had both spellings in adjacent rows without distinguishing them. A
declaration cannot be half-written in that way: `similar_reflexivity_independent`
either elaborates or it does not.

## Directionality of `Derives`

`HypermathCountermodel` interprets `Congruent` as `True`, which makes `Derives`
total and therefore symmetric, while satisfying every L0 and L1 clause:
`directionality_claim_fails`. `HypermathFullAxiomModel` interprets `Derives` as
reachability along a chain whose first coordinate only increases, satisfying all
44 clauses with the statement true: `directionality_holds`. Independent.

The pairing is `HypermathFullAxiomModel.directionality_independent`, and it is
stated against `HypermathTransportCountermodel` rather than against the Bool
model above, for a reason that is worth recording because it constrains where
every pairing in this file can live. `lean4/lakefile.toml` declares one
`lean_lib Hypermath` rooted at `lean4/Hypermath.lean`, so only modules under
`lean4/Hypermath/` are compiled to oleans. A top-level file in `lean4/` cannot
import another top-level file. `HypermathCountermodel` lives in one of those
top-level files, so no third file can mention both it and
`HypermathFullAxiomModel`; the transport countermodel is a library module and
can be imported anywhere. The upgrade from 24 clauses to 39 was forced by the
build graph and is an improvement anyway.

The sketch that formerly stood at `L1Relations` §V concluded from "`ax-box`
returns only at `~~`, and no axiom upgrades that return to `=~`" that no return
exists. Failing to prove a return is not proving there is none, and the step
that would close the gap reads the filtration backwards --- from
`¬ Simulation x y` to `¬ Congruent x y`. `reverse_filtration_fails` proves that
reading is unavailable.

## Reflexivity and symmetry of `~~`

The new `HypermathCountermodel.IrreflexiveSimilar` model satisfies all 24 L0 and
L1 clauses with `Similar` neither reflexive nor symmetric.

The obstruction is structural and short to state. Every clause that asserts
similarity asserts it *of an image*: `ax-sim` about `f2f x`, `ax-box` about
`f2f (f2f x)`, `trace-levels` about `f2f x`. `ax-ground-self` is the one
exception and it names ground only. So put a second chain beside the ground
chain and deny similarity at that chain's head. A head is nobody's image, so no
clause reaches it. The model does exactly this, with forms `(n, b)` and the
isolated head `(0, true)`.

Three consequences fall out of the same model:

* `similar_reflexive_claim_fails` --- `~~` is not reflexive, so the L1
  graduation obligation NC-1 rests on an assumption the development never
  makes;
* `similar_symmetric_claim_fails` --- `~~` is not symmetric, so the informal
  reading "non-empty overlap in continuation capacity", which is symmetric, is
  not binding on the Lean parameter;

The first two are paired against the Bool model, where `Similar` is `True` and
therefore both reflexive and symmetric, by `similar_reflexivity_independent` and
`similar_symmetry_independent`. Both cost `propext` and `Quot.sound` and
nothing else. The third is not paired, and should not be: `column_quotient_claim_fails`
quantifies over **every** relation `R`, so it is not a statement some other
model could satisfy --- the paragraph below says why, and the difference
between a claim that is independent and a claim that is refutable outright is
exactly the difference between having a pairing and not needing one.
* `column_quotient_claim_fails` --- for **every** relation `R`, coincidence of
  `R`-columns does not give `~~`. Taking `x = y` makes the hypothesis trivial,
  so any statement of that shape entails reflexivity. No argument about `D`'s
  finiteness can rescue `orbitReflexionQuotient`; the obstruction is not size.

## The whole grid: three relations, three properties

Settling `~~` reflexivity, `~~` symmetry and `=~` symmetry one at a time invited
the obvious question of how many more such gaps there are, and the question is
finite: the filtration has three relations and there are three basic properties
of a relation. Nine cells. All nine are independent of the 24 clauses. What
matters is that they are not nine findings.

| | reflexivity | symmetry | transitivity |
| --- | --- | --- | --- |
| `~~` | `similar_reflexivity_independent` | `similar_symmetry_independent` | `similar_transitivity_independent` |
| `=~` | `congruent_reflexivity_independent` | `congruent_symmetry_independent` | `congruent_transitivity_independent` |
| `≡` | `simulation_reflexivity_independent` | `simulation_symmetry_independent` | `simulation_transitivity_independent` |

The cells held the word `independent` until 2026-09-21 and four declarations
stood behind the nine of them. That is the same defect as the admission table
above in its least visible form, because here the five unbacked cells were not
merely asserted --- they follow from the freedom theorems below, which settle
whole rows at once and are stronger than any cell. The reading was sound. What
was missing was the object: a row that is free and a cell that is independent
are different claims, and a table that writes one word in all nine cells makes
them look like nine of the same thing. Now they are.

The nine names are `<relation>_<property>_independent` over `similar`,
`congruent`, `simulation` and `reflexivity`, `symmetry`, `transitivity`, and
`test_the_nine_cell_grid_is_nine_pairings` builds those names itself rather than
reading them from a list, so the convention is what is checked and not a copy of
it. Five of the nine are short --- the satisfying half of every cell is the Bool
model at the head of `lean4/Countermodels.lean`, where `~~` and `=~` are `True`
and `≡` is equality, so all nine properties hold there at once. Their length is
not the point; their existence is.

The reflexivity column collapses to one fact, and it is not a fact about
relations. `Hypermath.reflexivityLevelsCoincide` proves from the clauses that
`x =~ x` and `x ≡ x` hold of exactly the same Forms, and
`Hypermath.reflexivityIsGroundReachability` proves both hold exactly when x is
`~~` to some iterate of ground. The route is short: the triangle axioms make
`HMSyntax`, `Substance` and `Semantics` interderivable, and the three opaque
closes read those three predicates as reachability, `=~`-reflexivity and
`≡`-reflexivity respectively. Globally,
`Hypermath.globalCongruentReflexivityIsCofinality` states the consequence ---
`=~` is reflexive on all of `Form` exactly when the ground chain is `~~`-cofinal
in `Form`.

So "is `=~` reflexive?" was never a question about `=~`. It asks whether forming
from ground reaches everything, which is a statement about the shape of the
universe, and `IrreflexiveSimilar` satisfies every clause while failing it:
`congruent_reflexivity_fails_with_unreached_form` exhibits the model with a Form
the chain never reaches, both upper reflexivities failing together exactly as
the coincidence theorem requires. This also explains something §IV.b had only
observed. It proves reflexivity at ground twice, once at each level, and remarks
both times that it does not generalise. It could not: the two proofs were the
same proof, and what they rest on is `axGroundSubstanceAx` and
`axGroundSemanticsAx` asserting reachability of ground under two different
names.

The symmetry and transitivity columns collapse into two freedom theorems, and
this is the sharper result of the two, because a freedom theorem settles cells
nobody has asked about yet.

`AsymmetricCongruent.prefixAxioms_hold` takes an **arbitrary** relation `E` and
satisfies all 24 clauses with `=~` read as equality-or-`E`. The proof never
mentions `E`: every field either ignores `Congruent` or uses `Or.inl`, the
inclusion of equality. Three clauses constrain `=~` --- `filtrationSimCong` and
the third conjunct of `traceLevels` bound it below by `≡`, `filtrationCongSim`
bounds it above by `~~`, and `closeSubstanceOpaque` fixes its diagonal --- and
reading `≡` as equality and `~~` as everything makes all three vacuous. So the
clauses say of `=~` only that it contains equality, and **no** property of `=~`
beyond that is a consequence of them. Symmetry
(`congruent_symmetry_claim_fails`) and transitivity
(`congruent_transitivity_claim_fails`) are two instances;
`congruent_is_free_above_equality` is the general statement.

One level up the answer is not "no condition", and the difference is the
interesting part. `FreeSimulation.prefixAxioms_hold` satisfies all 24 clauses
for every `E` subject to one hypothesis: `E` relates no image to ground. That
side condition is not an artefact of the construction. It is forced in every
model, because `Hypermath.axDiffInRelationLanguage` derives `¬ (f2f x ≡ ground)`
from `ax-diff` and `closeStructDistinct`. Sufficiency and necessity together
make it a characterisation:

> The clauses constrain `≡` in exactly one way --- it relates no image to
> ground --- and in no other way whatsoever.

That is a better thing to know than a list of missing properties, and it was not
reachable by asking about properties one at a time.
`simulation_symmetry_claim_fails` and `simulation_transitivity_claim_fails`
fall out as instances, as does every other cell of that row.

`~~` admits no such theorem in that shape, and the reason is the finding.
`traceLevels` forces `f2f x ~~ x` outright, `filtrationCongSim` forces `~~` to
contain `=~`, and the reflexivity result above ties `=~`'s diagonal to
reachability --- so the bottom level is where the clauses actually say
something, and the two levels above it are nearly free. The filtration is
usually read as three levels of increasing strength. As a set of assumptions it
is the reverse: the content is concentrated at the bottom, and `≡` and `=~` are
almost entirely undetermined.

That shape is the limitation, not the answer. Each freedom theorem holds two
relations fixed to speak about the third, which is why `~~` --- the thing the
others are held fixed *against* --- gets none. The next section drops the fixed
background, and with all three free the question has an answer that is not a
freedom theorem at all.

## All three at once: an iff, not a third construction

Parameterising `~~`, `=~` and `≡` together removes the asymmetry from the
method rather than from the subject, and what comes back is a characterisation.
`HypermathCountermodel.FreeFiltration.prefixAxioms_iff_conditions` proves, for
an **arbitrary** carrier `Form` with a ground element and a forming map, and
**arbitrary** relations `S`, `C`, `E` on it:

> `PrefixAxioms S C E ↔ Conditions S C E`

Eight conditions, where `Reach S x` abbreviates `∃ n, S (Nat.repeat f2f n
ground) x`:

| | condition | constrains |
| --- | --- | --- |
| 1 | `∀ x y, E x y → C x y` | the `≡`/`=~` coupling |
| 2 | `∀ x y, C x y → S x y` | the `=~`/`~~` coupling |
| 3 | `∀ x, S (f2f x) x` | `~~` |
| 4 | `∀ x, S (f2f x) ground` | `~~` |
| 5 | `∀ x, S (f2f (f2f x)) x` | `~~` |
| 6 | `∀ x, ¬ E (f2f x) ground` | `≡` |
| 7 | `∀ x, C x x ↔ Reach S x` | `=~`, via `~~` |
| 8 | `∀ x, E x x ↔ Reach S x` | `≡`, via `~~` |

Both halves are on the record. Sufficiency is the countermodel file;
necessity is `Hypermath.filtrationConditionsHold`, proved in `L1Relations`
§VI.a from the declared clauses, so the eight hold in every model of them and
any triple satisfying the eight satisfies all 24 clauses. Neither direction
uses an axiom: `#print axioms` reports none for `prefixAxioms_of_conditions`,
`conditions_of_prefixAxioms` or the iff.

It can be an iff rather than a containment because seven of the 24 clauses are
not assumptions about the filtration at all. `closeSyntaxOpaque`,
`closeSubstanceOpaque`, `closeSemanticsOpaque`, `closeFormClosureOpaque`,
`closeDerivesOpaque`, `closeDischargeOpaque` and `closeDefinitionOpaque` read
`HMSyntax`, `Substance`, `Semantics`, `FormClosure`, `Derives`, `Discharge` and
`Definition` off the three relations. Define those seven predicates *as* what
the closes say they are and all seven fields become `Iff.rfl`, so nothing is
lost in passing to `Conditions` --- every clause either survives as a condition
or is a definition restated.

### The carrier has to be free too

The first version of this fixed the carrier to the ground chain, which is where
every other prefix model lives, and that was wrong in a way worth recording
because the statement it produced was still true.

On the chain every Form *is* an iterate of ground, so condition 3 --- `∀ x, S
(f2f x) x` --- makes `Reach S x` hold for every x on its own, by taking the
iterate to be `f2f x`. `reach_is_total_on_the_chain` proves it. Conditions 7
and 8 then degenerate: "the diagonal is exactly the reached part" becomes "the
relation is reflexive", and the reachability content vanishes. That content is
not incidental. It is the entire reflexivity column of the grid --- the thing
`reflexivityIsGroundReachability` identifies and `IrreflexiveSimilar` exhibits
--- so a chain-only characterisation names eight conditions of which two say
less than they appear to, and cannot state the one result the section above
calls the collapse of a whole column.

Leaving the carrier open costs nothing. The proof of the iff never mentions the
carrier: it goes through unchanged, and `#print axioms` still reports none. What
it buys is `ext_conditions`, which instantiates the eight at the chain with one
extra Form adjoined whose image is itself, so the chain never produces it. Take
`~~` to relate everything except into the adjoined point from outside, and `=~`
and `≡` to be equality restricted to the chain, and all eight conditions hold.
`congruent_reflexivity_needs_an_unreached_point` reads off the consequence:

> all 24 clauses, `~~` reflexive, `=~` not reflexive.

`IrreflexiveSimilar` already refuted `=~`-reflexivity, but `~~` is irreflexive
there too, which leaves open the reading that a badly behaved bottom level is
doing the work. It is not. One unreached Form is the whole requirement;
conditions 7 and 8 withhold the diagonal there and nothing else changes.

### What the list says by omission

Five of the eight are about `~~` alone. One is about `≡`. The remaining two are
the couplings. **Off its own diagonal, neither upper relation is constrained by
anything except the inclusion into the one below it.** That is the same finding
as the previous section, now stated once instead of assembled from a row and a
column, and it is where the two freedom theorems come from rather than a
summary of them. `total_similar_leaves_exactly_three_conditions` makes the
derivation explicit: over the chain, set `~~` to the total relation, conditions
3, 4 and 5 go away, 7 and 8 collapse to plain reflexivity, and what is left is
exactly

> `≡ ⊆ =~`, `≡` reflexive, and `≡` denies every image at ground

which is `AsymmetricCongruent` and `FreeSimulation` read off a single
statement. The nine cells of the grid are then corollaries of one theorem, not
nine findings and not three.

That collapse was stated over the chain, and the reason given for the two
diagonal conditions turning into plain reflexivity was that the carrier is the
chain. It is not. `total_similar_makes_reach_total` says the ground chain
reaches every Form as soon as `~~` is total, on any carrier, from no condition
at all --- `Reach` asks for an iterate of ground that the relation connects to
`x`, and a total relation connects the first one. So the corner is a statement
about an arbitrary carrier, like the other one, and it is now stated that way.

Cofinality is reached twice in this file by routes with nothing in common.
`reach_is_total_on_the_chain` gets it from the carrier, and needs the third
condition to do it. `total_similar_makes_reach_total` gets it from the relation,
and needs nothing. Reading the first as the reason for the second is what put
the chain in the statement of a theorem that never used it, and it is also why
the two corners look asymmetric for the wrong reason: **the upper corner is free
of the carrier because a total `~~` empties `Reach`, and the lower corner is not
because equality at the top makes `Reach` exactly cofinality.** That is the same
sentence as the count --- three against six --- said about the carrier instead
of about the conditions.

That line used to read "both reflexive", and the statement it summarised
carried reflexivity of `=~` as a fourth conjunct. Nothing was false. The fourth
conjunct is `congruent_reflexivity_is_not_a_fourth_condition` --- `=~` is
reflexive because `≡` is and `≡` is contained in it --- so the iff held with it
and holds without it, and the English joined the two reflexivities into one
phrase, which is how a name saying three sat above a statement saying four for
as long as it did. **Two conditions spoken as one is not a smaller claim; it is
an uncounted one.** The conditions are now the fields of
`TotalSimilarConditions`, a structure rather than a conjunction, so a fifth
cannot be added to the right of the iff without being named and counted.

**Each of the three is needed.** `two_hold_without_simulationIntoCongruent`
takes `≡` to be equality with the single extra pair from ground to the first
rung and `=~` to be equality: reflexive and denying, not contained.
`two_hold_without_simulationReflexive` takes `≡` empty, which is contained in
everything and denies everything and is reflexive nowhere.
`two_hold_without_imageNotSimulatingGround` takes `≡` to relate everything into
ground. So three is a measurement here for the same reason six is at the other
corner, and the comparison between the two corners is between counts and not
between two ways of writing a list.

### The other corner: what the clauses say about `~~`

Every result above holds `~~` fixed. The two freedom theorems fix two relations
to answer about the third, and the collapse just described fixes `~~` to the
total relation to answer about the two above it. So the relation the others are
measured against is the one nothing here was about, and "what do the 24 clauses
say about `~~`?" had no answer in this file --- not an open question, an unasked
one.

Take the upper two relations to their minimum instead. `=~` and `≡` must contain
equality and, by the freedom theorems, may be nothing more, so set both to
equality. Conditions 1, 2 and 6 become trivial or a fact about forming, and
conditions 7 and 8 read `True ↔ Reach`, which forces the ground chain to reach
everything. `minimal_upper_relations_leave_five_conditions_on_similar` is the
iff, on an arbitrary carrier and with no axioms:

> `~~` is reflexive, `f2f x ~~ x`, `f2f x ~~ ground`, `f2f (f2f x) ~~ x`, the
> ground chain is `~~`-cofinal --- and forming never returns to ground.

Five conditions on `~~` and one on forming. Compare the other corner, which
leaves three: an inclusion, a reflexivity and a denial. The asymmetry is the
finding: **the upper two relations are free above equality and `~~` is not free
at all.** The filtration reads as though its content were at the top, where the
interesting relations live; the content is at the bottom, and the two upper
levels are very nearly undetermined.

That the chain must reach everything is not a new fact ---
`Hypermath.globalCongruentReflexivityIsCofinality` proves the same implication
from the clause side. What is new is where it sits. It is not a consequence of
the clauses about `=~`; it is what the characterization becomes when the upper
relations are given no content of their own, which is why it survives having
both of them trivialised.

**Each of the six is needed.** An iff says what the conditions are and says
nothing about how many facts they are: four of the six could have followed from
the other two and the statement would read exactly the same, which would make
the comparison just drawn --- five against three --- an artefact of how the list
was written. That is not hypothetical. It is exactly what had happened at the
other corner, where a derivable conjunct sat in the statement for as long as
the count went unmeasured. So each is dropped in turn, and the six models are
`five_hold_without_similarReflexive`, `five_hold_without_imageSimilar`,
`five_hold_without_imageSimilarToGround`,
`five_hold_without_doubleImageSimilar`, `five_hold_without_chainIsCofinal` and
`five_hold_without_formingAvoidsGround`.

Four of them are relations on the chain chosen to miss one condition: strictly
above, equal-or-at-ground-or-two-up, within two steps, one-step-or-at-ground.
The other two need the carrier. Cofinality fails on the adjoined carrier, since
forming fixes the adjoined point and no iterate of ground produces it, and on
the chain alone the question cannot be asked --- `reach_is_total_on_the_chain`
gets cofinality out of the third condition. Forming returning to ground needs a
carrier where it can, which is the one-point carrier, where forming is the
identity. So two of the six conditions are invisible on the chain, and the
carrier had to be open for a second reason that was not among the reasons for
opening it.

### What the eight forbid

Everything above asks what the conditions allow. Freedom at the top, a count at
each corner, a model for each cell of the grid: every one of them exhibits
relations, and a file of exhibited relations reads as though the answer to "what
do the clauses rule out?" were "nothing much". It is not.

**Ground is not an image.** `ground_is_not_an_image` takes any model of the
eight and any carrier. If forming sent anything to ground, the third condition
would put ground under `~~` with itself, so the ground chain would reach ground
at its own first iterate, so the eighth condition would give `≡` on the diagonal
there --- and the sixth denies exactly that. Three conditions, no carrier, no
other assumption. The sixth condition is stated about a relation --- no image is
`≡` to ground --- and this turns it into a statement about identity: no image
*is* ground. `ground_is_not_a_fixed_point` is the case that gets used below.

That theorem was in the file already. It was proved a thousand lines further
down, inside the transfinite section, as the lemma that makes `axLimitNotFinite`
bite, with a docstring observing that the prefix clauses constrain the carrier
too --- an answer to this section's question, filed where this section could not
find it, and reproved here from scratch by someone who did not know. Lean caught
the collision because both proofs picked the same name. Under two names nothing
in the repository would have: the file would carry one fact as two theorems,
each with a docstring claiming it. The theorem has been moved to where its
subject is, and
`test_no_proposition_is_proved_twice_for_the_same_price` is the general form of
the rule the vocabulary pair had for itself --- two theorems may state one
proposition, and then their proofs must differ in what they spend.

**So `~~` is never equality.** `similar_is_never_equality`. Equality makes the
second condition say that forming is the identity, which fixes ground. The two
relations above `~~` may both be equality --- that is the lower corner, and it
is consistent --- and the relation below them may not be. So the sentence above
understates its own finding in one direction: `~~` is not merely constrained
where the others are free, it is kept off the bottom of the lattice of relations
altogether. **The clauses require the filtration to identify something.**

**And `~~` is never `≡`.** `similarity_is_not_contained_in_simulation`: the
third condition puts every image at ground under `~~`, the sixth keeps every
image off ground under `≡`, so the composite inclusion `≡ ⊆ =~ ⊆ ~~` is strict
in every model of the eight. No model is needed for that and none is used.
`the_three_relations_are_never_all_one` is the immediate corollary, and it is
the one worth stating: the clause set cannot be read as one relation under three
spellings.

Which of the two links carries the strictness is open.
`neither_inclusion_is_forced_to_be_strict` pairs a model where `=~` is `~~`
outright --- the chain with both total and `≡` equality, which is the upper
corner read backwards --- with `ext_conditions`, where `=~` is `≡` instead. So
three relations is three by necessity as a whole and by necessity at neither
link, which is a different and sharper statement than any count of clauses.


**Both ends of the lattice, for all three relations.** `similar_is_never_equality`
keeps `~~` off the bottom and says nothing about the top, and the same question
is open for the other two. Six settings; four hold.

| | at equality | total |
|---|---|---|
| `~~` | impossible | the upper corner |
| `=~` | the two-Form model | the upper corner's model |
| `≡` | the lower corner | impossible |

`simulation_is_never_total` is the new corner and the cheapest impossibility in
the file: the sixth condition denies `≡` between an image and the ground, and a
total relation denies nothing. No carrier, no second condition.
`total_congruent_forces_total_similar` fills the one cell that could have been
its own case --- a total `=~` drags `~~` up with it by the fifth condition --- so
the middle relation reaches the top only inside the upper corner.
`the_extremes_of_the_three_relations` states all six together.

The asymmetry is the finding, and it has one cause at each end. `~~` cannot be
smallest because `imageSimilar` makes it relate an image to something it is not.
`≡` cannot be largest because `imageNotSimulatingGround` makes it fail somewhere.
**The clause set requires the bottom relation to identify and the top relation to
distinguish**, and asks neither of the one in between, which is free at both
ends. That is a sharper reading of "the upper two relations are free above
equality and `~~` is not free at all": `=~` is free at both ends, `≡` is free
only downwards, and `~~` is free only upwards.

**And the carrier has a size.** Every result in the file before this one leaves
the carrier arbitrary and says nothing whatever about it. `ground_is_not_an_image`
is the first that does, because an image is a Form that is not ground, so the
eight have no one-point model at all --- `no_model_on_one_point`. Two points are
enough: `two_points_are_enough` puts `=~` and `≡` at equality, which the lower
corner allows, sends forming to the Form that is not ground, and lets `~~` relate
that image to everything. So `two_is_the_smallest_carrier`, and the smallest
model of the eight has exactly two Forms.

That corrects a claim one layer up. `the_limit_is_off_the_chain` used to call
`axLimitNotFinite` the first clause in the whole set that says anything about how
large the carrier must be. It is not: the prefix eight already demand a second
Form, and are satisfied by exactly two. What the limit clause demands is a point
off the chain, which is a different demand, not a larger one in the same
direction. Two sections both claimed a first because neither could see the other,
which is the same failure as the reproof, one level up in the prose.

So the limit clause's own demand is worth measuring the same way, and the answer
is one Form. `no_limit_on_two_points`: ground, its image and the limit are three
distinct Forms, because `ground_is_not_an_image` separates the first two and
`the_limit_is_off_the_chain` separates the limit from each of them at the chain's
zeroth and first positions. `ThreePointLimit` supplies the other half --- all
nineteen conditions on `Fin 3`, with forming constant at the image, the successor
the three-cycle, `~~` and `=~` total and `≡` equality --- so
`three_is_the_smallest_carrier_with_a_limit`.

**The transfinite layer does not demand an infinite carrier.** It is named for
the transfinite, its only model in this file is `Option Nat`, and both invite the
assumption. What `axLimitNotFinite` asks is that no *position* of the chain
simulate the limit, and a chain that stops moving has one position after its
first step. `spanned_carriers_admit_no_limit` is the nearest thing in the file to
the assumption and it says something weaker --- a carrier the chain *exhausts*
admits no limit --- which a constant forming satisfies on three points by not
exhausting them. Eight conditions cost two Forms, nineteen cost three, and the
eleven in between cost nothing: the operations and the composition never demand
a Form at all, the operations because their witnesses may all be ground and the
composition because it speaks of a carrier of paths instead.

**The paths are a second carrier and it has a size too.** The composition
conditions are the only ones that mention it, and two of the three are equations
that one path satisfies. The third is not: `unitalUpToCp` relates `comp p e` to
`p`, and on one path those are the same path, so `cp` holds between the unit and
itself where `someNonUnit` demands a path at which it does not ---
`no_compose_on_one_path`. Two paths suffice, with disjunction for composition and
`false` for the unit, which is the smallest monoid with a non-unit there is, so
`two_is_the_smallest_path_carrier`. `compose_conditions_are_always_available`
already said the layer excludes nothing; this says what it costs, which is one
path more than nothing.

So the whole clause set fits in three Forms and two paths, and neither number
can be reduced: `three_is_the_smallest_carrier_with_a_limit` now exhibits the
nineteen over `Fin 3` and `Bool` together. Every model in this file before it
used an infinite carrier for one or both, and none of them had to.

**Which layer is spending them is a separate question, and the counts mislead.**
The operations hold on one Form --- every witness they ask for may be the ground
and their one negative field is vacuous when `=~` is total ---
`operation_conditions_hold_on_one_point`. So do the transfinite conditions on
their own: ground and limit the same Form, forming and the successor the identity
on it, `~~` and `=~` total and `≡` empty, which satisfies
`limitNotSimulatedFinitely` with an empty relation instead of a large carrier
(`transfinite_conditions_hold_on_one_point`). The layer named for the transfinite
asks least of the carrier of the three. Only the prefix has no one-point model at
all, so every demand the clause set makes on size passes through the eight:
`only_the_prefix_demands_a_second_form`.

**And the third Form is demanded by neither layer alone.** The eight have a
two-Form model, the transfinite conditions have a one-Form model, and their
conjunction has no two-Form model --- `the_third_form_is_a_joint_demand`. This is
a second failed join, and it fails differently from the first.
`nineteen_is_not_fourteen_plus_five` fails because one side fixes relations the
other must then meet; this one fails on the carrier, where each side is
satisfiable at a size and the size at which both are satisfiable is larger than
either. An incidence table over symbols sees neither, and for the same reason
both times: `axLimitNotFinite` is a demand about a carrier and a table of symbols
cannot look at one.

**And "two Forms suffice" is a weaker sentence than the fact it reports.** What
a model still gets to choose at the smallest carrier had not been asked, and the
answer is: almost nothing. Forming is not among the choices.
`imageNotSimulatingGround` constrains forming by a denial and nothing else, and
at two Forms a denial of one value is a naming of the other, so every model of
the eight over two Forms has the same forming map ---
`forming_is_forced_at_two_points`. With forming constant one step lands on the
image of anything, so reachability is total, so both upper diagonals are total
by the two diagonal clauses (`both_diagonals_are_forced_at_two_points`), so
three of the four cells of `~~` follow
(`similar_is_forced_off_one_cell_at_two_points`). Counted,
`eight_cells_are_forced_at_two_points`: three cells of `~~`, two of `=~` and
three of `≡` hold or fail the same way in every model there is.

The remaining four are each free, and four models over those same two Forms
settle it: `two_points_are_enough` and `two_points_are_enough_with_total_similar`
differ at the ground-to-image cell of `~~`, that one and
`two_points_are_enough_with_total_congruent` differ at both off-diagonal cells
of `=~`, and `two_points_are_enough_with_maximal_simulation` differs from the
second at the ground-to-image cell of `≡`.
`the_eight_decide_forming_and_eight_of_twelve_cells` carries the forced half and
the four models together. At its smallest carrier the clause set is one model
wide in its operation and four cells wide in its relations.

**The rigidity belongs to the size, not to the clause set.**
`forming_is_not_forced_at_three_points` exhibits two models over three Forms
alike in ground and in all three relations and different in forming; the same
denial is doing the same work and there are now two values left, so it names
none. `two_points_determine_forming_and_three_do_not` pairs the sizes.
Minimality and rigidity coincide at the bottom and come apart at the very next
step, which is the general shape worth keeping: a clause set that constrains an
operation only negatively determines that operation exactly at the carrier where
one value survives the denial. Satisfiability at a size and freedom at that size
are different questions, and every earlier result in this file asked only the
first.

### The operation layer joins it: seven clauses, three conditions

The seven operation clauses are pure `~~`/`=~`. None mentions `≡`, so whatever
they add they add nothing about simulation, and everything the clause set says
about `≡` is already in the eight.

`FreeFiltration.operationAxioms_iff_conditions` states them over arbitrary `S`
and `C` on an arbitrary carrier and characterises them by three:

| # | condition | reading |
| --- | --- | --- |
| 9 | `∀ a b, ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab` | a congruent *pair* of common witnesses |
| 10 | `∀ a, ∃ c, S c a ∧ C c a` | one witness congruent to each Form |
| 11 | `∀ a b, ¬ C a b → ∃ c d, …∧ ¬ C c d` | incongruent witnesses for incongruent Forms |

Four of the seven clauses fall out of the first two --- that is
`commonWitnessesComeFromCommutativity` again, now as half of an iff --- and the
third is `axSeqAsymm`, whose antecedent nothing discharges. Neither direction
uses an axiom.

`prefixWithOperations_iff_conditions` composes the two: **31 of the 39 pre-closure clauses,
eleven conditions, arbitrary carrier, no axioms.** What is left outside are the
three path clauses, which §XIV opens separately and which
`prefixOperationsCompose_iff_conditions` below folds in, and the five transfinite
ones, which are projections of the single `ordinatics` instance and which
`all_thirty_nine_iff_nineteen_conditions` folds in after that.

### Eleven is not eight plus three

The statements compose. The freedoms do not.

`ext_conditions` satisfies the eight with one Form the chain never reaches, and
that model is what `congruent_reflexivity_needs_an_unreached_point` runs on. The
three operation conditions are **unsatisfiable** there, and
`operations_exclude_the_unreached_point` proves it. The argument is one step:
condition 10 at the unreached point needs some `c` similar to it and congruent
to it; nothing is similar to it but itself; and at anything unreached the
diagonal conditions withhold congruence. The witness would have to be the point,
and at the point congruence is exactly what is missing.

So adding the operation layer to the prefix constrains nothing new about `≡` and
still shrinks the model class. Everything in this note proved against 24 clauses
is a statement about the prefix, and says nothing on its own about the other
fifteen --- including the reflexivity witness above. **A freedom proved against
24 clauses has to be re-checked against 31.**

### `~~` may be a partial order

The other reading is a model that could not have been found by the earlier
method, because the earlier method never varied `~~`.
`similar_can_be_a_partial_order` takes `x ~~ y` to be `y ≤ x` --- *y is no more
formed than x* --- with `=~` and `≡` both equality, and verifies the eight
conditions. Forming climbs the order, which is conditions 3, 4 and 5;
reflexivity makes every Form reached, which is 7 and 8.

Every previous `~~` witness was either the total relation or the ad-hoc
irreflexive one, which left open the reasonable suspicion that the freedom
results were artefacts of a badly behaved bottom level. They are not. `~~` can
be reflexive, transitive and antisymmetric --- and still not total --- with
every clause satisfied and both upper relations as tight as they can possibly
be. Assuming the filtration is well behaved buys nothing back.

## Nothing is incongruent, and that settles the last admission

The row above that read "open, and blocked" for longest was
`plusAndAdditionallyAreDistinct`. Its proof applies `axSeqAsymm` to `f2f ground`
and `ground` and is left needing `¬ (f2f ground =~ ground)`, which the filtration
will not give: `ax-diff` denies `≡`, and `≡` implies `=~` rather than the
reverse. `HypermathCountermodel.reverse_filtration_fails` had established that
the backwards reading is unavailable across the 24 clauses, and there the matter
sat.

That was not enough to classify the admission, for a reason worth stating
because it recurs. The statement is existential over the pair `a b`; showing one
subgoal underivable leaves open that some other pair works. What settles it is a
model in which `=~` is **total**, since the statement's first conjunct demands
two Forms that are not congruent.

`HypermathTransportCountermodel` is that model, and it has been in the library
all along. It defines `Congruent` as `True`, certifies all 39 pre-closure clauses in
`full_axioms_hold`, and was built for an unrelated purpose --- a witnessed cycle
whose paths are not reproduced. Nobody had pointed it at this admission.
`no_incongruence_is_derivable` states the three facts together, and the middle
conjunct is the general form:

> The 39 pre-closure clauses have a model in which `=~` is the total relation. So they prove
> no instance of `¬ (x =~ y)` whatsoever.

The distinctness statement is one casualty of that, not a special case.
`HypermathFullAxiomModel.full_clauses_with_distinct_operations` supplies the
other half --- there `=~` is equality, so the statement is true --- and the
admission is independent, like five of the other seven.

This is the `=~` freedom theorem again, one clause set up. `AsymmetricCongruent`
is parameterised by an arbitrary `E` with `=~` read as equality-or-`E`, and
taking `E` everywhere true already makes `=~` total across the 24 clauses; the
transport model extends exactly that to all 39 pre-closure clauses. Read
together, the two say the
same thing at two scopes: the clause set contains no distinctness assumption at
`=~`, and adding operations and ordinals does not introduce one.

The practical consequence is narrow and worth being plain about. Every statement
in the development of the form "these two Forms differ" must be carried by `≡`,
where `ax-diff` and `closeStructDistinct` do declare something, or by a clause
that does not currently exist. The source describes `+` and `additionally` as
distinct operations. The clauses, as written, cannot tell them apart --- and the
next section shows that this is not an accident of the model but of the
declarations.

## Why they cannot: `+` and `additionally` are declared by the same clauses

The model argument above says the distinctness is independent. It does not say
what is wrong, and what is wrong is visible in `L2Operations.lean` with no model
at all.

Read the two operation blocks side by side:

| sequencing (`+`) | cooperation (`additionally`) |
| --- | --- |
| `axSeq : ∀ a b, ∃ c, (c ~~ a) ∧ (c ~~ b)` | `axCoop : ∀ a b, ∃ c, (c ~~ a) ∧ (c ~~ b)` |
| `axSeqIdentityR : ∀ a, ∃ c, (c ~~ a) ∧ (c =~ a)` | `axCoopIdentity : ∀ a, ∃ c, (c ~~ a) ∧ (c =~ a)` |
| `axSeqIdentityL : ∀ a, ∃ c, (c ~~ a) ∧ (c =~ a)` | |
| `axSeqAsymm` | `axCoopComm` |

Not corresponding. **Identical**, character for character. Five declarations,
two propositions. `Hypermath.sequencingClausesAreCooperationClauses` is the
kernel check: it states one proposition twice and inhabits the left copy from
`⟨axSeq, axSeqIdentityR⟩` and the right copy from `⟨axCoop, axCoopIdentity⟩`.
Both elaborate, so the two are the same type and not merely analogous ones. The
printed statement is `And X X`.

`nc1_L2` and `nc2_L2` --- the graduation obligations for sequencing and for
cooperation --- have carried the identical statement, one line apart, since they
were written. The evidence was never hidden.

That leaves one pair, and it does not separate them either. `axCoopComm` is
unconditional: for every `a b` it produces two `~~`-witnesses that are `=~` to
each other. `axSeqAsymm` fires only on `¬ (a =~ b)`, and by
`no_incongruence_is_derivable` no instance of that antecedent is derivable from
any of the 39 pre-closure clauses. It is a conditional whose hypothesis the clause set can
never discharge. `HypermathTransportCountermodel.sequencing_asymmetry_never_applies`
is the statement in the model where this is plainest: `=~` is total there, so
`axSeqAsymm` holds by vacuity rather than by producing anything.

So the admission was not close. `plusAndAdditionallyAreDistinct` asks the clause
set to distinguish two operations it declares with the same obligations, using
the one clause it cannot fire. The repair is a distinctness clause at `=~` ---
`similarReflexive`-style, declared rather than derived. Strengthening
`axSeqAsymm` in place does not work, because its antecedent is the problem, not
its conclusion.

`tests/test_declared_counts.py` pins both halves: the duplicate groups, and the
fact that `axSeqAsymm` is the only clause in the layer mentioning incongruence.
If either changes, the independence argument has to be re-read.

### Four of the seven are removable

Being written twice is not the worst of it. `axSeq` and `axCoop` are also
*derivable*. `axCoopComm` already produces, for every pair, two common
similarity witnesses that are congruent to each other; keep the first and
discard the rest and what remains is exactly their statement.

`Hypermath.commonWitnessesComeFromCommutativity` (L2 §VII.b) proves both
propositions and `#print axioms` reports its dependencies as

> `Congruent`, `Form`, `Similar`, `axCoopComm`, `axCoopIdentity`

--- no `axSeq`, no `axCoop`, no `axSeqIdentityR`, no `axSeqIdentityL`. Those
four declarations can be deleted and every theorem in the development still
goes through. The operation layer's real content is three clauses:
`axCoopComm`, one identity clause, and `axSeqAsymm`, which never fires.

That is worth separating from the duplication. Two identical declarations are a
drafting slip. Two *derivable* ones are a claim about strength: whatever
sequencing was supposed to assert beyond co-presence, the clauses do not assert
it, and deleting them loses nothing to lose.

## What no clause mentions

The eight admissions were classified one at a time --- build a model, watch the
property fail, record it. For a whole class of claims that work was avoidable,
and the cheap measurement says which class.

There are 26 declared symbols and 44 clauses. Ask, for each symbol, how many
clauses mention it at all:

| clauses | symbol |
| --- | --- |
| 0 | `pathLength`, `pathStep`, `pathTrace` |
| 1 | `Definition`, `Discharge`, `deriver`, `pathStart`, `pathEnd` |
| 2 | `DerivationPath`, `FormClosure`, `compose`, `pathGround`, `structDistinct`, `structOrbits` |
| 3 | `congruentPath`, `structContinues` |
| 5 | `Derives`, `Substance` |
| 6 | `HMSyntax`, `Semantics`, `Simulation` |
| 9 | `f2f` |
| 11 | `Congruent`, `ground` |
| 13 | `Similar` |
| 30 | `Form` |

**Three symbols are mentioned by none of the 44 clauses.** Nothing stated about
`pathLength`, `pathStep` or `pathTrace` alone is derivable, and no model has to
be built to know it: any model may read them however it likes and every clause
still holds. `pathLengthArithmeticClaim` and `compositionLengthAdditiveClaim`
were each refuted by construction. The table says neither was ever reachable,
along with every other claim of that shape nobody has written down yet.

The row below it is nearly as empty. Of the five symbols exactly one clause
mentions, four are named only by the clause that *defines* them off something
else --- `Definition` and `Discharge` by their own `close` clauses, `deriver` by
`axDeriverAtLimit`, which is an equation --- so they carry no content of their
own. `pathStart` and `pathEnd` are named only inside `axLimitDerives`, and there
only at the single path it asserts to exist. At any *given* path they are as
free as the three above.

Read together with `congruentPath`'s three clauses this settles a question the
definition route left open. The documented reading of `congruentPath` is
agreement on `(start, end, path trace, quantification)` --- and `pathStart`,
`pathEnd` and `pathTrace` are all in the two rows above, with `pathLength`
standing in for quantification in the fourth. The intended definition is built
entirely out of symbols the clause set does not constrain. That is why
`tuple_reading_consistent_and_conditional` can only relocate its missing
assumption: there is nothing underneath to discharge it against.

The same reading explains `axComposeNonempty`. Its docstring says "at least one
non-trivial DerivationPath exists connecting any two Forms", its statement binds
`∀ x y : Form` and then never uses them --- Lean's own linter says so on every
build --- and the reason it cannot say what the docstring says is that
"connecting `x` to `y`" needs `pathStart` and `pathEnd`, which no clause about
an arbitrary path constrains.

`tests/test_declared_counts.py` recomputes the table and pins the first two
rows. A future clause that starts constraining one of those symbols fails the
test, which is the signal to re-read every independence argument that rested on
the silence.

### The row of zero, in the kernel

A test that recomputes the table is a measurement of the source text. The
statement underneath it is about the clauses, and where a clause set is carried
by a structure it can be checked by the kernel instead.

`Ordinatics.Transfinite` is such a structure and is the nearest instance to
hand: it declares `limit`, `succ` and `apply` with five laws, and no law
mentions `apply`. `Ordinatics.Transfinite.withApply` rebuilds an instance around
a new application, and it elaborates *because* of that silence --- every proof
field still typechecks after the swap. The same expression at `succ` does not
elaborate, and the error names `succExtends`. So the kernel is checking the
incidence, not a reader.

What the silence buys is a splitting. `apply_is_free` gives, for any instance
and any function whatever, an instance with that application and the same limit
and successor; `apply_is_a_free_factor` gives the converse, that instances
agreeing on limit and successor differ by nothing else. An instance of the
interface is a constrained part with a free function carried alongside, and
neither theorem depends on any axiom.

`Ordinatics.TwoChainModel.only_apply_is_unconstrained` finishes the sort at one
substrate: every function is some instance's `apply`, `id` is the successor of
none, `ground` is the limit of none.

#### And in this repository, which needs an arbitrary carrier to do it

The same thing is available here, but only in the abstract setting, and the
reason is worth more than the theorem.

`FreeFiltration.PrefixAxiomsCarrying` is the 24 clauses again with three further
symbols carried alongside --- the types of `pathLength`, `pathStep` and
`pathTrace`, the zero row --- and every clause copied verbatim.
`carried_symbols_are_free` transfers an instance from any assignment of the
three to any other, `carrying_iff_prefix` says carrying them changes nothing in
either direction, and `the_unmentioned_are_unconstrained` is the pair:
everything the clauses assert is compatible with every reading whatever of the
symbols they never name. All three are axiom-free, and each proof is two
tactics: `cases` splits the instance into its fields, and
`constructor <;> assumption` rebuilds it at the new assignment.

The two tactics are the measurement. `assumption` closes a goal only by matching
a hypothesis, so a clause that did mention one of the three would leave a goal
nothing matches. Injecting `pl` and `ps` into one field makes all three theorems
fail with `tactic 'assumption' failed`, which is the check confirming it can
fail.

**It has to be an arbitrary carrier.** The first version of this was written
against `HypermathFullAxiomModel`, where the same structure, the same statement
and the same two tactics all went through --- and checked nothing. That model
defines `structContinues _ _ : Prop := True`, so the mutated field
`structContinues (pl pathGround) ground` unfolds to `True` and `assumption`
closes it from the unmutated hypothesis. The clause mentioned the parameter and
transferred anyway.

The general form is worth stating on its own, because it is not about these
clauses:

> A freedom theorem proved inside a model cannot witness a silence. The model is
> free to interpret the mention vacuously, and then the transfer succeeds for a
> reason that has nothing to do with the clause set.

That is the same failure the guard hygiene note records in a different dress: a
proof wide enough to succeed is wide enough to succeed for the wrong reason. The
ordinatics version escapes it because `withApply` transports proof *fields*
whose types the elaborator must recheck, not goals a model may unfold; this
repository's version escapes it by having nothing to unfold.

### The row of one is two rows

The table's zero row settles itself. Its next row does not, and reading it above
took a sentence of hand analysis --- four of the five symbols are "named only by
the clause that defines them", the other two only inside one existential. Those
two readings are not variants of one situation. They point opposite ways, and
both are provable over an arbitrary carrier with no model at all.

`FreeFiltration.determined_by_its_closing_clause`: two relations satisfying the
same biconditional are equal. A symbol whose only clause is a close has no
freedom whatever --- not a little, none --- and the clause contributes a name
rather than a constraint. That covers `Definition` and `Discharge`, and it is
also why the seven closes are `rfl` in the characterization.

`FreeFiltration.endpoints_free_off_one_path`: take any model of the one clause
mentioning `pathStart` and `pathEnd`, and any two assignments of endpoints
whatever. Keep the model's values at its own witness, take the arbitrary ones
everywhere else, and the clause holds again. An existential clause pins its
symbol at one point and says nothing about it anywhere else.

`incidence_one_is_two_cases` states both together. The exclusion of the witness
is load-bearing: dropping `p ≠ w` from the statement makes the proof fail, so
this is freedom at every point but one and not freedom everywhere.

The method that comes out of it is two steps rather than one.

| what the count says | what follows |
| --- | --- |
| no clause mentions the symbol | free outright; if it is a structure field the structure splits |
| one clause, a biconditional | determined outright; the clause adds a name |
| one clause, an existential | pinned at one point, free at every other |
| anything else | read the clause |

Only the first line is an answer on its own, and it is an answer precisely
because there is no clause whose shape could be read. Everywhere else the count
narrows the work and does not do it.

### The claim that was unreachable three times over

`pathLengthArithmeticClaim` is the case where all of this lands at once. It says

> `pathLength (compose p q) =~ ordinalApply (pathLength q) (pathLength p)`

and it was closed by building a full-clause model that refutes it. Of the four
symbols on the two sides, the relation is the only one the clause set pins.

| symbol | clauses | what that means here |
| --- | --- | --- |
| `Congruent` (`=~`) | 11 | pinned; it is the relation, not the content |
| `compose` | 2 | `axComposeAssoc`, `axComposeIdentity` --- which do not make it a monoid (below), and the reading that made the claim look plausible, `compose := (+)`, is a choice of model rather than a consequence |
| `pathLength` | 0 | nothing whatever |
| `ordinalApply` | none --- and no law either | nothing whatever, at either level |

`ordinalApply` is the new entry. It is not one of the 26 declared symbols at all
--- it is a projection of the single `ordinatics` instance --- so the table above
never had a row for it, and the question the table asks has to be asked twice:
**no law of the interface mentions that field**
(`Ordinatics.Transfinite.apply_is_free`, in the ordinatics kernel) and **no
clause of this repository mentions it either**
(`Hypermath.ordinalApplyUnconstrained`, pinned by
`tests/test_declared_counts.py` with `ordinalLimit` and `ordinalSucc` as the
control).

So both sides of the claim are built out of symbols with no content, and the
construction that refuted it was answering a question the incidence count
answers first and more strongly. A refutation says one reading defeats the
claim. The count says every reading is available, so there was never anything to
defeat.

The same applies to the two other named propositions beside it.
`ordinalZeroIdentityClaim` and `ordinalSuccAppliesClaim` are both about
`ordinalApply` alone, and `ordinalApplyUnconstrained` gives, for any function
whatever, an instance of the interface over this substrate with this limit, this
successor, and that function for its application. Deriving any of the three means
**declaring** a clause for the application --- which is what the ordinatics field
docstring means when it says a theory that wants one supplies it itself.

## Symmetry of `congruentPath`

`congruentPath` is an opaque parameter (`L2Operations` line 73) and exactly
four of the 44 clauses mention it: `axComposeAssoc`, `axComposeIdentity`,
`axComposeNonempty`. None relates `congruentPath p q` to `congruentPath q p`.

`FullAxiomsWith` is `FullAxioms` with that one symbol left as a parameter. The
same structure satisfies it twice: under the model's own reading `p = q`
(`fullAxiomsWith_congruentPath`, symmetric by
`congruentPathInternals_holds`) and under `p = q ∨ (p = 1 ∧ q = 2)`
(`asym_full_axioms_hold`, not symmetric by
`congruentPathInternals_claim_fails`). `congruentPath_symmetry_independent`
packages both.

### It is not reflexive or transitive either, and `compose` is not a monoid

Symmetry was one cell. The other two were not hard --- they were unaskable,
because `FullAxiomsWith` varies `congruentPath` and holds `compose` and
`pathGround` fixed. With `compose` pinned to `+`, the two sides of
`axComposeAssoc` are the *same numeral*: `p + (q + r)` and `(p + q) + r` reduce
to one element, so the clause degenerates to `cp x x` for every `x` and
reflexivity looks forced. It is not forced by the clause. It is forced by the
choice of `compose`.

Open all three at once. `HypermathFullAxiomModel.PathClauses` is the three
clauses that mention any path symbol --- `axComposeAssoc`, `axComposeIdentity`,
`axComposeNonempty` --- with `compose`, `pathGround` and `congruentPath` all
parameters. Nothing else in the clause set has to move: by the incidence table
above, no other clause mentions any of the three, and
`tests/test_declared_counts.py` pins that this is still so.

Then take composition that costs a step:

| symbol | reading |
| --- | --- |
| `compose p q` | `p + q + 1` |
| `pathGround` | `0` |
| `congruentPath x y` | `(x = y ∧ 2 ≤ x) ∨ x = y + 1` |

Associativity lands at `p + q + r + 2`, which the first disjunct covers. Either
identity lands one step above `p`, which is the second. Nonemptiness holds at
`0`. Nothing reaches down to `0` or `1`, and `congruentPath_is_not_an_equivalence`
reads off all three failures from that one gap:

> `congruentPath 0 0` is false; `congruentPath 1 0` holds and `congruentPath 0 1`
> does not; `congruentPath 2 1` and `congruentPath 1 0` hold and
> `congruentPath 2 0` does not.

`path_clauses_decide_nothing_about_congruence` puts the model's own reading
beside it, where `congruentPath` is equality and all three hold.

The consequence is about `compose`, not about `congruentPath`. "Associative and
unital up to `congruentPath`" reads as a monoid in a quotient, and that reading
needs the relation being quotiented by to be an equivalence. The clause set does
not say it is. So `axComposeAssoc` and `axComposeIdentity` do not make `compose`
a monoid up to anything, and the two clauses assert strictly less than the
operation names they are attached to suggest.

### Twice now, what was held fixed decided the answer

`prefixAxioms_iff_conditions` was first stated over the ground chain, where
`Reach` is total and two of its eight conditions cannot say what they mean. This
is the same shape one layer up: `FullAxiomsWith` was built to vary the symbol
that was in question, and the symbols it left alone are what made two of the
three cells invisible.

The rule that falls out is narrow enough to use. **A model answers a question
about a symbol only as far as the rest of the model is free.** Before believing
that a clause forces something, check whether it forces it in the model or in
the clause --- and the check is to vary the *other* symbols, the ones nobody is
asking about, until either the force survives or it does not.

### The third list joins, and the binders in it were never doing anything

Two lists have been characterised: the eight prefix conditions and the three
operation conditions. The three path clauses were opened above to *vary*
`congruentPath`, not to be characterised, and they are the last clauses this
repository declares on its own.

`FreeFiltration.ComposeAxioms` states them over an arbitrary path type with
`compose`, `pathGround` and `congruentPath` all parameters, and
`composeAxioms_iff_conditions` characterises them by three conditions. Two are
copied unchanged. The third loses something.

`axComposeNonempty` is declared as `Form → Form → ∃ p, ¬ congruentPath p pathGround`.
Its docstring promises a path between any two Forms; its statement takes two
Forms and then has no way to mention either of them.
`compose_nonempty_binders_are_inert` proves the two binders are removable ---
`(Form → Form → P) ↔ P`, given any one Form to discharge them with --- so the
entire content of the clause is that *something* is not the unit. This is the
row-of-zero reading applied inside a single clause rather than across the clause
set: a binder no part of the statement uses constrains nothing, exactly as a
symbol no clause names does. The gap between the docstring and the statement is
the same gap the pointer audit above kept finding, one scope smaller.

`prefixOperationsCompose_iff_conditions` then joins all three lists: **34 of the
39 pre-closure clauses, fourteen conditions, arbitrary carrier and arbitrary path type, no
axioms.** What is left outside is the five transfinite projections of the single
`ordinatics` instance, which the next section but one folds in as well.

### Fourteen *is* eleven plus three, and the incidence table said so first

The first join was not a sum. `operations_exclude_the_unreached_point` exhibits
a model of the eight prefix conditions in which the three operation conditions
cannot be met, which is why eleven is not eight plus three and why a freedom
proved against 24 clauses has to be re-checked against 31.

The second join is a sum, and it is predictable before any proof is attempted.
The operation clauses speak `~~` and `=~` --- the same two relations the prefix
constrains --- so they can collide with it. The composition clauses speak
`compose`, `pathGround` and `congruentPath`, and **no condition among the eleven
mentions any of the three**. Disjoint symbols, disjoint content.

`compose_conditions_are_always_available` supplies the witness: the naturals
under addition, with `congruentPath` read as equality, satisfy all three.
`lists_join_freely_exactly_on_disjoint_symbols` puts the two joins side by side
--- the obstruction on the left, and on the right the composition layer sitting
on top of *any* model of the eleven whatever. The proof of the right-hand
conjunct is the two hypotheses and that witness, and nothing else.

A trivial proof is the right outcome here rather than a weak one. What had to be
established was that nothing can obstruct, and the reason nothing can is
readable off the incidence table already in this note:

> Clause lists compose as freedoms exactly when the symbols they name are
> disjoint. Where the symbols overlap the join has to be measured, and it may
> shrink the model class without adding anything to what the clauses say.

The witness being a monoid does not undo the section above. Those three clauses
do not *force* a monoid: `congruentPath_is_not_an_equivalence` satisfies the
same three conditions with `compose p q = p + q + 1`, where `compose p pathGround`
is `p + 1` rather than `p` and the unit clause holds only up to a
`congruentPath` that is not an equivalence. Both models are permitted, which is
what "condition" means here and what "clause" never guaranteed.

### The last five, and what a symbol occurring once does to a shared binder

`TransfiniteAxioms` states the transfinite projections with every symbol they
name left open: the carrier, the three relations, the path type and its two
projections, and `deriver`, `ordinalLimit` and `ordinalSucc`. Two of the
eliminations are the incidence readings already used above, and one of them does
something the earlier cases did not.

`deriver` occurs in one clause, and occurs there in an equation ---
`axDeriverAtLimit : deriver = ordinalLimit`. That is the *determined* case: the
clause fixes the symbol rather than constraining anything, so both go, and the
count drops by one.

`pathStart` and `pathEnd` occur in one clause, and occur there existentially ---
`axLimitDerives : ∃ p, S (pathStart p) ground ∧ C (pathEnd p) ordinalLimit`. That
is the *pinned at one point* case, and pinning them **separates the clause**. As
written, one `p` has to serve both halves, and that shared binder is the only
thing tying them together. Free the two projections and the coupling has nothing
to hold: `transfinite_clauses_are_five_conditions` reads the clause as
`(∃ a, S a ground) ∧ (∃ b, C b ordinalLimit)`. So one clause leaves **two**
conditions behind, and the two eliminations cancel.

`all_thirty_nine_iff_nineteen_conditions` is then the whole declared clause set:
**39 of the 39 pre-closure clauses, nineteen conditions, no axioms** --- eight for the
prefix, three for the operations, three for composition, five for the
transfinite layer. Nothing this repository declares is outside that statement.

The observation is worth separating from the arithmetic. A binder shared between
two halves of a clause is doing real work, and the row-of-one reading dissolves
it. `axComposeNonempty`'s binders were inert because its statement could not
mention them; `axLimitDerives`'s binder is not inert at all --- it is load
bearing right up until the two functions it is applied to become free.

### Nineteen is not fourteen plus five, and the incidence table cannot say why

By the table this join should be free. `deriver`, `ordinalLimit`, `ordinalSucc`,
`pathStart` and `pathEnd` appear in no condition among the fourteen --- exactly
the situation that made the composition layer a union. The prediction is wrong,
and `nineteen_is_not_fourteen_plus_five` says how wrong:

* `BareChain` satisfies all fourteen conditions on a carrier the ground chain
  exhausts: the naturals, similarity and congruence total, simulation the
  diagonal.
* `spanned_carriers_admit_no_limit` shows no transfinite layer sits on it, for
  *any* choice of limit, successor, deriver and path projections.
* `LimitAdjoined` satisfies all nineteen on the chain with one point adjoined,
  so the obstruction is about which models extend and not about consistency.

The mechanism is one step. `axLimitNotFinite` denies simulation from every
finite position to the limit; `simulationDiagonalIsReach` grants simulation at
every reached point; `chain_points_are_reached` says every chain point is
reached. So `the_limit_is_off_the_chain`: the limit is not any `f2f^k ground`,
and a carrier with nothing else in it cannot supply one.

That is a demand on the **carrier**, and the incidence table records which
clauses name which symbols. It has nothing to say about how many Forms there
are. Three joins have now been measured and they fail three different ways:

| joined list | symbols | outcome |
| --- | --- | --- |
| operations | shares `~~` and `=~` with the prefix | obstructed, and the table predicts it may be |
| composition | three symbols in no condition | free, and the table predicts it |
| transfinite | five symbols in no condition | **obstructed anyway**, and the table cannot predict it |

The third row is the useful one, because it is where the instrument runs out.
Disjoint symbols are sufficient for a free join only among clauses that do not
also talk about *how much carrier there is*. `ground_is_not_an_image` shows the
prefix was already constraining the carrier --- forming never returns to the
ground, from `imageNotSimulatingGround` and the reached ground --- but that
forbids a coincidence inside the chain and never demands anything outside it.
`axLimitNotFinite` is the first clause in the set that does.

> A symbol-incidence table predicts a free join. It cannot predict an obstructed
> one, because the obstruction may live in the carrier, which the table does not
> record. Disjoint symbols are necessary and not sufficient.

### Ten of the 39 pre-closure clauses hold of nothing, so the reduction is
### twenty-nine to nineteen

`all_thirty_nine_iff_nineteen_conditions` does not say how many of the 39 were
already true before any condition was imposed. The answer is ten.
`the_closes_are_definitional` proves all ten with no carrier, no relation and no
hypothesis --- every conjunct is `Iff.rfl` --- because `FreeFiltration` *defines*
each auxiliary predicate to be the reading its closing clause asserts.
`prefix_is_its_fourteen_contentful_clauses` then removes them, and
`twenty_nine_clauses_carry_the_content` restates the characterisation over what
is left: **twenty-nine clauses, nineteen conditions.**

The namespace note above this said seven. Seven is the `*Opaque` family ---
`HMSyntax`, `Substance`, `Semantics`, `FormClosure`, `Derives`, `Discharge`,
`Definition`. Three more read `structContinues`, `structDistinct` and
`structOrbits` off the relations in exactly the same way, and are `rfl` for
exactly the same reason. The note has been corrected.

The direction that matters is the other one. These ten are **not** free in
hypermath. In the layers the auxiliary predicates are opaque parameters and
these ten clauses are precisely what pins them; the free reading discharges them
by fiat, at the cost of every model that would read an auxiliary predicate some
other way. That cost is real and it is paid by every result stated over
`PrefixAxioms`, this note included. What the ten measure is how much of the
clause set was spent defining its own vocabulary.

"Contentful" for the remaining fourteen means only *not discharged by the
reading*. It does not mean irredundant, and they are not:
`three_of_the_fourteen_are_derivable` derives `axGroundSelf` from
`filtrationCongSim` and `axGroundSubstanceAx`, `axGroundSyntaxAx` from `axSim`
at one step, and `axFormClosesLoop` from `filtrationSimCong` rearranged. The
reduction to eight `Conditions` measures the list as a whole. Clause by clause
it has never been measured, and that is the next open question this note leaves.

### The chain was joined at every link by a number

A clause travels from where it is declared to where it is characterised in three
steps, and until now every joint was an equality of counts:

| joint | what connected the two sides |
| --- | --- |
| layers to models | 40 logical declarations, one standing for five: thirty-nine and five make forty-four |
| model to model | five structures, each asserted to have forty-four fields |
| models to conditions | five condition structures, twenty-four and seven and three and five and five |

Forty-four five times over is agreement by arithmetic. A clause renamed in one
model and a different one renamed back keeps every count and moves nothing else.
Three tests now check the names instead:
`test_the_models_list_the_clauses_the_layers_declare`,
`test_every_clause_structure_names_the_same_clauses` and
`test_the_five_clause_structures_partition_the_clause_set`. All three pass on
the tree as it stands, which is the outcome worth having: the chain was sound
and is now known to be, rather than assumed to be.

The fifth structure and the fifth condition structure are the closing tier of
L0 §VIII.b and L2 §II. Its five clauses are properties of the relations ---
reflexivity and symmetry of `~~`, transitivity of `=~`, the denial of the
ground at `=~`, and symmetry of `congruentPath` --- and they are what the
closure added. They are a tier of their own because they say so about the
whole relation rather than about a carrier.

Getting there required fixing the reader, and the two defects in it are the more
useful finding. Its structure pattern required `where` on the line that opens a
structure, so any structure whose binders wrap was invisible --- and it returned
an empty dict for such a name rather than failing. Both `ComposeAxioms` and
`TransfiniteAxioms` wrap. Every measurement taken of them through that reader
had been a measurement of nothing, and the only reason this was never noticed is
that the reader's other callers assert a count afterwards. It also resolved a
repeated structure name by taking the last one, across namespaces:
`Countermodels.lean` declares six called `PrefixAxioms`, and a question about
one of them was being answered about another.

> An instrument that answers a question it was not asked will agree with you.
> Both defects returned a well-formed result for a name they could not resolve,
> and a well-formed wrong answer is worse than an exception in exact proportion
> to how much is built on top of it.

### Is any one of the eight implied by the other seven?

Eight conditions replaced the fourteen contentful clauses of the prefix list,
and that reduction was measured as a whole. The biconditional holds, so nothing
was lost --- and it
says nothing at all about how the eight stand to each other. A list can be
equivalent to what it replaced and still contain a condition the rest already
force. The reduction looks the same either way.

Eight models answer it, one per condition, each satisfying the other seven and
refuting its own. They come in three kinds, and the kinds are the finding.

**Three of them thin similarity at one family of pairs.** `ImageSimilar`,
`ImageSimilarToGround` and `DoubleImageSimilar` demand `~~` at `(f x, x)`, at
`(f x, ground)` and at `(f (f x), x)` respectively, and nowhere else. So each is
refuted by a similarity that holds everywhere except where that one condition
demands it, and the other two survive because the pairs they demand are
different pairs. Note what the incidence table would have said: all three
mention `S` and `f2f` and nothing else, so on symbols the three are
indistinguishable. Independence here is a fact about *which arguments* a clause
demands the relation at, and a scan over symbol occurrences cannot see an
argument. This is the third distinct way that table has been too coarse, and the
first in the opposite direction --- identical symbol sets, three independent
conditions.

**Two more keep every relation total.** Once `~~` is everything, `Reach` is
everything, and both diagonal conditions collapse to reflexivity of the relation
named. That is why the model for `ImageNotSimulatingGround` can read all three
relations as `True`: against a maximal reading, the only clause left that can
fail is the one denial in the list.

**And one of the eight cannot be refuted on the chain at all.** Half of
`CongruentDiagonalIsReach` is already proved from the other seven --- a reached
point self-simulates by condition eight, and self-simulation is self-congruence
by the inclusion, which is `reached_points_are_self_congruent`. So a model that
refutes condition seven has to exhibit a point congruent to itself that `Reach`
does not go to, and on the chain carrier every point is reached. It needs the
adjoined point: the same carrier `congruent_reflexivity_needs_an_unreached_point`
needed, for the same reason, one level up. The model is that carrier with `~~`
and `≡` left exactly as they were and `=~` widened to plain equality --- the one
widening `ext_conditions` refused to make.

### Irredundant is not minimal

None of the eight follows from the other seven, and two of them are still twice
as strong as they need to be. Both diagonal conditions are biconditionals, and
one half of each is derivable from the other half of the other one plus the
inclusion. `conditions_iff_six_and_two_implications` states the sharpened list:
six conditions unchanged, and two implications in place of the two
biconditionals ---

```
congruentDiagonalReaches : ∀ x, C x x → Reach ground f2f S x
reachedIsSelfSimulating  : ∀ x, Reach ground f2f S x → E x x
```

--- from which both biconditionals come back. Which two halves survive is not a
choice. The inclusion runs from simulation to congruence, so the two halves it
can supply are the ones running with it, and the two it cannot are the ones
running against it: congruence descending to `Reach`, and `Reach` rising to
simulation. Those are the two that have to be assumed. The same two models
refute them (`the_descending_half_is_not_derivable`,
`the_rising_half_is_not_derivable`), so the sharpened list is irredundant
exactly where the sharpening happened.

Lean checks that each model's statement is true. It cannot check that the seven
conditions a model asserts are the *other* seven: a statement listing its own
condition twice and one of the remaining seven not at all would typecheck, and
would read as though it had done the work.
`test_each_condition_is_either_refuted_or_derived` and
`test_every_model_names_its_whole_group_and_denies_one` measure the names, and
`test_the_sharp_list_keeps_six_conditions_word_for_word` checks that the sharp
list copies the six it does not weaken rather than restating them.

### Is any one of the three implied by the other two?

The operation layer contributes three conditions on top of the eight, and
`operations_exclude_the_unreached_point` already shows the three are not implied
by the eight. The question that leaves is the sharper one: does any one of the
three follow from the other two *while the eight hold*? That is not the same
question as whether it follows from the other two alone. The eight constrain the
very `S` and `C` the three quantify over, so a model refuting one of the three
has to keep the eight while it does so, and the eight are the reason it cannot
just be the empty structure.

Three models answer it: `NeedsPairedWitnesses`, `NeedsIdentityWitness` and
`NeedsApartWitnesses`, each satisfying `Conditions` and the other two, and
refuting its own. What the three have that the eight did not is a lemma apiece
saying where the condition is *already proved*, and those lemmas are what fix
the shape of each model.

**A reached point is its own identity witness.**
`reached_points_are_their_own_identity_witness`: the seventh condition gives
`C x x` from `Reach x`, and the inclusion turns that into `S x x`, so
`IdentityWitness` holds at every point the chain arrives at. Refuting it needs a
point off the chain --- and one is not enough. A single adjoined point lying
under everything is the only common predecessor a pair of distant chain points
has, and it may not be congruent to itself, because the diagonal condition ties
self-congruence to `Reach` and nothing reaches it. So the pairing condition
would fall with the identity one. The model adjoins two, relates them in one
direction, and that single congruence is what the pairing condition uses while
the point at the tail of it goes on owing a witness of its own.

**A reached common predecessor pairs the two points it lies under.**
`a_reached_common_predecessor_pairs_them`: serve the same predecessor as both
witnesses and the last thing to prove is `C c c`, which is `Reach c`. So a pair
refuting `PairedWitnesses` needs *every* common predecessor unreached, and no
two of them congruent --- and each of those still owes an identity witness,
which by the lemma above cannot be a reached point either. Two universal
predecessors with nothing relating them, and one witness apiece beneath them:
four adjoined points, and the lemma is why it is four.

**Two points lying under each other are their own apartness witnesses.**
`mutual_predecessors_are_apart_witnesses` uses nothing from `Conditions` at all.
`ApartWitnesses` at a pair is free as soon as `S` holds at the four pairs drawn
from it, because the hypothesis it is handed is exactly the denial its
conclusion has to produce. Where `S` is total that is every pair at once, so a
model refuting it has to keep `S` thin. The model that does is the chain with
one adjoined point and congruence read as plain equality: `S` reaches three
steps up and the ground below everything, which is the least the eight allow, so
the only common predecessor of two distant chain points is the adjoined one ---
and one point served twice is never apart from itself.

So none of the three follows from the other two over the eight, and the number
of points each model adjoins --- one, two, four --- is not incidental. It is
read off the freeness lemma, which says where the condition cannot fail; the
model is whatever the lemma leaves.

**What the three are balanced on.** Apartness is free where `S` is fat. Pairing
is free where `Reach` is fat, and `Reach` follows `S`. Both of those want the
same relation large --- so the model refuting apartness thins `S` and leaves
congruence alone, while the two models refuting the others leave `S` universal
at the adjoined points and thin the *congruence* instead. That is a fourth kind
of independence in this note, and the first between two relations rather than
within one. Three of the eight were separated by which arguments they demand the
relation at, two by what a maximal reading collapses, one by a point the chain
does not reach. Here the separation is a trade: what makes one of the three free
is what makes another refutable, and the incidence table sees none of it, since
all three mention `S` and `C` and nothing else.

### And the three the composition adds

The same question a third time, and the third answer is the cheapest of the
three. `composeConditions_iff_the_three` names the conditions ---
`AssociativeUpToCp`, `UnitalUpToCp`, `SomeNonUnit` --- and three models refute
one apiece.

| model | path type | composition | unit | refutes |
| --- | --- | --- | --- | --- |
| `NeedsAssociativeUpToCp` | the naturals | doubles its left argument | zero | associativity up to `congruentPath` |
| `NeedsUnitalUpToCp` | the naturals | addition | one | the unit law |
| `NeedsSomeNonUnit` | one path | the only thing it can be | that path | the non-unit |

**Why this one is cheap, and the operations were not.** A model refuting one of
the operations had to satisfy the eight filtration conditions while it did so,
because the operations constrain the very relations the eight have already
fixed. Nothing here has to be satisfied first. The path type, its composition,
its unit and `congruentPath` are all free of the carrier, so a model is a small
algebra and the carrier never appears in it. That is the second consequence of
the same disjointness `lists_join_freely_exactly_on_disjoint_symbols` read off
the incidence table: disjoint symbols make the *join* free, and they also make
the list's own internal question cheap. Where the symbols overlap, irredundance
is a question about a carrier; where they are disjoint, it is a question about
the list.

The audit sees it. Five of the fourteen models now depend on no axioms
whatsoever --- the three here, and the two among the eight that read every
relation as a constant. The other nine reason about positions on the chain, and
`simp` and `omega` bring `propext` with them. The dependency is a fact about the
tactic rather than about the mathematics, but it tracks exactly which models had
to look at a carrier at all.

**Where each is already free.** Both equational conditions come free from
reflexivity of `congruentPath` plus strictness: on-the-nose associativity gives
the first (`strictly_associative_is_associative_up_to_cp`) and a strict unit
gives the second (`strict_unit_is_unital_up_to_cp`). So neither is about
`compose` alone or about `congruentPath` alone --- each is about the pair, and
each model breaks the pair from the composition side while leaving
`congruentPath` as equality. The third runs the other way.
`no_non_unit_collapses_cp`: if nothing is a non-unit and `congruentPath` is
symmetric and transitive, then it relates every pair of paths. So the third
condition is free wherever `congruentPath` is a partial equivalence with two
classes --- and `congruentPath_is_not_an_equivalence` shows the three clauses
that mention it leave it neither reflexive nor symmetric nor transitive. It is
the only one of the three whose freeness would need a property the clause set
explicitly withholds.

**And the third model settles a docstring.** `axComposeNonempty` was already
known to have two inert binders, leaving "the clause's whole content is that
something is not the unit". `NeedsSomeNonUnit` prices that: drop the clause and
the one-path world satisfies everything the composition layer says. The clause
is not merely the only contentful part of its own statement, it is the only
thing in the layer ruling out the trivial structure --- which is what
`no_non_unit_collapses_cp` says abstractly and what the model says by being
built.

### And the five the transfinite layer adds

The same question a fourth time, and the fourth answer is the first *no*. Two of
the five conditions are theorems of conditions already on the list, so the
nineteen-condition characterisation is not minimal. The other three are
independent of everything else there is.

`transfiniteConditions_iff_the_five` names them, and then:

| condition | status | why |
| --- | --- | --- |
| `SomeStartAtGround` | derivable | `someStartAtGround_is_implied_by_the_eight` |
| `SomeEndAtLimit` | derivable | `someEndAtLimit_is_implied_by_the_operations` |
| `LimitAbsorbsTheChain` | independent | `NeedsLimitAbsorbsTheChain` |
| `LimitNotSimulatedFinitely` | independent | `NeedsLimitNotSimulatedFinitely` |
| `SuccEscapes` | independent | `NeedsSuccEscapes` |

**The two derivations are one line each, and that is the finding.**
`SomeStartAtGround` asks for something similar to the ground;
`imageSimilarToGround` says the image of *every* point is similar to the ground,
so the image of the ground is a witness. `SomeEndAtLimit` asks for something
congruent to the limit; `identityWitness` hands over something congruent to
*every* point, and the limit is a point. Neither proof is clever and neither
needed a search. They were not found earlier because nothing was looking: the
transfinite conditions were read as a block, and a block is exactly the wrong
unit for this question.

**A fourth way independence can fail: instantiation.** The three earlier failures
in this note were about symbols --- a symbol no clause mentions is free, a symbol
one clause mentions is free at every other point, two clause lists over disjoint
symbols join freely. This one is invisible to all three, because instantiation
does not change which symbols appear. `SomeEndAtLimit` and `identityWitness`
mention the same relation; the difference is that one of them quantifies its
point and the other names one. **A condition that names a point is implied by any
condition of the same shape that quantifies over points.** That is a criterion
the incidence table cannot state, because the table is indexed by symbol and the
difference here is a binder.

`SomeStartAtGround` is the starker case. It names *no* transfinite symbol at
all: not the limit, not the successor, not the deriver. It is a prefix condition
that happens to have been written down inside the transfinite structure, and no
countermodel to it can exist over any carrier whatsoever.

**The three that remain are independent of all eighteen others.** Each model
below satisfies the eight prefix conditions, the three operation conditions, the
three composition conditions and the four transfinite conditions that are not
its own, and refutes exactly one. No earlier model in the file manages more than
ten, because no earlier model had to stand on a carrier *and* carry a limit.

| model | carrier | what changes from `LimitAdjoined` | refutes |
| --- | --- | --- | --- |
| `NeedsLimitAbsorbsTheChain` | the chain with a limit | congruence thinned below the limit | absorption |
| `NeedsLimitNotSimulatedFinitely` | the chain with a limit | one simulation pair added, ground to limit | the finite denial |
| `NeedsSuccEscapes` | the chain with a limit | the successor is `id` | the escape |

Two of the three are one edit away from `LimitAdjoined`, which already proves all
nineteen conditions at once. That is what makes them sharp: the model and the
thing it refutes differ by a single decision, so the refutation cannot be blamed
on anything else in the construction.

**Where each is already free.** `a_limit_on_the_chain_absorbs_it`: if the limit
is a chain point, the hypothesis at that point is the conclusion, so absorption
is only ever a question about a limit that is off the chain.
`unreached_limits_are_not_simulated_finitely`: `simIntoCong` and `congIntoSim`
turn a simulation into a similarity, and a similarity from a chain point is what
`Reach` asks for --- so the finite denial is free wherever the limit is out of
reach, and the condition is not about the limit being infinite but about its not
being arrived at. `a_moving_successor_escapes`: a total congruence gives the
first conjunct and a fixed-point-free successor gives the second, so refuting
the escape needs either a thin congruence or a successor that stands still, and
the model takes the second because nothing else in the nineteen constrains the
successor at all.

**This does not contradict `nineteen_is_not_fourteen_plus_five`.** That result
says the transfinite list is not free over the other fourteen, and it is still
right: `spanned_carriers_admit_no_limit` obstructs, and what it obstructs is
`limitNotSimulatedFinitely` --- one of the three that survive. A list can fail to
be free over another list and still contain members implied by it. The two
questions were never the same question, and running them together is what hid
the redundancy for as long as it was hidden.

**The axiom rule held as a prediction.** The composition group left a rule: a
model depends on no axioms exactly when it never had to look at a carrier. All
three models here look at one, and all three depend on `propext`. So five of the
seventeen condition models remain axiom-free --- the same five as before, and
the rule picked them out in advance rather than after the fact. The prediction
was right and the criterion is not; *What an axiom report is a report of*, at the
end of this note, says what these three models actually have in common.

### Clause by clause at last: eighteen clauses, seventeen conditions

A redundancy nothing depends on is a remark. The section above found two, and
this one spends them --- and then answers the question the note has been leaving
open since the fourteen contentful clauses were first counted.

**Sharpening the conditions: `nineteen_iff_seventeen`.** The two derivable
conditions come out and the other three are copied word for word. The place the
biconditional has to be stated is the interesting part.
`conditions_iff_six_and_two_implications` sharpened the eight from *inside*,
because every half it removed was a consequence of sibling fields of the same
structure. Nothing like that is possible here: the proofs of the two dropped
conditions live in two other groups. **A redundancy found across groups cannot be
repaired within a group** --- it has to be stated at the joint, where the proofs
are. And with `someStartAtGround` goes the last transfinite mention of `S`. The
sharpened layer speaks only of congruence, of equality and of the successor.

**Sharpening the clauses: `twenty_eight_clauses_carry_the_content`.** One clause
comes out, and it is a different kind of clause from the ten that
`twenty_nine_clauses_carry_the_content` removed. Those ten were `Iff.rfl`: true
of anything, because the free reading defines its own vocabulary.
`axLimitDerives` is a real statement about a carrier. It comes out because it is
implied, not because it is empty.

How it hid is worth stating on its own. The clause is an existential binding two
halves under one witness: some path starts similar to the ground *and* ends
congruent to the limit. Neither half can be matched against anything while the
witness ties them together. Pin the binder and they come apart, and then each is
an instance of a clause that quantifies where this one names --- the first of
`axSim`, the second of `axSeqIdentityR`. So, alongside the instantiation rule
from the previous section:

> A clause that binds two halves under one witness can be redundant with neither
> half visibly so. Pin the binder before reading either half, or the clause looks
> irreducible because it is being read whole.

**The open question, answered.** The docstring on `ContentfulPrefixAxioms` said
the list had been measured as a whole and never clause by clause. Measuring all
four layers:

| layer | clauses | contentful | needed | conditions |
| --- | --- | --- | --- | --- |
| prefix | twenty-four | fourteen | nine | eight |
| operations | seven | seven | three | three |
| composition | three | three | three | three |
| transfinite | five | five | three | three |
| total | thirty-nine | twenty-nine | eighteen | seventeen |

`eleven_prefix_clauses_carry_the_content` removes the three that
`three_of_the_fourteen_are_derivable` derives, and
`twenty_clauses_are_seventeen_conditions` puts the layers back together at that
point. Eleven was not minimal either.
`nine_prefix_clauses_carry_the_content` takes two more clauses and two thirds of
a third, and `eighteen_clauses_are_seventeen_conditions` is where the line ends.

**Three of the four layers turned out to be their own conditions.** The
operations are seven names for four statements --- `axSeq` and `axCoop` are one
statement written twice, `axSeqIdentityR`, `axSeqIdentityL` and `axCoopIdentity`
are one statement written three times --- and the fourth statement is a
projection of `axCoopComm`, leaving three, which are `OperationConditions`
character for character. The composition is three statements carrying two inert
binders. The transfinite layer is three statements carrying one inert binder and
one clause implied from beneath. **The entire remaining distance between the
clause set and the conditions is the prefix layer** --- and that distance turned
out to be smaller than eleven against eight.

**Eleven was not minimal either, and what is left is one cycle.** Two of the
eleven are the ground at the diagonal, and the diagonal reaches it without being
told to: `axSim` puts the ground within reach at one step,
`axSyntaxRequiresSubstance` turns reach into congruence there, and
`axSubstanceRequiresSemantics` turns congruence into equality there. A third
removal is not a clause but two thirds of one. `traceLevels` states three things
at an image, and the second and third are `filtrationCongSim` and
`filtrationSimCong` read at that image --- **a conjunction can hide a redundancy
as well as a clause list can**, and a scan that compares clauses to clauses will
not find it.

Nine remain, and six of the nine are fields of `Conditions` written out
identically: the two filtration implications, the two image clauses, the double
image and the difference. What is left on each side is the diagonal, and
`three_implications_are_two_equivalences` states it with nothing else in scope:

| clauses | conditions |
| --- | --- |
| reach implies congruent | congruent iff reach |
| congruent implies equal | equal iff reach |
| equal implies reach | |

A cycle of three implications against two equivalences to the same point. That
is the entire residue of a reduction that began at thirty-nine clauses, and it is
not a redundancy at all. It is also not yet a fair comparison: a biconditional is
two implications, so the right-hand column is four statements counted as two
fields, and whether the count really differs by one cannot be read off a table
written in two connectives. *The last connective*, at the end of this note,
settles it --- two of those four are free, the hub is two arrows, and the
difference of one is real.

**In three of those four cases the measurement was already in the file.** This is
the part worth carrying away. `operationConditions_of_operationAxioms` reads
exactly three fields of its argument and has done so all along; the other four
are reconstructed by the reverse direction. That is a complete proof that seven
clauses are three, sitting in the open, written before anyone asked. The general
form is mechanical:

> If one direction of a bridge consumes only a sub-list of the clauses and the
> other direction rebuilds them all, the sub-list carries the list. The proof of
> the reduction is the proof already written; what is missing is the count.

Cheaper than a countermodel, and checkable by reading which fields a proof
mentions. The same reading applies to `three_of_the_fourteen_are_derivable`,
which proved three derivations and stopped without removing anything, and to the
incidence table, which had already listed `deriver` among the symbols exactly one
clause names --- so `the_deriver_binder_is_inert` is the operative form of a table
entry, exactly as `prefix_is_its_fourteen_contentful_clauses` is the operative
form of `the_closes_are_definitional`. **The table says free; a theorem says
removable; and until the theorem is written the count does not move.**

`the_deriver_binder_is_inert` is also the second inert binder in the file, after
`compose_nonempty_binders_are_inert`. Two instances make it worth naming as a
kind: a binder no other clause reads is not a hypothesis, it is a name.

**The nine are minimal, and the cycle was the only part that needed new work.**
Six of the nine are conditions written out identically, so a model refuting one
of those six is a model already in the file: the condition models each satisfy
the other seven conditions, five of which are the five remaining shared clauses,
and the two diagonal equivalences give all three arrows by
`three_implications_are_two_equivalences`. So such a model satisfies the other
eight clauses and refutes its own. Every step of that is a theorem or a textual
identity the guard below checks; the assembly is a reading of the two, not a
third theorem.

The three arrows inherit nothing, because an arrow is not a condition. They
needed models, and `nine_is_six_and_a_cycle` is what makes stating them cheap:

| model | reads | refutes |
| --- | --- | --- |
| `DropsReachIntoCongruent` | similar always, congruent never | reach into congruent |
| `DropsCongruentIntoSimulation` | similar and congruent always, equal never | congruent into equal |
| `DropsSimulationIntoReach` | the chain with a point reach never arrives at | equal into reach |

The first two read every relation as a constant and need no carrier at all ---
break the cycle by making two of its three points disagree everywhere. Only the
third has to be built, because breaking the arrow *back* to reach means having
somewhere reach does not go, and that is a fact about a carrier. The axiom rule
holds for a third time as a prediction: the two constant models depend on no
axioms and the constructed one depends on `propext`. It is the last time it is
cited as a rule; the model in the next section but one looks at a carrier and
depends on nothing, and that is where the criterion comes apart.

So the reduction is finished. Thirty-nine clauses, eighteen of them carrying the
content, every one of the eighteen irredundant, and seventeen conditions on the
other side of one triangle.

One hundred and thirteen guards hold the measurement.
The suite defines three hundred and fifteen guards in all, and this roster
names one hundred and thirteen of them. Below stand forty-one entries;
eighty-nine of the names here stand under one of them and twenty-four stand
under none, named between entries instead. The two hundred and two guards
this roster does not name at all are thirty-four in the twelve files it does
draw entries from and one hundred and sixty-eight in thirteen files it has never cited once. Which
of those belong here has not been decided. What is settled is that the answer
cannot move quietly: the check behind the total had these numbers in hand and
asked of each only whether it was large enough, which is true of every one of
them and is not what any of them is.
`test_the_needed_prefix_clauses_drop_exactly_the_three_derivable` checks that the
three removed are the three derived and that all four clauses the derivation
consumes survive the removal, which is the only reason it is safe.
`test_the_operation_clauses_are_seven_names_for_four_statements` checks the
duplicate claim that `operationAxioms_iff_conditions` has asserted in prose since
it was written, and which nothing compared until now.
`test_the_sharpened_transfinite_clauses_are_the_three_conditions` and
`test_the_contentful_transfinite_clauses_drop_exactly_one` check that the copies
are copies, because a biconditional would survive a rearrangement and the claim
being made is stronger than a biconditional.
`test_the_nine_prefix_clauses_are_six_conditions_and_one_cycle` checks the split
itself: which six are conditions word for word, which three are the cycle, which
two conditions they face, and that the clause replacing `traceLevels` really is
the conjunct it claims to be.
`test_each_arrow_of_the_cycle_has_a_model` checks that there are three arrow
models, that each carries the six and denies exactly one statement, and that
they are filed under `Drops` rather than `Needs` --- an arrow is not a condition,
and the condition coverage test would be wrong about its own subject if one were
filed there.
`test_a_conjunction_splits_under_forall_and_not_under_exists` and
`test_the_split_lists_have_one_more_field_and_no_conjunction` hold the normal
form the next section arrives at: which conjunctions are two clauses, which are
one, and that the lists said to be split are split.
`test_the_split_conditions_spend_both_biconditionals` and
`test_both_halves_that_survive_are_refuted_somewhere` hold the last connective:
that the two implications which arrive are halves of the two biconditionals
which leave, and that each surviving half is one the file already knew it could
not derive.
`test_the_arrow_vocabulary_is_the_five_the_six_do_not_give` and
`test_the_pairs_the_minimality_theorem_excludes_are_the_hub_itself` hold the
minimality claim: that the vocabulary it quantifies over is the whole vocabulary
--- five arrows, because the sixth is a shared clause --- and that the pairs the
theorem declines to refute are the hub's own two orderings and no third.
`test_the_two_lists_are_the_same_two_lists_in_both_theorems` holds the closing
claim, which is a claim about two named lists and so is exactly the kind Lean
cannot check: that the five conjuncts of the irredundance are five, that each
mentions its whole list and nothing off it, that each drops a different member,
and that the lists dropped from are the lists proved equivalent.
`test_every_countermodel_report_has_a_pinned_cost` and
`test_the_vocabulary_pair_still_costs_two_different_things` hold the cost table:
that every report has a recorded cost, that the four shapes are the four shapes,
and that the two halves of the vocabulary pair are still in different rows,
which is the whole of what the pair exhibits.
`test_no_proposition_is_proved_twice_for_the_same_price` generalizes that pair
into a rule over the file: theorems are grouped by namespace and by their
statement with binder style and bound names normalized away, and a group of more
than one has to differ in what its proofs spend. The vocabulary pair is the one
group that passes on purpose. It is here because `ground_is_not_an_image` was
proved twice and only a name collision caught it, and it is grouped by namespace
because three model namespaces prove a `succ_moves` whose text is identical and
whose subject is their own carrier.
`test_where_the_choice_principle_enters` holds the census of the choice
principle across every pinned table --- which tables name it, how many times,
and which four reports name it without naming `Quot.sound` or `propext` ---
because a claim that four reports are the unaccompanied ones is falsified by a
fifth joining them as surely as by one leaving.
`test_the_observation_row_reports_the_costs_it_claims` checks the one exact cost
claim the notes made before any table could check it: twenty-four observation
reports, twenty-two free and two costing choice.
Six hold the sweep. `test_the_sweep_covers_every_public_declaration`
regenerates the declaration list from the sources and requires the swept file
to name exactly those, because a list of names drifts in the direction that
loses coverage and says nothing while it does.
`test_the_layer_stack_consumes_downwards_and_never_upwards` and
`test_the_layer_stack_is_a_chain_and_the_measure_says_so` hold the shape: that
nothing reaches a layer declared after it, and that the stack is a chain over
the ground layer, which is the part no file structure implies.

That second guard was written against a sibling reading --- that `L1Relations`
and `L2Operations` are siblings over the ground layer, neither reaching the
other. The measurement said otherwise: `L2Operations` consumes `L1Relations`
and `L3Ordinatics` consumes both. The two claims disagreed, and the prose was
the one that was wrong. The sibling reading was carried by a scan that asked
whether `L1Relations` reached `L2Operations` and not whether the reverse held,
which is the shape of question a chain answers differently from a diamond.
`test_five_declared_clauses_are_consumed_by_nothing` holds the idle names in
both directions, against the sources for whether they are declared and against
every other pinned table for whether anything already names them.
`test_the_finite_action_results_rest_on_the_signature_alone` holds the eleven
to the three signature names, and
`test_the_milestone_costs_stay_inside_the_layers_they_may_consume` crosses the
two tables that were measured apart: a milestone's own costs must lie inside
the layers its declaring file consumes.
Three hold the associativity result.
`test_nothing_declares_the_composition_relation_transitive` measures its
premise instead of trusting it, pinning the clauses that mention the relation
and requiring that none applies it the three times a chaining clause needs.
`test_the_missing_step_is_the_only_difference_between_the_two_halves` is the
character-for-character comparison above, because a theorem whose negative half
denies something weaker than its positive half proves would typecheck and would
read as though transitivity had been isolated. And
`test_the_explained_clause_is_one_the_sweep_found_idle` keeps the explanation
and the thing it explains together, so that spending the clause or deleting the
block is a change to both.
Two hold the form-closure result.
`test_the_idle_form_closure_clause_is_the_stronger_of_the_two` measures the
premise there too: exactly the reviewed clauses mention `FormClosure`, and none
of them takes it as an antecedent, which is the whole reason the surplus
implication has nowhere to go.
`test_the_consumed_form_closure_clause_is_the_weaker_one` fixes which of the
pair is the idle one, because both are declared, both are clauses about form
closure, and the equivalence between them holds whichever one is spent --- so
nothing in Lean can tell that the block is explaining the right clause.
Three hold the incidence.
`test_no_declared_name_is_both_idle_and_spent_once` crosses the zero row
against the one row, which come out of one reduction and are reviewed as two
independent facts.
`test_two_theorems_hold_five_names_out_of_the_idle_set` pins the concentration
rather than the counts, so a proof rewritten to spend one of the five is a
visible change and not a silent one.
`test_the_form_closure_vocabulary_rests_on_one_theorem` holds the join of the
incidence with the idleness result, because either half can be edited into
agreement with itself while contradicting the other.
One holds the zero row at the whole clause set.
`test_the_zero_row_is_free_at_every_clause_there_is` compares
`FullAxiomsCarrying` field by field against the five structures it copies,
because that assembly is a measurement only while every field is still the
clause it copies. Bundling the five in as fields instead leaves the freedom
proof closing by the same two tactics while proving nothing about the symbols
it is named for; `carrying_iff_the_whole_clause_set` does refuse that bundle,
but only while its own proof is left alone, and the rewrite that makes the
bundled file compile clean is two lines.
Two hold the sweep against the table the audit reads it with.
`test_every_probe_runs_a_swept_file_and_every_sweep_is_a_probe` pairs the
probes, the pinned tuples and the files that end in a sweep, because the audit
pairs the first of those with each of the other two and nothing pairs those two
with each other --- a sweep added to a file no probe runs is printed by nobody.
`test_every_swept_theorem_has_a_pinned_record` makes the audit's comparison
without Lean, as far as that is available: a swept name the table does not pin,
or a pinned name no line asks for, ends the run rather than failing one check,
and the digest standing in front of that fires on every edit to the file and so
says nothing about any of them. The three Python facts about that tuple are
pinned against each other, which is why leaving one of them out is caught at
once and leaving all three out was not caught at all.
Two hold the admission.
`test_one_declared_name_is_held_only_by_an_admission` checks the claim against
the Lean source rather than against another table, in three directions: the
listed name's sole consumer must say `sorry`, the clause must stand in that
proof and not merely in its statement, and every other singly-spent name's
consumer must not say `sorry`.
`test_no_clause_is_held_only_by_an_admission` holds the row empty and keeps
the two results that make the hypothesis underivable, because the conjunction
is the claim and either half can be edited into agreement with itself. The
row emptied when the closing clause `axDiffCongruent` supplied the
incongruence that `plusAndAdditionallyAreDistinct` had been admitted for.
One holds the confinement.
`test_the_theory_is_confined_to_five_files` requires every layer file to be
wholly consuming, fixes the bridge as the rest of the support table, and names
`QuadrilateralFiltration` explicitly, since it is the one wholly-consuming file
that is not a layer and dropping it would leave a true but much weaker claim.
Three hold the seam.
`test_no_operations_clause_is_reached_from_outside_the_theory` splits the
bridge vocabulary into clauses and symbols using the model's clause structure
rather than a prefix test, and requires the operations clauses to be absent from
what the outside reaches --- the licence the layer-level support table cannot
give. `test_the_seam_goes_through_the_signature_in_every_file` holds the other
half, that every bridge file reaches `Form` and `f2f` and that exactly two reach
no clause at all, so a file drifting from signature use into clause use is a
visible change.
`test_no_declared_name_is_used_only_across_the_seam` holds the direction
neither of those covers, that nothing is reached only from the bridge, and
builds a sweep where something is so that an empty answer cannot come from an
absent computation.
Three hold the evidence table.
`test_the_finite_trace_row_counts_what_the_table_says` and
`test_the_finite_arithmetic_row_splits_where_the_reports_split` compute each
row's numbers from `PROVED_DEPENDENCIES` and require the prose to say them, so
that the two places can no longer drift apart in either direction.
`test_every_count_in_the_evidence_table_is_computed` does the same for the three
rows that cite a table size, and pins each group's split as well, so that the
rows whose prose mentions no axiom still cannot gain one quietly.
Two hold the other direction.
`test_the_theory_takes_two_things_from_outside_its_own_files` pins what each of
the five imports, since a machinery import is easy to add by accident --- the
file is right there and it typechecks --- and an import from another repository
is a dependency edge that ought not to appear silently.
`test_no_clause_is_stated_in_a_word_from_outside_the_theory` holds the half that
makes the first harmless, over both the clause structure and the types of all
sixty-one declared names.
One holds the audit's own failure path.
`test_no_probe_group_can_end_the_audit_without_a_report` requires every probe
group to reject an unreviewed axiom rather than raise past the audit's
handlers, and reads the handled kinds out of the audit's source rather than
restating them. It is the only guard here about whether an answer arrives
rather than about whether an answer is right.
One holds the index itself.
`test_every_declared_name_is_homed_where_the_source_declares_it` reads the map
from name to file back out of the Lean sources. It is the only guard here that
checks something no other computation uses, which is exactly why it was missing:
the homes of the five idle names were inert, so the suite could not have
noticed any of them being wrong.
One holds this roster.
`test_the_guard_roster_names_guards_that_exist` requires every guard named in
any of these documents to be a guard that exists, and the total above to equal
the number of distinct guards the roster names. The count had been raised by
hand at the end of every increment, which is the one piece of bookkeeping in
this repository that nothing computed; one pointer had already gone stale.

One holds the roster's own reach.
`test_the_roster_states_its_own_shape` holds the paragraph under the total to
the suite that paragraph is about. The total was computed the moment it was
questioned; what nothing computed was how much of the suite it covers, how many
entries carry it, and how many of its names sit under no entry at all. The check
behind the total had all three and kept a floor under each instead. A floor is
true and is not a measurement, and that difference is the whole subject of this
document.

One holds the names the notes credit.
`test_every_name_the_notes_credit_with_a_result_exists` holds the other
direction of the same convention, across every note here rather than this one:
where the prose says a name proves, checks or refutes something, that name has
to be something this repository or its Lean dependency actually declares.

One holds the verdicts the notes credit.
`test_no_note_credits_a_model_with_a_target_it_refutes` covers what the name
guard structurally cannot. Three notes credited `FiniteActionCountermodel` with
satisfying the self-derivation target after it had begun refuting it, and two of
those sentences named no declaration at all --- every backticked name in them
still existed, so a guard over names could not see it. This one reads each
model's verdict out of the *type* of its theorem rather than the theorem's name,
pins the four verdicts, and refuses a present-tense sentence that credits a
refuting model with the target. It is the first guard here whose subject is a
claim about a proposition rather than a name or a count, and it exists because
the same error occurred three times before anything failed.

One holds the shape of an independence claim.
`test_an_independence_claim_names_a_pairing` reads both directions of the word.
A theorem named `*_independent` has to state two parenthesized halves joined by
the only conjunction at depth zero, with the negation in exactly one of them;
and a paragraph claiming independence from the clauses, if it cites any
declaration at all, has to cite one so named. It was written after the same
defect was found twice in two days --- once where two *satisfying* models were
offered as an independence result, once where four rows of the table above named
only the refuting model --- and the shape rule is what distinguishes them,
because a conjunction and a negation somewhere in the statement is a test both
errors pass.

One holds the grid.
`test_the_nine_cell_grid_is_nine_pairings` builds the nine names
`<relation>_<property>_independent` from the three relations and the three
properties, requires each to be a declared pairing, and requires the three grid
rows above to name exactly those nine. It builds the names instead of listing
them, so the convention is the subject and a tenth cell cannot be added to the
table on its own.

It found those rows by scanning the whole note for a line prefix until
2026-09-21, which named the grid only for as long as the grid was the only
table using the three relations as row labels. The six-extreme table above is a
second one, and the guard duly reported six rows where the grid has three: a
true count of a table it could not tell from its own. It now locates the
section by its heading and reads rows only inside it. The guard was the
soundest reader in the roster and carried exactly the defect it was written to
catch --- a reading that held because of a fact about the document rather than
because anything required that fact.

Two hold the corners.
`test_each_corner_condition_has_a_model_that_drops_it` reads the field names of
`SimilarConditions` and `TotalSimilarConditions` out of the Lean source and
requires a drop model for each, named from the field and from how many fields
are left. An iff says what the conditions are and never how many facts they
are, and the paragraph below counts them --- five on `~~` against three at the
other corner --- so each count needs models and not names.
`test_a_corner_states_its_conditions_as_a_structure` requires the right-hand
side of both corner iffs to be a structure and not a conjunction, which is the
shape that let an uncounted fourth condition into the upper corner: a conjunct
can be added to a conjunction with no other change anywhere, and a field cannot
be added to a structure without a name and a model.

One holds the other nine condition lists.
`test_every_condition_field_is_dropped_separated_or_implied` reads all eleven
structures named `*Conditions` rather than the two above, and requires each of
their fifty-five fields to be accounted for: by a drop model, by a proof
separating it from the half it was split from, or by a proof that it is a
theorem of another layer. Ten have no drop model and none of the ten can have
one --- eight are halves of a split, where both halves hold in every model of
their own layer, and two are not conditions at all. The rule the entry above
states was applied to two structures out of eleven for as long as it has
existed, and the nine outside it were not failing it; they were outside it.

One holds the reader those three use.
`test_every_statement_the_guards_read_is_a_whole_statement` requires every
statement read out of `lean4/` to have balanced brackets and to stop before the
proof. The reader used to cut at the first `:=` in the text, and Lean spells a
named argument `(Form := Path)`, so twenty-eight statements were being read as
far as the inside of a bracket. That is not a guard failing; it is a guard
answering a question about a prefix. One of the three passed on a right-hand
side it should have rejected, which was checked by writing that right-hand side
out. A guard is only as good as what it is given to read, and nothing had been
looking at that.

One holds the whole of what that reader is given.
`test_the_statement_reader_sees_every_declaration` requires the dictionary to
have one entry per theorem in `lean4/`. It had 963 for 1052, and had lost the
other 89 by two mechanisms that each kept quiet. Its regex stopped at the first
dot, so the four theorems named `Alignment.<something>` shared a single key; and
55 bare names are declared more than once across `lean4/` --- `reach` eight
times, `full_axioms_hold` and `check_sound` five --- so the dictionary kept
whichever file came last alphabetically. The key now carries the module and the
enclosing namespaces, which makes it unique by construction rather than by luck,
and the count is compared with the sources on both sides.

The guard above is the one this cost. Its subject is readers that fail open, and
it was itself reading five sixths of what it named; a statement in the missing
sixth could have been cut inside a bracket and nothing would have said so. What
hid the loss was the shape of the check, not its strictness: the reader was
floored at five hundred entries, and `963 > 500` and `1052 > 500` are the same
answer. A floor cannot see a leak. Only a comparison with the source can, which
is the same lesson as every count in this document and the first time it was
owed to the guards themselves.

One holds the names that are fewer facts than they look.
`test_the_alias_families_are_the_declared_ones` pins the five sets of
declarations across `lean4/` that state one proposition with one proof under
several names --- eleven declarations, five propositions.
The guard above that prices repeated propositions had asked this of
`Countermodels.lean` alone, because the reader it had could not be asked about
anywhere else; with that reader repaired the question reaches the rest of the
project, and the rest of the project has the same shape in two files.
`L2Operations.lean` states three source obligations twice, once under the
operation each belongs to and once under the `nc<n>_L2` name of the graduation
section. `FullAxiomModel.lean` discharges five clause names with two proofs,
because three of those clause names are one clause and two more are another.

Every one of the eleven is wanted, and that is the point. A model that
discharges `axSeqIdentityL` should say so under that name whether or not
`axSeqIdentityR` is the same statement, and a graduation section reporting four
source obligations should report four. The defect is not the duplication; it is
that nothing said the names were fewer facts than they look.
`sequencingClausesAreCooperationClauses` says it for one file, in prose and by
elaborating both sides of an identity --- which is the right idiom and reaches
three of the eleven. The other eight had nothing. So the set is pinned and not
the count: a twelfth alias must be written down before it can exist, and a
family that stops being one because a proof or a statement changed fails the
same guard. An upper bound on duplicates would have passed while the set drifted
underneath it, which is the same failure as the floor in the entry above.

Two hold the paths the documents cite.
`test_every_path_the_documents_cite_is_one_that_exists` requires each of the
198 paths cited across 58 documents to be the tail of a path that some readable
checkout carries. 193 are. The naive form of that check --- every cited path
resolves from the repository root --- fails five ways, and each way is a fact
about how a citation works rather than an exception to be waved through. A
sentence names a file by as much of its path as it needs, so `L2Operations.lean`
and `lean4/Hypermath/L2Operations.lean` are one claim and a tail match is what
holds it. The imported documents under `references/precursor/` are pinned by
sha256 in their own manifest, so the five broken links they carry are evidence
of what arrived and must not be repaired; the guard reads that exclusion out of
the manifest, so unpinning a snapshot puts its links back under the guard rather
than quietly leaving them out. Three cited paths are build outputs, one is in
the verifier-standard sources, and one is not written. Those five are pinned
with the reason each is unreadable, so a sixth has to be classified before it
can exist.

Adding them cost the name guard an asymmetry it had been carrying for free.
The guard named further up as holding the names the notes credit resolves each
one against everything a reader could reach, and that set was built from the
Lean sources, so it held `Countermodels.lean` and not `README.md` --- two names
of the same shape, one of which happened to be a file this project compiles.
The first sentence to credit the second failed. The set now carries every file
name in the readable checkouts, on the ground that a credited name which is a
file is a claim about a file and the guard above is what holds it.

The other is the first guard here whose claim expires when work is *done*.
`test_the_construction_the_documents_call_unwritten_is_still_unwritten` holds
the three documents that cite `lean4/Hypermath/ConstructiveQuine.lean` because
it does not exist --- `README.md` records that it has not been written,
`CYCLE_BOUNDARY.md` that the construction it schedules does not yet exist and
so self-closure remains open, and `CONSTRUCTIVE_QUINE_SELF_CLOSURE.md`
schedules it as Stage 2. Everything else in this document catches prose that
fell behind its sources. This catches prose the sources caught up to, which is
the one failure that arrives as good news and so is the one nobody goes looking
for. Both halves are held together, because either alone fails open: check only
the file and the sentences can be deleted while the pin still claims a reason
no document gives; check only the sentences and writing the file leaves three
documents calling it unwritten.

One holds the names the notes cite.
`test_every_name_the_notes_cite_resolves_or_is_classified` requires each of the
847 identifiers these notes write in code style either to be a name some
readable checkout declares or to be classified as something else. The guard it
sits beside asks that question only when one of seventeen crediting verbs
follows the name. That vocabulary reaches 171 of the 940 words that follow a
name here; among the 769 it does not reach are `says`, `satisfies`, `requires`,
`supplies`, `retains`, `preserves`, `exhibits` and `asks`. Roughly ninety
sentences credit a name with a result in words nobody wrote down, and a name in
any of them could have been deleted from the sources with nothing noticing. A
count of what a hand-written list catches is a floor, and a floor cannot see a
leak.

What the vocabulary was really doing was suppressing false positives, and it
suppressed the true ones with them. Of the names these notes cite, some are
Lean's, some belong to other projects, some are values in a table, and some were
withdrawn from the sources and are cited *because* they are gone. So the
vocabulary goes, every cited identifier is held, and the 51 that do not resolve
are written down one at a time under six kinds. Two of those kinds are checked
against the sources rather than asserted: a name called withdrawn has to be
called that by a Lean comment, and a name called superseded has to have its
replacement still declared. The classification tried to be wrong first ---
`driverInDAtSimulation` and three of the ordinal claims were filed as withdrawn,
and the guard refused them, because each was replaced rather than dropped.

Widening what counts as declared was most of the work, and it is where the real
hole was. The reader that collects Lean names had never read a structure's
fields or an inductive's constructors, because it reads the line a declaration
starts on and members are not on it. 219 names were invisible, including the
eight fields of `Conditions` --- `imageSimilar`, `congIntoSim` and the rest ---
which this note cites more often than it cites anything else. The reader that
collects Python names read one module of the package, the one the first such
citation happened to be in, leaving 47 of the package's 89 constants outside.
Neither omission could be seen through the vocabulary, because no sentence
credits a field with proving anything: **a narrower reader and a narrower
question hid each other, and each was the reason the other went unnoticed.**

The fail-open control found one more thing by failing to fail. Renaming the
declaration of `ordinalZeroIdentityClaim` left the name resolving, because two
files declare it --- the layer that advertises the claim and the countermodel
that refutes it, each stating the proposition in its own namespace. A name that
exists twice is a name a single rename cannot remove, which is the same shape as
the six-of-nine reading further up: the second copy is not a duplicate, it is
the refutation carrying its own statement of what it refutes.

Three hold the claim that something is discharged.
`test_the_retired_names_are_read_out_of_the_sources` reads the eight names
these sources retire out of the sentences that retire them. The guard that
forbids citing a retired name as a proof used to carry a list of one, written
down by hand, under a docstring in the plural --- and the plural was the only
thing that said the list was supposed to be longer. `driverCycleIsClosed` was
the name being cited as a discharge on the day the guard was written, so it was
the name the guard held. `simulationPairExists`, `dSpansGround`,
`driverCycle_FRAME`, `conditionalRetrace`, `Abstraction`,
`abstractionTransitive` and `syntaxToAbstraction` were retired by these same
sources, in sentences that say so, and any of the seven could have been cited
as a proof with nothing objecting. **A hand-written list of what the sources
say is a copy of a measurement, and a copy goes stale in silence, because the
thing it copies does not know it is being copied.**

Reading the retirement took three tries, and the two failures are the
interesting part. A line reader finds five of the eight, because the sentence
that retires `Abstraction`, `abstractionTransitive` and `syntaxToAbstraction`
runs across three lines and names them on the first two. A sentence reader
finds seven, because `driverCycleIsClosed` is retired by "Step 16:
driverCycleIsClosed. There is no such theorem, here or anywhere." --- a label
and then the claim about it, which is this project's own idiom and puts the
name in the sentence *before* the retirement. So the reader is a sentence and
the one before it. It is not the comment block, which was the obvious next
widening and is wrong: §IX of `L3Ordinatics` is one block of sixty lines
containing two retirements, and reading the block would retire every name the
census mentions. Each widening is a claim about where a sentence ends, and the
one that goes too far is as wrong as the one that stops too early.

The other two hold the documents, which is where most of the claims are.
`test_the_documents_claim_more_discharges_than_the_sources_do` states the
reason as a measurement: the Lean comments claim a discharge on 52 lines, and
this project's own prose claims one on 89, across 22 files. The module that
checks discharge pointers says in its first line that it is about the Lean
sources, and it is --- that is where the rot was found, so that is where the
guard went, and it was never where most of the claims were. A majority of them
sat outside the subject of the only thing checking any of them.
`test_every_discharge_the_documents_claim_names_something_that_exists` asks the
prose the two questions the comments have been asked all along: the name has to
exist, and it must not be one the sources retired. The prose passes both today,
which it had been doing by luck.

One reading came out of the backticks along the way. A regex that blanks quoted
terms pairs the wrong delimiters: in "the withdrawn `conditionalRetrace`, which
was `fun _ _ _ hWit => hWit`" the first span containing a space is `, which was
`, so blanking it leaves the term exposed and reads `hWit` as a retired name.
Backticks are positional, not paired by pattern, and splitting on them gets the
answer a regex cannot. A span with a space in it is a term, and a name inside a
term is part of the term.

Three hold the rules this repository states about itself.
Everything above holds prose to sources. `AGENTS.md` §8 is a source that holds
prose: it says every skipped test MUST disclose its rationale against a rubric
of definitional categories, and `.github/PULL_REQUEST_TEMPLATE.md` states the
same rubric for the pull request that carries the skip. No test read either
document. The suite has been checking that the notes describe the sources, and
the one document telling the suite what to do was outside every reader --- the
same claim from the other side, and the side with no guard at all.

`test_every_skip_this_repository_takes_names_a_rubric_category` reads the
categories out of `AGENTS.md` and holds every skip in the repository to them.
All three failed. One had always been `OPTIONAL_DEPENDENCY_ABSENT` --- the Lean
dependency's checkout is not always there --- and said so in words the rubric
did not use, which is the cheap kind of failure. The other two were not cheap.

**None of the eight categories fits a test that does not apply.** The two
remaining skips are on a document that is a dated record of an earlier commit,
whose numbers describe that commit; the test cannot fail, because there is
nothing about today for it to be wrong about. Read the eight in a row and they
are one thing eight times: an absent capability, dependency, service,
architecture, device or privilege, a defect quarantined, a duration excluded.
Every one is a reason the measurement is unavailable. Not one is a reason the
*subject* is. Those are different, and the difference is the same one this
document found when a cited path turned out to be cited because the file does
not exist: a claim can fail to hold because it cannot be checked, or because
there is nothing there to check. A checklist that does not cover the cases in
front of it cannot be satisfied honestly, only quietly, so the rubric gained a
ninth --- `DATED_RECORD_BOUNDARY` --- in both documents that state it.

`test_the_skip_rubric_is_stated_the_same_way_twice` holds the two statements
against each other. They had not drifted in the names, which is what a category
is; six of the nine glosses are worded differently between the documents, and
that is prose. The template carries one entry the other does not, and it is not
a category: `NOT_APPLICABLE`, the box a pull request ticks when it skipped
nothing. Counting that as a category would make "every skip names one"
satisfiable by a run with no skips in it, which is how a checklist item becomes
a formality. The third,
`test_the_rubric_categories_the_skips_use_are_ones_that_apply`, requires a
named category to be one the source can show --- a claimed
`QUARANTINED_DEFECT` with nothing quarantined reads as disclosed and is worse
than an undisclosed skip.

The reader is the syntax tree, not the text. A skip is a call and a decorator,
not a line, and a reason built at runtime is not one a reader of the source can
check --- so a non-literal reason is itself a failure to disclose, by the same
argument that makes an unstated category one.

Three hold the invariants the policy says must survive refactoring.
`AGENTS.md` §5 lists four things no cleanup may quietly remove. They are the
strongest self-descriptions this project makes, because they are the ones it
promises about its own future. Two of the four were already false when read,
and the third was true in a place nobody had said.

**A number no subset reconstructs.** §5 says "keep the source assumption
inventory matching `_baseline.py` exactly (18 kernel axioms)", and §1's table
row says the same. `AXIOM_DECLARATIONS` in `_baseline.py` holds sixty-one, and
`lean4/Hypermath/` declares exactly those sixty-one with the `axiom` keyword
--- the symmetric difference is empty. The two sides of the sentence agree
perfectly with each other and neither agrees with the number standing in front
of them. That is the worst kind of stale, because there is nothing to find by
looking: twenty-one declarations are `ax`-prefixed, twenty-three with the
filtration pair, thirty-five are definitions, eleven are L0's logical clauses,
and none of the readings is eighteen. The count was right about something once
and the sentence outlived it.
`test_the_axiom_count_the_policy_states_is_the_inventory_it_names` holds
the stated number to the inventory and the inventory to the Lean sources,
so the next time one of them moves the sentence has to move with it.
`policy_errors` in `_reports.py` is the arbiter
--- it compares what it reads out of Lean against `AXIOM_DECLARATIONS`, which
is therefore what a kernel axiom *is* --- so the failure was never in the
mechanism, only in the prose describing it, sitting in the document that tells
this suite what to do.

**A check that runs and is not described.** §6 says what
`scripts/check_presentation.py` checks and named four of the five it runs.
`check_lineage_claims` rejects phrases that silently upgrade recorded ancestry
into causality; it has run in CI as long as the other four; nothing mentioned
it. `test_the_presentation_gate_lists_every_check_it_runs` requires the section
to name every check the script calls.
An unlisted check is the exact mirror of an unheld rule: the increment
before this one found a rule stated and not enforced, and this is a rule
enforced and not stated. Both are a gap between what this project does and
what it says it does, and only one of the two is usually called a bug.

The first reader for this matched a description to a check by the words in the
check's name, and reported four of five unlisted --- `check_versions` against
"version agreement" fails on a plural. A reader that fuzzy cannot distinguish
a missing description from an unlucky one, so §6 now cites each check by name
in code style and the guard requires the citation. Naming the thing is cheaper
than describing it well enough to be recognised, and it is checkable.

**An invariant true where it is load-bearing and false where nothing looks.**
"`.gitattributes` forces `eol=lf`" is, on the disk, false right now: twenty
tracked files carry CRLF, among them `LICENSE`, `L0_ground.hm` and every
`docs/terms/*.md`. Nothing sees it. Git reports them unmodified because it
normalizes on read, and Python reports them as LF because text mode translates
newlines, so this entire suite can read those files all day without one byte
of CRLF reaching it. It does not reach the release either: the archive is
built by `git archive`, which reads the index, and `_normalize_newlines`
handles the rest.

So the sentence is a claim about the index and had been read as a claim about
the working tree.
`test_the_line_ending_invariant_holds_where_the_release_reads_it` states
which one it is rather than leaving the distinction to luck. In the
index the invariant holds, and its exceptions are marked rather than tolerated: the only files whose index bytes
are CRLF are the imported snapshots under `references/precursor/`, which
`.gitattributes` marks `-text` precisely so that normalization cannot touch
them --- they are pinned by sha256 in their own manifest, and a normalized
snapshot is a different file. An exemption that names itself in the same
document as the rule is not a hole in the rule. An exemption discovered by
reading the disk would have been.

How the twenty got there is neither a mystery nor history. Writing one of
these files back through Python's text mode on this platform rewrites
every line ending in it, and four files were converted that way while this
entry was being written --- including this one. Nothing reported it: git
showed them modified only where they had been edited, the suite read them
as LF, and the index never saw a carriage return. The drift is constant,
silent and confined to the place where it does not matter, which is the
argument for saying which place the sentence is about rather than widening
the guard until it catches weather.

Six hold the language the layers are written in.
`L0_ground.hm` through `L3_ordinatics.hm` are the specification the Lean
development formalises, and until now nothing in this suite had ever opened
one. They were the input to a sha256 in the audit and a filename in a fixture.
Every other guard above holds a document to the Lean sources or the Lean
sources to a document; the four files in between were held to their own bytes
and to nothing else.

So a document could name a layer axiom that no layer declares, and nothing
would say so. Three did. `docs/terms/` cited `ax-sem-nec`, `ax-sub-nec` and
`ax-syn-nec`, and the search for them ends in the commit that added the
dictionary: they were short forms written in prose for axioms whose real names
are `ax-semantics-requires-syntax`, `ax-substance-requires-semantics` and
`ax-syntax-requires-substance`. Every sentence around them was true. The
triangle is the triangle, each cited edge is the edge its declaration states,
and the only thing wrong was that the names did not exist.

Reading the language is the whole repair, and reading it meant getting the
grammar right in both directions. A reader that knows only `axiom` misses the
eighty-five names `derive` introduces and reports them as undeclared. A reader
that matches names anywhere in the text finds `ax-syntax-precedes-semantics`,
which exists only in the comment recording its own retirement, and reports it
as declared. Neither is the smaller mistake, so the grammar is held first:
`test_every_statement_in_the_layer_language_is_one_the_reader_knows` requires
every left-margin line to be a form the table knows and to yield the name that
form introduces. That is the anti-vacuity condition for the two guards resting
on it, both of which answer "nothing is missing" for free if the reader cannot
see the statement that declares it.
`test_every_layer_name_a_document_cites_is_one_a_layer_introduces` then asks of
every Markdown and Lean file whether the layer names in it resolve, and
`test_a_name_a_layer_retires_is_not_a_name_a_layer_introduces` keeps the
retirement comments meaning something: a name recorded as gone and still
declared makes the comment a description of a rename that did not happen.

The fourth holds the dictionary to the form the dictionary states about itself.
`docs/terms/__template__.md` names the sections an entry has and twenty-one
entries follow it exactly, which is worth holding for the reason any hand-kept
form is: it stays kept until it does not, and the entry that breaks it is the
one nobody checks.
`test_the_dictionary_keeps_the_shape_its_own_template_states` reads the shape
out of the template rather than repeating it, so changing the template changes
what the entries must be.

The fifth came out of the same reading and is not about the layers at all.
`L0_ground.hm` said "The five axioms" and then named seven of them, in the same
sentence, ninety lines above the block that calls them "Seven Section VIII
axioms". No audit is needed to catch that and none of the counters above would
have: they hold a number against a measurement, and this is a number standing
next to its own evidence.
`test_a_count_that_introduces_a_list_is_the_length_of_the_list` reads the
cheapest checkable claim in the repository --- a count, the noun it counts, and
the list in the parentheses immediately after them.

Where the phrase begins is its whole difficulty, as where it ends was the
difficulty one increment ago. "three statements with one inert binder and one
clause implied from beneath (`alpha`, `beta`)" cites two witnesses for a
compound claim, and the count nearest the parenthesis is not the count the
parenthesis belongs to; when more than one count stands in the clause the
binding is ambiguous and the reader declines it rather than guessing. And the
guard passed on the real defect the first time it was written. Wrapped lines
are joined with a space, which carries a layer comment's marker into the middle
of the list, where it makes a name look like prose and the claim disappears
entirely. Blanking that marker without changing the length of the text is what
made the list readable while keeping the reported line number true.

How far that reader gets was not written down, and is four. Sixty-four spans
match its pattern across a hundred and five files; fifty-two hold fewer than
two items, four hold something that is not a bare name, three carry a second
number in the clause and one sits inside a quotation. The guard asserts only
that nothing disagrees, so a reader that matched nothing at all would satisfy
it in silence --- the failure this document exists to record, one level up from
the prose. Its reach is now pinned per file type, so emptying one surface fails
while the others still compare.

The sixth reads the symbols rather than the names, because the language cannot
declare one. Every introducing form here introduces a word, so an operator
written infix has no line that could declare it, and the two that exist have
none. `L3_ordinatics.hm` closes with a note saying so: that Section I's permit
and the Section IV banner both announce them, and that no primitive, opaque or
relation line introduces either. The note is prose, so nothing failed when it
stopped being true --- and it can stop being true in two opposite directions,
which is why holding it needs a table and not a search for the sentence.
`test_every_operator_the_layers_use_is_declared_or_disclosed` keeps the two in
step. An operator that acquires a declaration drops out of the undeclared set
and the table is stale until it says so; an operator whose last use goes away
stops being used and the table is stale until it says that instead.

The two are different kinds of open, and that difference is the finding. One of
them is applied on five lines that are not comments, one of them step 3 of
this file's only close of a lower layer's residual, asserting there that it is now
available from Section IV --- which declares two opaques and three derives, and
neither operator. So that close, and the discharge of the composition-length
frame beneath it, rest on a symbol nothing introduces. The other is announced
twice and applied nowhere, which costs nothing to retire. Declaring the first
is a decision about the language rather than a repair, so the guard holds the
disclosure where the note held it alone, and leaves the decision where it is.

One holds the same claim set out down the page.
A list under its own heading is the same claim in the punctuation a document
uses when the items are sentences, and the reader above cannot see one: it
wants parentheses. `CONSTRUCTIVE_QUINE_SELF_CLOSURE.md` announced two rigorous
boundary results over a numbered list of four, and referred to the fourth by
number further down the same section --- so the list had grown twice, the prose
around it had followed, and the number introducing it had not.
`test_a_count_that_introduces_a_set_out_list_is_its_length` reads that shape.
Three such lists exist, all in the notes; no Lean docstring or layer file sets
one out this way.

What makes the shape safe is that the list is set out beneath it. Inline, a
colon does not bind its noun to what follows: `README.md` says "across two
models" and then names five declarations, which is correct --- two models, five
declarations --- so a reader taking an inline colon as introducing the count's
own list reports a defect that is not there. Measured before the guard was
written, that reader found exactly one disagreement in the repository and it
was that correct sentence.

The colon is also required to end the line, and that was first written down as
the thing ruling the inline case out. It is not. Dropping the anchor leaves the
guard green, because an inline colon has no list beneath it to count, so the
anchor is a narrowing nothing here can currently distinguish --- recorded
rather than claimed, which is cheaper than leaving a reason nothing tests. The
rule the guard above uses for ambiguity had to be dropped here for the opposite
reason: it declines a clause carrying a second number, and applying it would
have declined the real defect on the strength of the words "Lean 4".

One holds the claim that a count is the whole clause set.
The reader that holds clause counts in the notes reads markdown and nothing
else. The same claim is written in Lean comments and in the layer language, and
two sources there put `FullAxiomModel` at a total of thirty-eight where the
sources have thirty-nine --- the drift this module was opened against, caught in
the notes and never looked for anywhere else.
`test_a_total_clause_claim_is_the_measured_total_wherever_it_is_written` reads
the total wherever it is written. Fifty-seven such claims exist: twenty-one in
the Lean comments, thirty-five in the notes, one in the layer language.

Widening the existing reader was tried first and does not work, which is worth
recording because it is the obvious move. Pointed at the Lean comments it
reports four spans and not one of them is a defect. Two are subset counts
written in digits, which is legitimate and which the markdown happens never to
do: the fourteen clauses of `PrefixAxioms` left once the ten closes are
removed, and `prefixWithOperations_iff_conditions` reaching thirty-one of them.
Two are numbers its forty-five character window reaches across to a noun they
were never attached to --- a line number, and the size of a reduction. So the
set of counts the prose may name reads as a fact about this project and is a
fact about one file type, held up by an accident of how the markdown happens to
be written. A rule can be enforceable on the files it was written for and
unenforceable on the files that carry the same claim, and nothing about the
green guard says which it is.

What ports is the word "all". It makes the sentence a claim about the whole
set, so the only counts it can name are the two the sources support, and that
holds in any file. The count may be spelled out: this document writes all
thirty-nine clauses in words, and a digits-only reader would have left the one
spelled total unread. Words are safe to admit because the table of number words
stops at twenty while both permitted totals are larger, so a numeral that table
can express is a subset by construction. The guard asserts that relation rather
than assuming it, so moving either constant fails instead of quietly widening
the skip. Two things are not claimed. A subset spelled out is not checked at
all --- there are four, all correct, and telling one from a total needs the
sentence parsed rather than the numeral read. And the reach is pinned as floors
rather than to the number, because fifty-odd claims across living documents
would fail on correct edits and teach the next reader to retype a number
without reading it, which is the habit this module exists to break.

Three hold the census a layer keeps of itself.
Every layer ends with a self-kernel: a numbered walk over everything the file
declared, with the closure status of each. `L0_ground.hm` describes it as a
census that does not compute but manifests, and then says the sentence that
made these guards necessary --- that a future parser can evaluate the block
mechanically against the file. None ever had. It is a hand-written index of a
file kept beside the file, which is the oldest way a true document goes stale,
and its length is restated in the layer header, in the section banner, in the
closing block and again in the Lean file that formalises the layer.

Three of those copies had drifted, and each drifted alone with the correct
value standing elsewhere in the same file. `L2_operations.hm` indexed its own
section as a census of 29 steps eleven lines below the line saying the census
is 42, which the file goes on to repeat twice, and the census has 42 rows.
`L3Ordinatics.lean` opened by saying 18 and closed its own self-kernel section
by saying 20, which is what its source says and what its source has. And one
census row accounted for a derive under a name one word short of the name the
layer declares, so the row pointed at nothing --- the dictionary defect from
the increment before this one, found in a file's index of itself rather than in
a document about it. None of the three was wrong about the mathematics. The
rows are right and the layers declare what the rows say they declare; the
artifact just did not have the 29 steps, the 18 steps, or the name.
`test_every_stated_census_length_is_the_length_of_the_census` counts the rows
and holds every restatement to them, in the layers and in the Lean sources
both, which is the first guard here to read a claim on one side of that seam
against evidence on the other.
`test_the_census_accounts_for_every_entity_its_layer_declares` takes the claim
L0 writes down in so many words --- that every entity declared in the file is
accounted for above --- and holds all four layers to it, since a census whose
whole content is a list of what the file declared makes that claim by being
one. The census derive itself is the single exclusion, uniformly, because a
census cannot appear in its own walk of what came before it.

One asymmetry is recorded rather than repaired.
`test_no_further_layer_demotes_its_census_to_commentary` exists because L2
indexes its self-kernel as a section like the other three, calls it the closed
structural census, and writes all 39 rows inside comments: there is no
statement to close, and the language has no record that the layer censused
itself. Turning those rows into a statement would be writing specification
content, which is not a guard's to write, so the guard asks the smaller
question it is entitled to ask --- whether any further layer has gone the same
way --- and a control confirms it stays green if L2 is repaired and fires if
the repair is half done, a carrier standing over rows that are still comments.

Both of this module's readers were wrong in the direction that reports a clean
file. The section banner was matched without its colon, so the reader began at
the layer header's prose mention 550 lines earlier and counted every proof step
in the file as a census row: 58 in L0, where the census has 41. And the
census was read to the end of the file, so a declaration added after it counted
as accounted for by it --- the guard passed a mutation that was exactly the
defect it exists to catch. A census is what stands in its rows, and a row runs
until the next row or the next statement.

Three holds the ledger the layers keep across each other.

A census row marked FRAME is a forward dependency stated out loud, and the
layers are explicit that naming one is the honest thing to do: a file with all
its FRAMEs named is better than a file with hidden gaps. A later layer pays one
off by citing the row that opened it --- `Discharges L1 step 10` --- and L3
closes with a register listing every FRAME it discharged. That citation is a
pointer into another file's numbered index, written by hand, and a numbered
index is renumbered whenever material is inserted into it.

Ten of those pointers had gone stale, in two clean groups. L1's census has 25
rows, and L3 cited L1 step 26 and L1 step 30 four times each --- both past the
end, and both off by exactly five. L2's census grew by eight rows when
abstraction was added, the same growth that left its section index claiming 29
steps until the previous increment repaired it, and L3 cited L2 step 24 for
`composition-length-additive`, which is step 25, and L2 step 30 for the
congruent-path internals, where step 30 says in so many words that it has no
FRAME and step 37 is the close that carries the residual.

Nothing was wrong about which obligations exist or which layer paid them. The
rows are right, the discharges happened, and every parenthetical named its
target correctly --- each one quotes its row almost verbatim, which is how all
ten were resolved without guessing. Only the numbers pointed elsewhere.

`test_every_row_another_layer_cites_is_a_row_that_layer_has` asks the part no
reading can argue with: a census with 25 rows has no step 30, so a citation of
one is not a row described wrongly but a row that is not there. It reads the
layer files and the Lean sources both, because a row's number needs no
translation to be checked and the Lean side cites these rows eleven times in
one contiguous hand-written run.
`test_a_cited_row_is_about_what_the_citation_says_it_is_about` takes the other
two: a parenthetical naming something the cited layer declares says which row
is meant, so the row it points at has to be the row that names it too. A
parenthetical that only describes is prose about the row and is held to
nothing. That guard reads the layers alone, because a Lean source names its own
declarations in its own spelling, and `definitionOfGround` cannot be matched
against a census that spells it `definition-of-ground` without a
transliteration the guard would have to invent.

`test_the_other_census_parameters_agree_with_the_layers` finishes what the
census length started. Three parameters are restated across that seam by hand
and only one of them had ever been checked. The count of atomic entities a
layer introduces is now held to being one number rather than several, and to
the list beside it wherever a list is given; the count of graduation conditions
is held to the conditions the layer's own graduation block states by name. L3
graduates to terminal with no conditions at all and never states that count,
which is why the guard holds what is written rather than what could have been.

One discrepancy is recorded and not repaired. `definitionOfGround` is cited as
L0 step 24 in four places, twice in the Lean sources and once each in the
changelog and this note; the census puts `definition-of-ground` at step 41, and
step 24 is the graduation status, which carries no FRAME. The citation is
certainly not step 24 as the census numbers it, and nothing written down says
which row it is. Replacing a reference that visibly points at the wrong thing
with one that invisibly does is the worse trade, so it stands. Neither guard
fires on it, and a control confirms that removing it changes no verdict --- the
scope is a reading decision and not a way of keeping a red out of the suite.

The reader that had to be got right this time was the row boundary. A census
row runs until the next row, and a reader that let a row run on into its
neighbours found every name it was looking for somewhere nearby and reported
the ledger clean. The control ran that mutation against the very defect the
guard exists to catch, and watched it pass.

Three holds the promises and the claim that they are all.

The increment before this held the paying side of the ledger: a discharge must
point at a row that exists, and at the row it says it does. This holds the
opening side, where a layer keeps its own inventory of what it leaves undone
--- and does not merely keep it. L1's closes with a sentence about itself.

> No entity unaccounted.  No FRAME hidden.

Exhaustiveness is the hardest claim to keep by hand, because nothing goes wrong
when an item is left out. Every sentence in the inventory stays true. The list
is simply not all of them.

L1 opens four residuals, at steps 10, 21, 22 and 25, and its inventory names
three. The missing one is step 22, `opaque(D)`, whose row reads FORM for the
schema and a residual at L3 for the content --- the same shape L2 uses at step
6 for `compose` and step 7 for `congruent-path`, both of which its own
inventory lists and one of which L3 discharges by name. Step 22 appears in no
inventory and in no discharge register, at either end.

It is not repaired, and the reason is that the repair is not determined.
Everything else in the stack says `D` belongs to L1: the declaration gives its
reading in full, a trace-sequence from x to y maintained at `=~` or above, and
marks it orbital to L1; L1's inventory says so twice, in the header and in the
closing block; L3 says in so many words that the matrix is defined at L1, and
its register neither discharges the residual nor lists it as remaining. Four
places say L1 and one census row says otherwise. Listing it would assert a
residual that four places deny, and clearing the row would assert a closure
that nothing states. Which of the five is wrong is a question about the
specification, so the gap is written into the guard instead of into prose,
where a control confirms that repairing it from either end leaves the guard
green and that a second gap does not.

`test_a_layer_naming_one_of_its_own_rows_names_a_row_it_has` reads a surface
that had none. Inside its own file a layer cites its rows without the prefix
--- `step 10`, not `L1 step 10` --- because the file is already talking about
itself, and the cross-layer reader cannot see one of the thirty-six. Being in
range is all that is asked, and it is the part a renumbering breaks first.

`test_an_inventory_cites_only_rows_that_open_a_residual` is the soundness half:
an inventory of promises whose members are promises. It is the half that breaks
visibly, because an entry pointing at a row that opens nothing claims a promise
the layer never made.

`test_no_further_residual_goes_unlisted_by_the_layer_that_opens_it` is the
completeness half, and it is asked only where it can be asked. L1 is the one
layer whose inventory cites its rows by number. L0 documents its eight
residuals as two descriptions and L2 its seven as five, and a description
covers as many rows as it covers; matching one to the other is a reading and
not a measurement, and a reader that guessed would be wrong in both directions
at once. What the survey found by hand and this note records rather than
guards: L2's inventory omits `path-trace` and the `compose` internals, and L3
accounts for the first among its non-blocking residuals and for the second only
through the length law that `composition-length-additive` asks for.

Four readings had to be got right, and three of them are about where a phrase
stops. A reference belongs to another layer when a layer identifier stands
close in front of it, and the window has to allow words between: L1 cites L0's
self-kernel step 40, and a reader wanting the two adjacent takes that for a
claim about L1's own twenty-five rows. An inventory heading is the word
followed immediately by its colon, because L2 labels three census rows as its
residuals and a looser reader takes those rows' own numbers for an inventory of
them. Payment is the verb and not the statement form: `discharge` is also a
declared name, and matching it loses six of L0's eight. And the fourth was a
filter watching for nothing --- three rows say they have no residual, not one
of them names a layer to close it, so requiring a named layer already excluded
them. What is held now is the thing that would make it matter, that a denial
and a target never meet on one line, since the day they do the reader starts
taking a denial for a promise.

Three holds the grant and the copy kept of it.

Each layer closes by handing the next one a lettered grant, permits and
prohibits, and the receiving layer opens by keeping a copy of it under a header
that says what the copy is for.

> Copied from L1 graduation block for traceability.

That sentence is a claim about the block beneath it, and it is the only thing
that makes the block worth reading: a copy is traceable exactly insofar as it
is a copy. Nothing inside one of these blocks ever reads as wrong, because
every sentence in it was true somewhere. The question is only whether it is the
sentence that was granted, addressed to the layer that was bound. Six grants
stand in the four files and four copies are kept of them, and comparing the two
clause by clause found three ways it was not.

The first is the one worth the increment. L2 forbids L3 three things and L3's
copy of them runs (a), (b), and stops. The missing clause is separate
classification machinery --- and L3 *obeys* it. "The self-kernel pattern (L0-L3)
IS the classification machinery," it says at line 478, and again at 611, and
its own census closes the question as CLOSED at 730. The constraint is alive in
the body of the layer and absent from the layer's list of constraints. That is
the whole species in one instance: the artifact does the right thing and stops
saying that it must. Nothing is false anywhere, and a reader who wanted to know
what L3 may not do would have been told two of three.

The second is a sentence addressed to the wrong layer. Inside L2's copy of the
grant that binds L2, clause (a) read "L3 may NOT assert: a + b == b + a" where
L1 wrote "L2 may NOT assert commutativity for `'+'`". The sentence was true.
L3 may not, and L2 says so itself, in the block that binds L3, where the
prohibition belongs and where L3 duly copies it. But a prohibition addressed to
the wrong layer binds nothing at the layer it was written for, and the clause's
own next words --- "Commutativity is prohibited at L2" --- disagreed with its
subject inside a single line. Both of these are repaired, because in both cases
the granting layer says in full what the copy should have said, and the
receiving layer already behaves as though it had.

The third is recorded instead, and it is the largest. L1 permits L2 four
things; L2's copy keeps the first two and substitutes the last two. L1 grants
the quant family and free use of filtration. L2's copy grants `compose` and
finite structural operations. The substitution is not idle in either direction:
L2 *uses* both grants its copy dropped, spending `quantification` and `quanta`
throughout its congruent-path close and citing the filtration chain by name ---
and `compose`, which the copy reports as granted, is granted by nobody. The
string occurs nowhere in either layer beneath it, while L2's own grant to L3
leans on it, permitting L3 to close `simulation-pair-exists` "using compose +
ordinal continuation". So the chain of grants has a link that begins in the
middle. Making the copy a copy would delete the only sentence in the stack that
says `compose` is permitted; leaving it leaves the header's claim false. Which
one the specification wants is a question about whether L1's grant should reach
`DerivationPath`, and that is a question about the theory rather than about its
bookkeeping, so it is written into the guard as a pair of clause addresses and
a control confirms that repairing it from the copy's end leaves every guard
green.

`test_every_clause_a_layer_grants_is_a_clause_the_next_layer_copies` asks only
about letters, and letters were enough for the first finding. It also holds
that a copy sits in the file of the layer it binds and names the layer below it
as its source, and it records the one grant that no layer copied at all: L0's,
to L1. The copy convention starts at L2, and whether L1 predates it or skipped
it is not decidable from the files --- L1 has a Section I and it holds axioms.

`test_a_copied_clause_is_about_what_the_clause_it_copies_is_about` is the
quieter half, the one that cannot be seen by counting, because the letters
agree while the text underneath them is substituted. A clause and its copy have
to share one distinctive token, and the reader has to be shown able to tell
clauses apart at all or sharing proves nothing: of the fifty pairs made by
setting a clause against the other letters of its own copy, thirty-three share
nothing, and a reader generous enough to match those would be matching
scaffolding. One reading had to be got right and it is a small one. Words are
compared exactly and never stemmed, because `operation` and `operations` are
the only two tokens standing between L1's clause (d) and L2's, and a reader
that stemmed would close that divergence without noticing it had.

`test_a_prohibition_binds_the_layer_whose_block_it_stands_in` reads the deontic
form and not the mention. A clause may name another layer perfectly correctly
--- "those belong to L3", "prohibition carries forward from L2" --- and a
reader that took any mention for a binding reports four defects that are not
there, which a control shows by making it do exactly that. What binds is the
verb with a subject: twelve such sentences stand in the four files, eleven of
them always bound the layer whose block they stood in, and the twelfth is the
one repaired above.

Two terminators end one of these blocks, a blank line and the header of the
next, and in these four files they are redundant: every block is followed by a
blank line and then a header. The control drops each alone and confirms nothing
changes, then drops both and watches the permits copy run on into the prohibits
copy below it, every clause read against the wrong one. That was the first
reading of this increment, and it reported defects in the loud direction where
there were none --- which is the failure mode to prefer, and the reason it was
caught in an hour rather than kept.

Three holds the header's account of its own sections.

Every layer file opens with a header that is partly an account of the file
beneath it: a list of its sections, counts of what those sections hold, and
sentences saying where a thing declared in one place gets closed in another.
All of it is written by hand, all of it sits directly beside the thing it
describes, and none of it was read by anything.

The finding is in the third kind. Three sentences in `L0_ground.hm` said the
seven executive opaque predicates find their semantic close in Section IX:

> their full semantic close is Section IX.
> opaque declarations here; semantic closes in Section IX.
> OPEN at executive layer (Section VIII closes stated, semantics pending
> Section IX).

Section IX exists. That is the entire reason nothing caught it. Every one of
the fifty-five section references in these four files resolves to a section
that is there, and a reader built to check that a pointer resolves would have
reported a clean file three times over. Section IX is the L0 self-kernel. It
contains no `close` statement at all --- the whole file has three, and they are
in Section VI --- and it says of itself, in its own words, that at L0 "this is
structural verification only (not semantic validation)", deferring the
validator to L1 in the next line. The seven closes are in `L1_relations.hm`
Section IV, which is titled SEMANTIC CLOSES FOR EXECUTIVE OPAQUES, holds
exactly seven, and states that it discharges L0 self-kernel steps 25-31.

So this is a pointer that resolves and lands on the wrong thing, and it stood
against eleven statements of the truth in its own file: the header's FRAME
residual reading "executive opaques semantic content (L1)"; the line
introducing the seven census rows as "Semantic closes deferred to L1"; those
seven rows themselves, one per opaque, each ending "semantic close: L1 pending.
FRAME/L1."; the census close's "Semantic validation: L1 (deferred, dependency
named)"; and Section IX's own "VALIDATOR (L1)". Eleven right, three wrong, and
no contradiction visible anywhere, because the three wrong ones named a real
section of a real file --- the third of them four lines above that section's
own banner. All three are repaired to name L1 Section IV.

`test_a_section_named_as_where_something_closes_is_a_section_that_closes` asks
the thing resolution does not: that a section named as the place something is
closed contains a close. Four pointers stand in these files and all four now
land. The reading that had to be got right is the direction of the sentence.
"Section VIII closes 7 previously informal terms as opaque predicates" is prose
about what a section accomplishes, and Section VIII holds no `close` statement;
a reader taking the subject form for a pointer reports that as a defect, and
the repair for a defect that is not there is to delete a true sentence. The
trap cannot even be set on whole lines, because both forms share one: "(Section
VIII closes stated, semantics pending L1 Section IV)" is a false pointer and a
true pointer inside a single parenthesis. What the control asks instead is that
no pointer anywhere resolves to L0 Section VIII.

`test_a_header_count_of_a_section_is_the_count_that_section_has` reads the
eight numbers the headers write into their section lists and measures each one
against the section it is about: four axioms in L0's Section III, five derives
in Section IV, four necessity constraints in Section VII, seven opaques and
seven axioms and three derives in Section VIII, forty-one census steps in
Section IX, and thirty-nine in L2's. All eight are right. Two of them --- the
census lengths --- were already held from the other end by the census-length
guard in the increment that found L2's index reading twenty-nine, and the
control confirms that guard still fires on the same mutation rather than
asserting it; the other six had never been read by anything at all.

That asymmetry is the whole point. L2's section index once said twenty-nine
against a census of thirty-nine, and it was only because that number had gone
wrong that anything was ever pointed at it. The six that had not gone wrong yet were the six nothing was watching.

The reading here is that a count has no fixed word order and L0 uses both, four
words apart in one list: "III axioms (4)" puts the noun first and "VII
graduation criterion (4 NCs discharged)" puts the number first. A reader that
knows one order finds six of the eight counts and reports nothing missing,
because the two it cannot see it also cannot miss --- which is the quiet
direction, so the control removes the second order and confirms the guard goes
red on the floor rather than passing with a hole in it. The lookbehind on the
first order is load-bearing in the other direction: without it the digits
inside the layer names L1 and L2 read as quantities, and the guard measures
three things nobody claimed and finds all three absent.

`test_every_section_a_header_lists_is_a_section_the_file_has` holds the list
against the banners both ways, in both shapes the four files use: L0 writes its
sections inline in a run of prose, L2 and L3 write a block one section to a
line, and twenty-seven entries are read. One of those entries is VIII.a, and a
reader for roman numerals alone cannot see it --- that near-miss came first this
increment and was a narrow reader, not a defect, which is now the ninth time
the same thing has been true here.

L1 lists nothing. It carries the census parameters and stops. That is the same
boundary the grant-copy convention has, and it falls on the same side: the
convention starts at L2 and L1 is the layer without it in both. Which side L1
belongs on is not decidable from the files, so the absence is recorded as a
set rather than repaired, and the control adds a list to L1 and confirms the
record fails rather than absorbing it.

One thing is recorded and not repaired. L0's note on its own status says
"Current graduation status: ... OPEN at executive layer" at line 568, while the
header five hundred and fifty lines above says "FORM (executive layer)" and the
census a hundred lines below writes a close of FORM. The note's own
parenthesis says why it might be both --- closes stated, semantics pending ---
so this is not obviously an error in the bookkeeping but a question about whether L0's executive layer is FORM on
structural grounds while OPEN on semantic ones. That is a question about the
theory, and it belongs to whoever owns the theory.

Three holds the boundary each layer declares about itself.

Every one of the four layer files says it, in its eleventh or sixteenth line,
in almost the same words:

> Layer boundary: no term from L1 or above appears anywhere in this file.
> Layer boundary: no terms from L2 (operations) or above appear here.
> Layer boundary: no term from L3 (ordinatics) or above appears here.
> Layer boundary: terminal layer. No layer above.

That is the strongest self-denying claim in the stack. The stratification the
whole design rests on --- structure before comparison, comparison before
executive action --- is asserted by each layer about the entirety of its own
text, four times, in four headers. Nothing read it. Not the audit, not the
census guards, not the grant-and-copy guards from the increment before this
one, which read clause by clause the very blocks where it is broken.

It is kept. One hundred and thirty-four names are declared by some layer above
some other layer and not by that layer itself, and across all four files not
one of them stands in a statement of a layer below. Zero. The stratification is
exactly what it says it is.

The sentence is not kept, and what makes that worth an increment is which
sixteen mentions break it. Every single one is in a comment whose purpose is to
manage the boundary. L1 tells L2 it "may NOT introduce ordinal_limit". L2's
graduation block grants L3 `ordinal_succ` and `ordinal_limit` by name. L0 warns
that a derive in L1 requiring `ordinal_limit` is over-reaching, and says
elsewhere that L1 is where `filtration` is introduced. Four are FRAME
deferrals naming what a later layer will discharge; three are locators saying
which layer a term belongs to. A prohibition has to name the thing it
prohibits. A grant has to name what it grants. A deferral has to name what is
deferred.

So the claim, read as written, is refuted entirely by the machinery that
enforces it, and by nothing else. There is no use anywhere --- only the
sentences that prevent one. That is a shape this series has not had before: not
a claim that is false, and not a claim that is unchecked, but a claim drawn so
wide that it swallows its own enforcement.

The three non-terminal claims are repaired to say what the files do: no term
from above in any *statement*. That is not a weakening dressed up as a fix,
because the part of the strong claim that was worth asserting --- that those
seventeen comments are bounding those terms rather than using them --- is
not
left to a sentence. It is held by
`test_a_term_from_above_is_named_only_to_bound_it`, which requires every
mention to stand in a comment that forbids the term, grants it, defers to it,
or says which layer owns it. Five forbid, three grant, eight defer, eight
locate, with overlap; no category is empty, and no two of them take the same
mentions or read a subset of another's. The bound that stood here instead ---
no category covers every mention --- is implied by that and was the only part
of it anything checked.

`test_no_layer_uses_a_term_the_layers_above_it_declare` is the one that holds
the stratification, and it took two readings to get right. A name the lower
layer declares as well is that layer's own vocabulary, whatever the layer above
does with the same spelling, and counting it produces breaches out of shared
words. And one spelling has to be classified out loud or the guard measures
nothing at all: L2 declares `step` as a primitive, while L0 and L1 both write
"step 25:" at the head of every row of their own censuses. One hundred and
seventy-one such lines against seventeen real mentions. A reader that took the
spelling for the primitive would report the two layers keeping this boundary
best as the two breaking it most, so the collision is named and the reason
given, and the guard runs the reader without the collision named rather than
describing what a control once showed.

`test_every_layer_states_its_boundary_and_states_the_one_it_keeps` asks that
each layer state the claim exactly once, name the layer directly above it as
the floor, and state the scope it actually keeps. The control reverts each of
the three repairs in turn and confirms the old wording goes red --- and, more
directly, mutates the reader so that it holds the claim as it was written, no
term from above anywhere, comments included. That goes red on the layers' own
grant and FRAME blocks, which is the whole finding in a single run.

L3's claim is recorded and not held. "Terminal layer. No layer above" cannot be
violated, because there is nothing above L3 to violate it with. It is true, and
it is the one of the four that could never have been false, so counting it as
kept would be counting an empty set as a success. What is asked of it instead
is the opposite: that it name no floor, and that if a layer above L3 ever
appears, the record has to change before the guard passes again.

Four holds the account this repository keeps of the repositories around it.

It keeps two, and until now nothing had read either. Section 1.1 of AGENTS.md is
hand-written and counts itself in words: three tightly coupled adjacent formal
systems and one reference standard, over a numbered list. The family graph under
docs/family is generated, sealed by a sha256 over its own body, five public
nodes and sixteen citation edges, consumed by the pages build and by no test.

They disagreed in both directions and nothing in either was false. The register
named the verifier standard, which the graph has no node for, correctly, because
its nodes are fields and that is a standard. The graph had a node for hyperlogic
with an edge running into this repository, and the register did not mention it
at all. And a note written the day after the graph was sealed cited hyperlogic
by name, which made an outbound edge the graph does not have. A generated census
went stale the moment one new document was written, and the seal is over the
body, so it cannot be repaired by hand.

That note is what forced the increment, because it arrived as three unrelated
red guards at once: the layer-name reader, the cited-path reader and the
clause-count reader, all three reporting the same document as defective. It was
the first document this repository ever wrote about somewhere else, and every
reader in the suite rested on an assumption none of them states --- that a name
or a path a document cites belongs to this tree. True of every document that
existed when they were written. False of a refusal note, whose whole subject is
what is not here.

One of the three was right, and its finding is repaired: the note put the clause
total at 38 where the sources have 39. The other two were reading correct
sentences about elsewhere.

So the exemption is not a list of tokens to ignore. A citation is excused from
resolving here when the paragraph it stands in says which tree does hold it,
and that tree has to be one of the repository's own two accounts, or the
precursor, which is anchored by the commit it forked from and which this
repository can therefore check. That anchor resolves: the commit is here and
its date is the date the note gives. The layer-name reader and the cited-path
reader both consult that reading now instead of reporting absence, which is why
the exemption lives in a sentence in the document and not in a set in a test.

Mention is not enough, and the difference is the whole reader. Every tree in the
register is also a word this repository uses about itself, and one of them is a
clause name, an axiom and a layer file as well. Attributing every paragraph that
merely contains a sibling's name excused seven hundred and four names. Requiring
the tree to be named as carrying, shipping or declaring the thing cuts that to
ten. The word boundary has to stop at the underscore, too, or this repository's
own L3 layer file reads as a citation of the sibling whose name it contains, and
it sits four words from "declares": that one alone excused nine local names.

`test_the_register_of_adjacent_repositories_names_as_many_as_it_counts` adds the
list up. `test_every_repository_the_register_names_is_one_the_graph_has_or_says_it_is_not`
checks the seal first, because comparing a hand-written account against a
generated one means nothing if the generated one can be hand-edited.
`test_every_sibling_this_repository_cites_is_an_edge_the_generated_graph_has`
is the one that caught the staleness, and it caught it on its first run. The
missing edge is pinned with its reason rather than invented, because the graph
is built by a tool outside this repository; what the pin buys is that a second
omission is a failure instead of a silence. And
`test_a_citation_that_does_not_resolve_here_names_the_tree_that_holds_it` holds
the attribution itself: the two citations three readers called defects, the tree
each of them lives in, and the fork commit that makes one of those trees
something this repository can still check something about.

Four holds the regions a declaration is read from and the count above them.

The Lean sources are read by declaration: a comment block, then a body. Two
readers decide where that region begins and ends, and they were wrong in
opposite directions. The walk upwards stopped at the first blank line, which in
a paragraphed Lean docstring is inside it. The walk downwards ran to the next
declaration, which swallowed the next one's docstring and every section banner
in between. Too narrow above, too wide below, so every declaration still came
back with prose and none of it looked wrong. In this tree 795 of 1985 regions
overlapped the region after them.

What that bought was an accident. An admitted declaration must say what its
admission is: independent, open or underivable in words, or else discharged
elsewhere by a named declaration that is not itself admitted. Every admission
in the tree carried one of the words, so the guard never reached the pointer,
and the part of the pointer test that refuses a witness which is itself
admitted never ran at all. A disjunction whose second arm is unreachable states
more than it holds.

And one admission was carried by the overlap. `definitionOfGround` says nothing
about independence; it says it is admitted at its own layer only and proved at
`definitionOfGround_L1`, which is the second thing an admission may say, not
the first. It passed the word test on "independent" taken from a section census
about `derivesIsDirectional`. Both texts are correct. The reader joined them.

With the regions repaired every declaration is read from the line its docstring
opens on and no line is read twice, seven of the eight admissions state a word
and all eight name a witness, and the pointer arm carries a real admission for
the first time. `derivesIsDirectional` gains its two models, which its closing
sentence had been pointing at from outside the readable region;
`congruentPathInternals` goes from six resolving names to twelve.

`test_no_two_declarations_are_read_the_same_line` holds the partition, and it
is the one that would have caught either defect on its own.
`test_a_docstring_is_read_from_the_line_it_opens_on` holds the upper edge
against a subtler regression: a region can be disjoint from its neighbours and
still begin in the middle of its own docstring.
`test_every_admission_names_a_witness_that_is_not_itself_admitted` asks the
second arm of the rule directly of every admission rather than only of the ones
that fail the first, which is the strongest thing true of them and was never
the thing being checked.

The module that reads those regions opens its docstring by saying how many
invariants it holds, and that word went from four to seven in this increment
with nothing watching it.
`test_a_module_that_counts_its_own_invariants_counts_them_right` reads the word
against the list beneath it. The reader is general and finds one list today, so
it asserts that it found one at all: a count guard that passes because it read
nothing is the failure it exists to prevent, and this series has already found
that shape twice elsewhere.

Four hold the audit's census of its own checks.

`lean4/README.md` has twice been a correct count of a smaller audit. It said
"seven required processes" when the audit ran seven, and was still saying it when
the audit ran twelve. The repair rewrote the sentence to "fourteen checks" over
the twelve it then ran and the two it derives, and the entry above records that
as done --- which is the only thing that ever checked it. Nothing was left
reading the file, so the same body of work that took the audit to fourteen
processes and sixteen checks put the sentence wrong again before it was ever
committed. Fourteen names under the word "fourteen", every name a real check,
and the set wrong twice over --- so every count guard here passed over it,
because they hold a number against the list beside it and here the list was the
error.

`test_every_list_of_the_audit_checks_is_a_list_the_audit_has` asks the question
of every document rather than of the one sentence the first repair was written
against. A run of names in code style that are all checks is the audit's list of
checks and has to be a list the audit has; a sentence naming only some of them
says so in the words it would use anyway. The other file carrying that sentence
was the guarded one, which is why the second drift ran in plain sight.

`test_a_number_in_front_of_the_word_process_is_one_of_the_measurements` holds
the numbers with no list beside them. The note above said ten where the source
has twelve, in the present tense, and said `docs/verification.md` carries ten
sizes where its table has twelve rows. Both are measured now. The reader cannot
tell a claim from a record, which the guard states rather than leaving for
whoever writes the next boundary note to find from a failure.

`test_every_check_the_report_carries_is_named_in_a_document` is the mirror at
the level of the check. Every dependency group had to be written down somewhere;
the checks themselves did not, and the two the audit derives were named in no
sentence of the document that says what a completed execution requires --- while
one of them is the check expected to fail and the other decides the gate beside
it. That document now names them and says why a completed execution is
consistent with a failing check in the same report. `CHANGELOG.md` is not read
for this, on the same ground the roster gives for not reading it: an entry keeps
the names its release had, and a check named only in an entry is one nothing
current describes.

`test_the_failure_handler_walks_the_order_the_run_uses` closes the one that is
not about prose. The audit keeps two orderings of the same names in one file:
the table it runs and the tuple the report is seeded from. When a probe returns
evidence the audit rejects, the handler names the failing check as the last
attempted one in the report, which is the seed's order and not the run's. They
agree today. A name moved in one list and not the other would charge the error
to a check that ran and passed, whose exit code, output and reasons would all
still say it succeeded. Nine existing tests pin parts of that agreement by
accident, because each raises from inside a probe and names the check it expects
to fail. Measured over every adjacent exchange of two names in the seed, those
nine catch ten of the thirteen. The three they do not catch are the exchanges no
test raises across, and the last two entries are among them --- those can be
exchanged with all of `tests/test_audit.py` still passing, which is how a
divergence of exactly that shape would arrive unannounced.

Three hold the prose the sources carry about themselves.

Every count and name guard listed above reads `docs/**/*.md` and `README.md`,
and `lean4/` carries 3,586 lines of comment prose, 857 of them inside doc
comments that are rendered as this project's API documentation and are the
first thing a reader of the sources meets.

That prose was not unread, and the first draft of this entry said it was. Five
guards reach into it, each keyed to a narrow trigger: a line carrying the word
"discharge", which is 52 of the 3,586; a name qualified by one of this
project's namespace roots; or the prose inside an admission's own docstring.
Between them they reach 55 of the 309 names these comments cite. The other 254
were read by nothing, and a count of what is covered cannot see what is not.
What made that invisible is that no document says the guards stop at the
file-type boundary, so there was no claim to check and no failure to notice ---
the gap was in the shape of the roster rather than in anything the roster says.

Two names had gone stale there. One appeared exactly once in the repository and
named nothing at all; the theorem it meant is `prefixAxioms_iff_conditions`.
The other put `derivesIsDirectional` in the ground layer, where what is
declared is `derivesIsDirectional_FRAME`; the name it wrote does exist, one
layer up. The sentence's own subject was that the two layers admit the same
statement, so naming one of them twice lost exactly the fact being reported.

`test_every_name_the_sources_cite_resolves_or_is_classified` holds the first.
It keeps no list of its own: the five kinds the documents needed --- withdrawn,
superseded, another project's, a value, a binder --- turn out to be the kinds
this prose needs, with not one entry added. Of the 309 names cited in the
sources, eight do not resolve and all eight were already written down. That is
worth recording, because it is evidence the classification is about the project
rather than about the documents, and a second table would have been a second
thing to keep true.

`test_a_name_qualified_by_a_file_is_declared_in_that_file` holds the second,
and it is a rule no guard here had. A dotted name resolves by its last
component, because Lean writes a name at whatever depth the surrounding
namespace makes unambiguous and a reader demanding the full path would reject
correct prose. The cost is that the qualifier goes unread, which is how a
citation can land on the wrong file while every part of it resolves. Where the
qualifier is a file of this project it is now read; 28 names are written that
way. A qualifier that is a namespace is not read, because a namespace spans
files and the question has no answer there, and one name is both: `Hypermath`
is the top namespace and also the stem of the file that imports the layers,
which declares nothing. Thirty-nine of the forty files are read as qualifiers.

`test_no_reader_in_these_guards_is_defined_twice` holds a defect found while
placing the other two. The reader that finds a name set in code style was
assigned twice in one file, narrow at the top and wide 1,847 lines below ---
two definitions of one name, and Python keeps the last of them, so
both ran on the wide one --- including the guard written directly beneath the
narrow definition, whose account of its reader its own module had already
contradicted. Nothing failed and nothing could have, because the surviving
reader was the stricter of the two. The collision was what kept the guard
honest, which makes the ordinary repair --- widen the reader --- the move that
would have opened the hole. So the rule is not about that reader: no name in
these files is bound at module level twice, and a reader can be known by
reading it.

### The last joint: from names to statements

Three tests joined the chain by name, and a name says which clause is meant,
never what it says. Two joints were still unmeasured under that heading.

The first is model to model. The four clause structures were known to declare
the same 44 names; whether they state the same 44 propositions had never been
checked. They do. `FullAxiomModel.FullAxioms`,
`FiniteActionCountermodel.FullAxioms` and `TransportCountermodel.FullAxioms`
agree character for character on every field, and the fourth, `FullAxiomsWith`,
differs in exactly the three clauses that mention `congruentPath` ---
`axComposeAssoc`, `axComposeIdentity`, `axComposeNonempty` --- by exactly the
substitution `congruentPath → cp`. That is the entire difference the
abstraction makes. Nothing else in the list moved to accommodate it, which is
what lets `congruentPath_symmetry_independent` be read as a result about the
clause set rather than about a list rewritten until it gave one.
`test_the_clause_lists_agree_word_for_word` holds it there.

The second is models to the free characterisation, and it was the weakest link
in the chain. Everything proved in this note about the clause set --- the
fourteen contentful clauses, the nineteen conditions, the irredundance of the
eight --- is stated over `PrefixAxioms`, `OperationAxioms`, `ComposeAxioms` and
`TransfiniteAxioms` in `FreeFiltration`. Everything a model is asked to satisfy
is the canonical list. The two were connected by the names of the fields and by
an unverified reading of what those fields say.

`CanonicalAxioms` closes it. Its 44 fields are the fields of
`TransportCountermodel.FullAxioms`, copied rather than retyped and held there by
`test_the_canonical_list_is_the_declared_one`; its parameters are the carrier,
the three relations and the ten auxiliary predicates, so the same statements can
be read at any interpretation. Read at the free one:

> `the_canonical_clauses_are_the_free_ones`: `CanonicalAxioms` instantiated at
> `structContinues ground S`, `structDistinct E`, `structOrbits S`,
> `HMSyntax ground f2f S`, `Substance C`, `Semantics E`,
> `FormClosure ground f2f S C E`, `Derives f2f C`, `Discharge f2f C` and
> `Definition f2f C` is `PrefixAxioms ∧ OperationAxioms ∧ ComposeAxioms ∧
> TransfiniteAxioms`.

The proof is seventy-eight field projections and no tactic, and `#print axioms`
reports no dependency at all --- not even `propext`, which nearly everything
around it picks up from `omega` or `simp`. That is the sharp form of the
result. The two readings are not merely equivalent, and not equivalent by way of
the `close*` clauses that fix the ten predicates: they are definitionally the
same 44 propositions, one at a time. What a model owes is what the
characterisation describes, and stays so under any change that keeps the
definitions.

The chain now reads:

| joint | what connects the two sides |
| --- | --- |
| layers to models | the names of the clauses, checked |
| model to model | the statements, character for character |
| models to the free structures | a theorem, definitional clause by clause |
| free structures to conditions | `all_thirty_nine_iff_nineteen_conditions` |

The first row is the one still made by name, and for a reason worth stating
rather than hiding: the layers write their clauses in the `~~`, `=~` and `≡`
notations, so comparing statements there would be comparing different syntax for
the same relations. Closing that row needs a reader that knows the notation, or
a theorem on the Lean side relating a layer's clause to a model's. It is the
last joint in the chain that a rename could still slip through.

> A count says the two sides are the same size. A name says which clause is
> meant. Only a statement says what it says --- and only a proof says that two
> statements say it of the same thing.

## What the definition route actually buys

The obvious repair is to stop treating `congruentPath` as opaque. Its intended
reading is already written down at `L2Operations` line 72 --- agreement of `p`
and `q` on `(start, end, pathTrace, quantification)` --- and every component is
an existing parameter, so the definition can simply be made. `tupleCongruentPath`
in `lean4/FullAxiomModel.lean` makes it, and three facts follow.

It is consistent: `tuple_full_axioms_hold` satisfies all 39 pre-closure clauses, and
`tupleCongruentPath_iff` shows that in this model the tuple reading *is* the
model's own `congruentPath`, three of its four components being constant there.

Its symmetry is conditional, and on something more basic.
`tupleCongruentPath_symm_of_congruent_symm` derives symmetry of the tuple
reading from symmetry of `=~`, applying the hypothesis once per component;
nothing about paths enters the proof. So the tuple reading is symmetric exactly
when `=~` is.

And `=~` is not symmetric under the clauses. `AsymmetricCongruent` in
`lean4/Countermodels.lean` is a fourth model of all 24 L0 and L1 clauses in
which `1 =~ 0` holds and `0 =~ 1` does not. Three clauses constrain `Congruent`
--- `filtrationSimCong` and the third conjunct of `traceLevels` bound it below
by `Simulation`, `filtrationCongSim` bounds it above by `Similar`, and
`closeSubstanceOpaque` fixes its diagonal --- and not one of them relates
`x =~ y` to `y =~ x`. Equality plus a single ordered pair satisfies all of them:
`congruent_symmetry_independent`, against the Bool model's `Congruent := True`.

So defining the parameter does not remove the missing assumption. It relocates
it from `congruentPath` to `=~`, which is a better place to owe it: one clause
giving symmetry of `=~` would yield symmetry of the tuple reading, of
`congruentPath` under it, and of every other componentwise notion at once. The
one route that does not work is the one the source took --- admitting it and
recording it FORM.

`tuple_reading_consistent_and_conditional` packages the three facts.

## The pointer rot this exposed

Three cross-module pointers claimed a discharge that did not exist.

1. `L1Relations` §II pointed at `L3Ordinatics.simulationPairExists`. That
   theorem was withdrawn when a full-clause model refuted the nontrivial pair;
   it survives only as the unproved `simulationPairExistsClaim`. The weak pair
   it was needed for turns out to need no ordinal machinery at all and is now
   proved outright as `simulationPairExists_L1`.
2. The L3 census, step 16, recorded `driverCycleIsClosed` as FORM discharging L1
   steps 21 and 25. No theorem of that name has ever existed in this repository.
   The claim it names is refuted in both models.
3. The `deriver` docstring said its `≡`-cycle was discharged in `L3Ordinatics`.
   That layer carries only the conditional `driverInDAtSimulationOfCycle` and
   the equivalence `selfDerivation_iff_driverCycleClaim`, neither of which
   proves the cycle.

`tests/test_discharge_pointers.py` now fails the suite if a comment claiming a
discharge names an identifier that is not a declaration, if a
repository-qualified name in prose does not resolve, or if an admission does not
state whether it is independent, open, underivable, or closed elsewhere by a
named theorem that is not itself admitted.

## Counts that are now checked

`tests/test_declared_counts.py` measures the clause and assumption inventory
from the Lean sources and fails if any Markdown file in the repository names a
different number. That closed a drift of twenty-eight "38 logical clauses" and
nine "67 declared assumptions and 11 admissions", against measured values of 39,
61 and 8. `docs/research/PROOF_AUDIT.md` is exempt: it is a dated snapshot of an
earlier commit, and its numbers are history rather than claims about the present
sources.

The production-milestone totals were left alone on the first pass, because
rewriting a number on an inference is the failure this note is about. They are
now measured, not inferred. "Production milestone declarations" names
`PROVED_DECLARATIONS` in `src/hypermath_foundations/_baseline.py`, and the three
commits that introduced the three different totals each set that dictionary to
the number they wrote:

| Commit | Introduced | `PROVED_DECLARATIONS` there |
| --- | --- | --- |
| `6b050fc` | "34 proved production milestone declarations" | 34 |
| `b35b795` | "38 proved production milestone declarations" | 38 |
| `c5de9dc` | "45 production milestones" | 45 |

Three for three on the introducing commits settles the referent. The working
tree has 76 production milestone declarations, and every site that names that
noun says so. The test measures the baseline rather than pinning a literal,
because a new proof is meant to move the total --- and to move the sentences
reporting it in the same commit.

It did, immediately, and three times since. §IV.c adds five theorems and took
the total from 58 to 63; §VI.a adds two more and took it to 65; §VII.a adds one
and took it to 66. Each time the scan named the stale sentences without being
told where to look. That is the difference between a measured total and a pinned
one: the pinned literal would have gone on being right about nothing.

### The one number the scan could not see was in this section

That paragraph used to end "the working tree has 66, and every site that reports
it now says so", and by the time anyone read it again the tree had 68. The scan
did not catch it, and the reason is exact: **the scan binds a number to the noun
it counts, and that number's noun was a pronoun.** "Reports *it*" carries the
referent from two paragraphs earlier, far outside any window an adjacency rule
can use, so the sentence named a measured total and matched no total pattern.
The repair is not a cleverer pattern. It is to make the sentence carry its own
noun, which it now does.

> A number is checkable exactly as far as it is attached to what it counts.
> Anaphora is free in prose and invisible to a scan, so a total that refers to
> its noun instead of naming it is unchecked however many scans run over it.

The sentence also claimed something the instrument could not support. "Every
site that reports it now says so" asserts *coverage*, and the scan measures
disagreement. Those are different properties, and the difference is the second
defect below.

### The scan ran in one direction only

`test_prose_clause_counts_are_real` and `test_prose_totals_match_the_audit` both
fail when a sentence disagrees with a measurement. Neither fails when a
measurement is named in no sentence at all --- and a measurement nothing reports
is one nothing can contradict, so it drifts without limit and the scan stays
green over all of it.

Twelve processes each bind a group of exact dependency reports. Ten of them
existed when this was measured, and four of those ten --- `layered_derivation`,
`full_model`, `record_machine` and `countermodel` --- were
named at their current size in no document in the repository. The six that
*were* reported are exactly the six that had not moved since the note that
introduced them, which is the mechanism rather than a coincidence: each research
note states a group's size as of the boundary it records, the group grows after
it, and nothing goes back. `full_model` was last written down at 63 and stood at
92.

`docs/verification.md` now carries every size as a table generated from
`_reports.py`, and `test_every_audit_group_size_is_reported` requires every
process to be named on some line together with its size. A new process fails
that test until someone writes it down. The check is the mirror of the two
above, and the pair of them is the actual invariant: **no sentence may
contradict a measurement, and no measurement may go unsaid.**

This check would have failed on the countermodel work in this note. That group
went from 45 to 53 across the sections above, and not one of them said so. It
then did fail, on the very next section: the transfinite layer below took the
group to sixty-one and the table said fifty-three until the same commit fixed
it. An instrument that only ever confirms is not being used; this one caught its
author within an hour of existing.

The third pass found two sites the first two had missed, and the reason was a
second coarse guard. A paragraph mentioning what an earlier commit *withdrew* was
skipped whole, so every other number sharing that paragraph was excused with it
--- including two live milestone totals, which had been wrong since §VI.a and
reported by nothing. The exemption is now per sentence. Same failure shape as the
wrapped-field counter above: a guard wide enough to be safe is wide enough to
hide the thing it was guarding.

The scan reads paragraphs rather than lines, and matches a number to the noun
it counts rather than to a fixed phrase. The notes are hard-wrapped, so a number
and its noun routinely land on different lines; a line-at-a-time scan catches
only the ones that happen not to wrap. Together those two widenings found four
further drift sites, including a wrapped "38 declared logical clauses" in the
root README and three worded differently from the phrasing the test knew:
"67 assumptions", "67 reviewed parameter/axiom declarations" and "11 remaining
admission sites".
The "eleven finite-orbit/action results" inside one of those sentences is
deliberately *not* checked: it describes the batch that note introduced, and no
measurement in the repository reproduces it.

`lean4/README.md` said the audit had "seven required processes". Those seven are
the first seven of the fourteen it runs; the other seven were added later and
the sentence was never revisited. It was rewritten to name them all and to say
which check is expected to fail --- and then went wrong again in the same way,
because the rewrite was the whole repair and nothing was left reading the file.
The audit grew by two more checks it runs, and two checks it derives rather than
runs had been counted among those, so the sentence named fourteen of the sixteen
the report carries and wrote "fourteen" over a list of fourteen. Every count guard here passed over it: they hold a number against the
list beside it, and the list was the part that was wrong. The guard written at
the time reads `docs/verification.md`, which was the other file carrying that
sentence, not the file this entry is about.

## What was closed

Two admissions were not gaps at all.

* `simulationPairExists_L1` --- `∃ x y, (x ~~ y) ∧ (x ≡ y)`, witnessed by
  `ground, ground`. It needs `closeSemanticsOpaque` to turn the one asserted
  `Semantics ground` into `≡`, and the two filtration axioms to step down to
  `~~`. That is why it could not be proved where it was stated: the closes are
  declared one layer later, not because ordinal machinery was missing.
* `definitionOfGround_L1` --- `Definition ground ground`, by zero applications
  of forming and `axGroundSubstanceAx`. This is L0 step 24, and its forward
  pointer now resolves to a closed proof.

Both are in `L1Relations` §IV.b, placed after the semantic closes rather than at
the point where the source states them.

## The incidence method run backwards: what a clause would cost

Every result above asks what the clauses give. The last one asks the reverse,
and it is the same instrument pointed the other way: given a proposition someone
might want to state, which of its consequences survive?

`ax-deriver-at-limit` places the deriver at the ordinal limit.
`L3_ordinatics.hm` writes it with `==`, the top relation of the filtration;
`Ordinatics.Transfinite` mechanizes it with Lean's `Eq`. Both consequences the
interface draws from it --- the deriver is at no finite position, and some path
reaches it from ground --- are proved by rewriting along the equation, which is
available to one reading and not the other.

`WeakPositionPrice` states the two replacement routes over an arbitrary carrier,
so that nothing is available beyond what is written:

| Consequence | Route without the equation | Needs |
| --- | --- | --- |
| deriver at no finite position | one transitivity step | `==` transitive |
| some path reaches the deriver | bridge, then turn around, then chain | `==`-into-`=~`, `=~` symmetric, `=~` transitive |

Neither route is deep; both are one line. The content is the third column, and
`the_weak_position_is_unaffordable_here` reads it off against this layer's own
clause set. Exactly one of the four properties is available, and it is the
bridge: `filtrationSimCong` is among the prefix clauses, so it holds in every
model of them. The other three are each refuted by a model satisfying all 24
clauses --- `FreeSimulation.simulation_transitivity_claim_fails`,
`AsymmetricCongruent.congruent_symmetry_claim_fails`,
`AsymmetricCongruent.congruent_transitivity_claim_fails`.

So under the weaker reading this layer loses both consequences too. On the path
consequence it is worse off than the bare interface rather than better: it holds
the bridge and still cannot cross, because crossing needs the far side to be an
equivalence and the far side is free above equality.

**The result is assembly, and that is the finding.** Nothing in
`WeakPositionPrice` is new mathematics. The three refutations were proved
earlier, against a different question, and they answer this one unchanged. What
was missing was the question --- and in its place the source note carried the
opposite claim, that both costs were already paid here, with the refutations
three theorems away in the same file. The incidence method is cheap enough that
an unchecked assertion of this kind has no excuse; the cost of checking it was
an afternoon's reading and the cost of not checking it was a false sentence in a
specification.

The general form, alongside the one about models above:

> A consequence proved by rewriting does not survive a weakening of the equation
> it rewrites along. What replaces it is a chain, the chain has hypotheses, and
> those hypotheses are what the weakening actually costs. Price them before
> claiming a layer can afford them.

### What the count is relative to: a `∀` splits and an `∃` does not

Every count in this note has been a count of fields, and a field is a unit of
writing. Two of the eighteen clauses and two of the seventeen conditions are
conjunctions --- `axComposeIdentity` and `unitalUpToCp` say the unit acts on both
sides, `succEscapes` says the successor is derived and is not equal to what it
succeeds --- so the two sides have been compared in a form that is not normal.
The note's own rule, written three sections ago, says to split a conjunctive
clause before counting it. It had not been applied to the lists the rule was
written in.

Applying it does not mean splitting every conjunction, because not every
conjunction comes apart:

| shape | splits | why |
| --- | --- | --- |
| `∀ x, P x ∧ Q x` | yes | the halves never meet; `x` is re-bound in each |
| `∀ a, ∃ c, P c ∧ Q c` | no | the halves meet at `c`, and only there |

`the_unit_clause_is_two` and `the_successor_clause_is_two` are the first row at
the two places it occurs. The second row is the three operation conditions, and
it needed a model rather than a proof: read similarity as holding only of one
point and congruence only of the other, and every form has something similar to
it and something congruent to it while nothing at all is both.
`WitnessConjunctionDoesNotSplit` is two lines long and it settles the question
for all three.

The file had already found this from the other side and not recognised it as the
same fact. `axLimitDerives` was one clause that left *two* conditions behind,
and `TransfiniteConditions` explains why in its docstring: pinning `pathStart`
and `pathEnd` separated the clause, because the single `p` was the only thing
tying its two halves together. That is the second row becoming the first row the
moment the witness is pinned. What is added here is the converse --- while the
witness stands, the halves cannot be read apart at all --- and it is the converse
that makes the convention a convention rather than an oversight.

So the normal form is: split under `∀`, stop at `∃`. In it the layers are

| layer | clauses | conditions |
| --- | --- | --- |
| prefix | nine | eight |
| operations | three | three |
| composition | four | four |
| transfinite | four | four |
| total | twenty | nineteen |

and `twenty_split_clauses_are_nineteen_split_conditions` is
`eighteen_clauses_are_seventeen_conditions` counted that way. Both sides gain
two. The prefix gains none, because none of its nine is a conjunction; the
operations gain none, because theirs cannot be split at all.

**The counts moved and their difference did not.** That is the useful part. A
count of fields is not an invariant of the content --- conjoining any two
conditions gives eighteen, and nothing stops it --- so *eighteen* and *seventeen*
were never facts about the theory, only about a way of writing it. What survives
the change of convention is the difference of one, and the difference of one is
the triangle against the hub. The reduction from thirty-nine was never heading
for a number. It was removing consequences, and the number was a by-product that
has to be read relative to how the survivors are written down.

### What an axiom report is a report of

The composition group left a rule: **a model depends on no axioms exactly when it
never had to look at a carrier.** It is cited three times in this note as a
prediction that came true, including twice in the sections above. It is false,
and the counterexample arrived in the section just written:
`WitnessConjunctionDoesNotSplit` looks at a carrier, decides two relations on it,
and depends on nothing.

What the reports actually track is the proof's vocabulary.
`AxiomsMeasureVocabulary` is the exhibit: two theorems, the same statement about
the same model, one proved by naming `Nat.succ_ne_zero` and one by constructor
injectivity. The first depends on `propext` and the second depends on nothing,
because that core lemma happens to be proved with it. Nothing between them is
mathematical.

Measuring all of it rather than arguing about it, across the models in the file:

| the model's proofs | axiom-free |
| --- | --- |
| use `omega`, `simp`, `simpa`, `subst` or `rw` | none of them |
| use none of those | all but five |

and of those five, four depend on `propext` solely through `Nat.succ_ne_zero`
and the fifth inherits its dependency from a model it cites, which does build a
carrier. So the rule's predictions kept coming true for a reason that is not the
rule: building a carrier forces automation, automation is what carries the
axiom, and the two travel together often enough to look like one thing. They are
not one thing, and the free reading is where they come apart, because there the
carrier is a variable and every proof is a projection.

This does not make the reports worthless --- a dependency on `Classical.choice`
still marks a proof that chose something. It makes them reports about how a
proof is written, which is why four of the file's `propext` dependencies are
removable by editing one identifier, with no model changed and nothing
reproved. `test_the_axiom_pair_states_one_fact_in_two_vocabularies` keeps the
exhibit honest about its subject: if the two halves ever stop stating the same
thing, the pair stops demonstrating anything.

That test was the only thing watching the pair, and it watches the wrong half of
it. Reprove the expensive half by hand and the two still state the same fact, so
the test passes, and the pair quietly stops being a pair. The sentence that used
to end this section said as much --- *nothing else in the repository would
notice* --- and it was true, for a reason larger than the pair.

**The countermodel group was the only probe group not pinned to its costs.**
Eight of the ten groups compare against an exact dependency table; the
countermodel group asked only that no axiom outside `propext`, `Quot.sound` and
`Classical.choice` appear, which catches an admitted proof and nothing short of
one. So a report's cost could
change and the audit would still pass, once the source digest was refreshed
alongside the edit --- and refreshing the digest after an intended edit is not
an oversight, it is the workflow. A digest detects that something changed. It
does not record what.

The table now records it. One hundred and forty-nine reports in four shapes:

| the proof costs | reports |
| --- | --- |
| nothing | ninety-nine |
| `propext` | thirty-two |
| `Quot.sound` and `propext` | thirteen |
| `Classical.choice`, `Quot.sound` and `propext` | five |

Pinning it makes three things measurable that were not. The first is the
sentence above about removable dependencies, which was a claim nothing could
check. The second is the pair: the audit now rejects the edit that makes both
halves free, and rejects it for the right reason, naming the report whose cost
moved. The third is the shape of the choice principle's footprint. Those five
reports are the limit-adjoined model and everything that cites it ---
`LimitAdjoined.all_nineteen_conditions_hold`, the three models that need a
transfinite condition, and `nineteen_is_not_fourteen_plus_five`. **Choice enters
this file in exactly one construction and reaches exactly what quotes it.** That
was always true and nothing said it, because nothing had written down where the
axioms are.

### Where choice enters, and where the reports decline to say

*Choice enters this file in exactly one construction* is a claim about one
file. Every dependency table in the repository is pinned the same way now, so
the same measurement runs over all of them, and it says something the one-file
version could not.

Thirty reports name `Classical.choice`: five in `countermodel`, eighteen in
`full_model`, two in `observation`, one in `record_encoding`, and four among
the sixty-eight milestone declarations. Twenty-six of the thirty name it
alongside both `Quot.sound` and `propext`. Four name it without either:

| report | what it is |
| --- | --- |
| `Observation.chosenDecoder_correct` | the chosen decoder is correct |
| `Observation.compatible_iff_decoder` | compatibility is decoder existence |
| `finiteOrbitDecode_spec` | the finite-orbit decoding meets its specification |
| `finiteOrbitEquivalence_laws` | the finite-orbit equivalence is one |

What this licenses is narrow, and the section above is the reason to keep it
narrow: reading axiom reports as a criterion produced a rule that was false as
stated. So only the safe direction. Whatever brings `Quot.sound` and `propext`
into the other twenty-six, it is not what brought choice into these four,
because these four do not name it. The converse does not follow. A report naming
all three may need choice for what it says, and the report does not distinguish
that from a proof that reached for a tactic; **twenty-six of the thirty do not
say why choice is there.**

The four that do are the four where a decoding is asserted to exist, which is
where a noncomputable choice would be expected. The reports make that visible.
They do not explain it, and nothing here proves the other twenty-six could be
rewritten without it.

One of the four pairs was already claimed in prose. `docs/verification.md` has
said *24 observation reports: 22 axiom-free, two with classical choice* --- an
exact cost claim, made before there was a table that could check it, and true.
`test_the_observation_row_reports_the_costs_it_claims` checks it now, and
`test_where_the_choice_principle_enters` holds the census: which tables name
choice, how many times, and which four reports name it alone.

### The other bound: what the proofs actually consume

Everything above is a lower bound. An independence result says a clause cannot
be dropped, and it says so by exhibiting a model that satisfies the others and
denies this one. It says nothing whatever about whether the development uses
the clause, and until now nothing in the repository did.

The upper bound was already being printed and thrown away. Every axiom report
names two different kinds of thing in one list --- the Lean foundation axioms a
proof costs, and the declarations from this theory it uses --- and the second
kind is a use-set: an exact, transitive statement of which of the sixty-one
declared symbols and clauses a result needs. `LayerConsumptionChecks.lean`
sweeps all seven hundred and eighty-two public declarations in
`lean4/Hypermath/` and the audit replays it.

What is reviewed is the shape of the sweep rather than its lists. A rewritten
proof moves counts; only an architectural change moves the shape.

#### The stack is a diamond, not a chain

Four files declare the theory's own names: `L0Ground` thirty of them,
`L2Operations` nineteen, `L1Relations` eleven, `L3Ordinatics` one. Ten files
consume any of them, and this is what each one consumes:

| the file | consumes declarations from |
| --- | --- |
| `L0Ground` | `L0Ground` |
| `L1Relations` | `L0Ground`, `L1Relations` |
| `L2Operations` | `L0Ground`, `L2Operations` |
| `L3Ordinatics` | `L0Ground`, `L1Relations`, `L2Operations`, `L3Ordinatics` |
| `FiniteAction` | `L0Ground` |
| `GroundDerivation` | `L0Ground` |
| `GroundSyntax` | `L0Ground` |
| `PathTransport` | `L0Ground` |
| `PathLayers` | `L0Ground`, `L1Relations` |
| `QuadrilateralFiltration` | `L0Ground`, `L1Relations` |

The fourteen files not listed consume no declaration of this theory at all.

Two things fall out. The first is the claim the layer order exists to make, and
it holds: **no file consumes a declaration from a layer that comes after it.**
The import graph was the only evidence for that before, and an import is
permission to use, not use.

The second was not expected. **`L2Operations` consumes nothing from
`L1Relations`,** and `L1Relations` consumes nothing from `L2Operations`. Every
one of the seventeen declarations in the operations layer was checked and not
one of them reaches the relations layer --- not `filtrationSimCong`, not
`traceLevels`, not `deriver`, not any of the seven opaque closures. The two
middle layers are incomparable. They are siblings over the ground layer, and
`L3Ordinatics` is the only place in the development where both are consumed at
once. `L2Operations` is consumed in exactly two places: itself, and there.

Read forwards that is a fact about what the theory needs. Read backwards it is
a scope result, and the useful direction: an operations clause can change
without disturbing anything proved in the relations layer, and the reverse,
because nothing crosses.

#### Five declared names that nothing spends

Sixty-one names are declared. Fifty-six are consumed somewhere. Five are
consumed by nothing anywhere --- no statement and no proof in
`lean4/Hypermath/` mentions them:

| the name | what it is |
| --- | --- |
| `axComposeAssoc` | composition of derivation paths is associative |
| `axSeqIdentityL` | the left identity of sequencing |
| `closeFormClosureOpaque` | form closure is the conjunction of the three predicates |
| `pathStep` | a step of a derivation path |
| `pathTrace` | the trace of a derivation path |

Three are clauses the theory asserts and has not spent. Two are symbols it
declares and never reasons about.

This is where the two bounds meet and disagree, and the disagreement is not a
fault in either. A clause can be independent --- underivable from the rest,
with a countermodel to prove it --- and simultaneously idle, because nothing
has yet been proved that needs it. Independence is about the clause list;
consumption is about the theorems. The five are the names where the list has
outrun the theorems.

Part of this was already known in a narrower form. `Countermodels.lean` records
that `pathLength`, `pathStep` and `pathTrace` are the three symbols in the zero
row of the clause incidence table: no clause mentions them. That is a different
question and it gets a different answer --- `pathLength` is consumed, by
`compositionLengthAdditiveClaim`, so a symbol no clause constrains does reach a
statement. What no clause mentions and what no proof uses are two measurements,
and they agree on two of the three.

#### Why the five are idle, and the three reasons are different

The sweep says five names are unspent and does not say why, and for one of them
the repository already had. `axSeqIdentityL` is a duplicate it names as one:
`L2Operations.lean` records that four of the seven operation clauses are
removable, two derivable from `axCoopComm` and two written out as
`axCoopIdentity` verbatim. Three of the four are consumed anyway, because
`sequencingClausesAreCooperationClauses` inhabits one proposition from each
operation's own clauses and spends them doing it. `axSeqIdentityL` is the one
that was not wanted even for that.

`axComposeAssoc` is the interesting one, because nothing states it twice. It
says composition of derivation paths is associative up to `congruentPath`, it
carries its own symbols in the incidence table, and
`prefixOperationsCompose_iff_conditions` counts it among the thirty-four. It is
not a duplicate and it is not inert. Nothing uses it.

Associativity is spent by chaining. One instance rebrackets three factors; the
first thing anyone wants from it is four, and four needs two rebracketings with
a step between them. That step is transitivity, and nothing anywhere declares
`congruentPath` transitive. Three clauses mention the relation, and the most any
of them applies it is twice --- the two halves of a conjunction about a single
path, which share no endpoint and so compose into nothing.

`ComposeNeedsTransitivity` states both halves of that.

- **Transitivity is sufficient, and by itself.** Two instances of the clause
  meet at `comp (comp p q) (comp r s)`, and transitivity joins them there. No
  congruence rule, no symmetry, no reflexivity, and neither other clause.
- **And the clause alone does not give it.** Bracketings over atoms with a
  formal unit, related by equality, one rebracketing step, and the two unit
  laws --- nothing further. All three clauses hold, and the four-fold law
  fails, because one step carries `a (b (c d))` as far as `(a b) (c d)` and no
  further.

`transitivity_is_exactly_the_missing_step` is the pair, and the guard on it
compares the halves character for character: delete the transitivity hypothesis
from the derivable one and what is left has to be the underivable one. That is
the sense in which the step is exactly what is missing, and it is the part a
reader cannot check by eye.

Two things the pair is careful not to say. The model keeps its relation
reflexive, so this is not a reflexivity failure, and `related_is_reflexive`
says so in the file rather than leaving it to be noticed. And transitivity is
sufficient without being necessary: `four_fold_without_transitivity` satisfies
the three clauses and the four-fold law with a relation that breaks one chain,
because there the composition is associative outright, the clause is discharged
by equality, and equality chains whatever else the relation does.

That second one places an earlier result rather than repeating it.
`congruentPath_is_not_an_equivalence` already refutes transitivity from these
same three clauses --- and its model is exactly the case just described: its
composition is addition with an offset, both four-fold bracketings are the same
numeral, and its relation holds between them. Transitivity had been shown
underivable. What had not been shown is that the consequence the clause exists
to deliver is underivable too, and showing that needs a carrier where the two
bracketings are genuinely different things.

So this is not another independence result, and it is not an idleness
observation either. It is the join of the two that the sweep made possible for
the first time. An independence result explains why a clause cannot be dropped.
This explains why one is never picked up.

The third clause is idle for neither reason. `closeFormClosureOpaque` reads
`FormClosure x` as the conjunction of the three triangle predicates.
`axFormClosesLoop` reads two of them as sufficient for it, and that one is
consumed --- `groundIsFormClosed` is the only theorem in the development about
form closure, and it is the loop applied to the three ground inhabitants.

The two are not independent of each other. Relative to the triangle and the
ground clauses, the close is exactly the loop plus one implication:
`FormClosure x` implies `HMSyntax x`, and the triangle supplies the rest.
`the_close_clause_is_exactly_its_converse` states that as an equivalence rather
than as two implications, because the point is that nothing else of the close
survives the other clauses. So the idle clause is strictly stronger than the
spent one --- `the_other_clauses_do_not_give_the_close` exhibits a carrier where
everything else about form closure holds and the close fails --- and its whole
surplus is one arrow pointing out of `FormClosure`.

`FormClosure` is the antecedent of no arrow in any clause of the theory. There
is nowhere for an implication out of it to be used. That is the third reason,
and it is the only one of the three where the clause carries content the
development has no place to put: `axSeqIdentityL` says something already said,
`axComposeAssoc` says something that cannot be chained, and this one says
something true and unusable until some statement takes form closure as a
hypothesis. None does.

The remaining two of the five need no new argument, because a narrower result
already covers them. `pathStep` and `pathTrace` are in the zero row of the
incidence table: no clause mentions them, so nothing about them alone is
derivable and nothing about them is available to be used. They are idle in the
way an undeclared symbol would be.

So the five close out at three reasons and a fourth that was already recorded:
duplicated, unchainable, pointed the wrong way, and unconstrained. What the two
bounds together say is that "unspent" is not one phenomenon. It is a bucket,
and emptying it means asking of each name separately what the development would
have had to look like for the name to be wanted. The section after next adds a
fifth thing to the bucket, and that one is not in the five at all.

#### The idle set is a fact about these proofs, not about the clauses

The sweep was read as a binary: five names spent by nothing, fifty-six spent by
something. The refinement is the incidence --- for each of the sixty-one
declared names, how many of the seven hundred and eighty-two declarations
consume it --- and it is very uneven. At the top are the signature symbols:
`Form`, then `f2f`, then `Congruent`, then `ground`, each consumed by more
declarations than every clause of the theory put together. At the bottom is the
zero row already recorded.

Counts are not structural. They move whenever a proof is rewritten, and none of
them is pinned anywhere. One step in the distribution is structural, and it is
the step from one to zero, because that is the step out of the development and
into the idle set. Seven names are on the near side of it, and
`LAYER_SPENT_ONCE` records each with the single declaration that consumes it.

Five of those seven are held by two theorems. `groundIsFormClosed` holds three
--- `FormClosure`, `axFormClosesLoop` and `axGroundSyntaxAx` --- and
`dischargeIsAbstractionTier` holds `Discharge` and `closeDischargeOpaque`.
Deleting those two proofs would take the idle set from five to ten without
changing a clause, a symbol, or a single character of the theory. The step goes
the other way just as cheaply: adding `closeFormClosureOpaque` to one proof
takes the idle set to four and moves that name into the spent-once row, which
is what running the reduction over the sweep with that one line changed does.

So `LAYER_UNCONSUMED` reads like a property of the clauses and is not one.
Idle and spent are properties of a name relative to a set of proofs, and for
most of the names near the boundary that set is one proof deep. The sweep
measures the development. The independence results measure the theory. Only the
second kind of fact survives a rewrite, and the previous section was careful to
give reasons of the second kind --- a duplicate stays a duplicate, an
unchainable clause stays unchainable --- which is exactly why those reasons
were worth proving rather than reporting.

The form-closure fragment is where the two readings meet. Four declared names
speak form closure: the symbol, the two clauses about it, and the ground
hypothesis the consumed clause needs. One of the four is idle and the section
above says why. The other three are held by one theorem, and it is the theorem
`the_ground_closure_needs_only_the_loop` proves with the carrier left open. So
the fragment is not half-used. It is one three-line proof away from being wholly
unused, and the analysis of the idle clause applies verbatim to the rest of the
fragment the moment that proof goes.

The same reading turns up a name that is not in the idle set and is not spent
either. `axSeqAsymm` has one consumer, `plusAndAdditionallyAreDistinct`, and
that consumer is admitted. The clause is genuinely applied there --- the proof
reads `exact axSeqAsymm _ _ (by ... sorry)`, so the clause stands at the head
of the term and the sweep is right to count it. What is missing is its
argument. The hypothesis the application needs is
`¬ Congruent (f2f ground) ground`, and that is the `sorry`.

The hypothesis is not merely unproved. `no_incongruence_is_derivable` gives a
carrier satisfying all thirty-nine pre-closure clauses in which `Congruent` is total, so no
two Forms are incongruent there and the hypothesis is false everywhere in it.
`sequencing_asymmetry_never_applies` says it in one line: the antecedent of the
clause holds of no pair, so the clause is discharged by vacuity rather than by
a witness. The file's own comment draws the conclusion --- closing the `sorry`
needs a distinctness clause at `=~`, the development declares none, and
declaring one is the only route.

So this is the strongest of the five. The other four describe the development
as it stands and would be undone by someone writing a proof. This one is a
statement about the clause list: `axSeqAsymm` cannot be spent by the route it
is applied on unless the theory grows a clause it does not have.

It is the only declared name in the theory in that position --- nine
declarations in the sweep are admitted, and `axSeqAsymm` is the one name all of
whose consumers are among them.

Almost none of that is new, and it is worth being exact about which part is.
The audit already reports every one of the eight `sorry` sites under
`admissions.source`, and which of its seventy-eight dependency targets inherit
`sorryAx` under `admissions.transitive_targets`. `L2Operations.lean` already
carries the argument above in a comment at the `sorry` itself, and
`TransportCountermodel.lean` already proves both halves of it. What no comment
could state, because it is a fact about all seven hundred and eighty-two
declarations at once, is the uniqueness: `axSeqAsymm` is the only declared name
in the theory all of whose consumers are admitted. Every other consumed name is
consumed somewhere by a proof that exists. That is the join, and it has exactly
one member. `LAYER_HELD_ONLY_BY_ADMISSION` records it, and
the row empties by itself the moment that `sorry` is discharged, which is the
behaviour a pin should have.

This is the fifth thing "unspent" can mean, and it is the only one the sweep
cannot see unaided, because `#print axioms` reports an application whether or
not the proof around it is finished. It also corrects the count in the section
above:
the idle set is five counted by mention and six counted by proof, and the
difference is this clause. The four reasons given there are reasons of the
second kind and are unaffected --- a duplicate stays a duplicate whatever is
admitted --- but the number they close out was measured with nine admissions
counted as proofs.

One number looked alarming and turns out not to be. Five hundred and sixty-seven
of the seven hundred and eighty-two declarations consume no declared name at
all. Read as a proportion that says most of the development is unrelated to the
theory. Read by file it says something quite different, because the silence is
almost perfectly file-aligned.

Of the twenty-four files swept, fourteen contain not one declaration that
touches the vocabulary, five contain nothing but declarations that touch it,
and five sit in between. The five in the middle hold thirty-eight declarations
that reach the vocabulary and are otherwise silent: they are the seam. The five
at the pure end are `L0Ground`, `L1Relations`, `L2Operations`, `L3Ordinatics`
and `QuadrilateralFiltration` --- the four layers and the filtration, one
hundred and seventy-seven declarations, every one of them about the theory.

Some of the silence is not a fact about style but a requirement of the method.
`TransportCountermodel.lean` is wholly silent and has to be: it builds carriers
in which the clauses are satisfied, and it declares its own `FullAxioms`
structure to do it. A countermodel that consumed a clause of the theory would
not be a countermodel. The rest of the silent group is parametric machinery of
the kind the finite-action milestones below are made of, generic over a pointed
map and inheriting nothing.

The silence of the fourteen was already pinned, though nobody had said so: a
file that consumes nothing cannot appear in `LAYER_CONSUMPTION_SUPPORT`, and
the audit compares that dict by equality. What was not pinned is the line
between the other two groups, because a support row says that a file consumes
`L0Ground`, not that everything in it does. `LAYER_WHOLLY_CONSUMING` holds that
line. A generic helper drifting into a layer file would have left every other
pinned fact in this document intact.

#### The seam is a signature, not a theory

Naming the five files in the middle raises the question the support table
cannot answer. `LAYER_CONSUMPTION_SUPPORT` says that `GroundSyntax` reaches
`L0Ground`. That sentence is true of a file that uses `Form` and nothing else
and equally true of a file that uses every clause `L0Ground` declares. By layer
is too coarse to be an interface, so `LAYER_BRIDGE_VOCABULARY` pins the seam
name by name: exactly which declared names each of the five bridge files
reaches.

Read down it and the development has a shape nobody had stated. Of the
thirty-eight bridging declarations, thirty-three consume symbols only ---
`Form`, `f2f`, `ground`, and the relations --- and go nowhere near a clause.
The five that do reach one are two mirrored pairs and a lemma: `nativeModel`
and `native_check_sound` in each of the two ground files, which build a model of
the ground theory and prove its check sound and so are precisely the
declarations that have to discharge clauses, plus
`cycle_witness_length_preserved`, which needs one filtration clause. Every
bridge file reaches `Form` and `f2f`; two of them reach nothing else that is a
clause at all.

So the clause list is confined further than the theory is. The theory is five
files; the clause list is five files and five further declarations. Eight of
the thirty-four clauses are consumed from outside the five, all of them homed
in `L0Ground` or `L1Relations`, and twenty-six never are.

The last of those numbers is the one worth keeping. **No clause `L2Operations`
declares is consumed anywhere outside the theory's own files.** That converts
the L1/L2 incomparability from an observation about two files into a licence:
the whole of `L2Operations` can be restated without disturbing a proof anywhere
else in the development, and the support table could never have said so, because
it records that a file reaches a layer and not which of the layer's names it
took.

Splitting the seam this way needs the clause list and not a prefix test. Three
of the names the two ground files reach --- `structContinues`, `structDistinct`
and `structOrbits` --- begin with neither `ax` nor `close` and are symbols the
clauses constrain rather than clauses, and `filtrationSimCong` is a clause that
begins with neither. The forty-four fields of the model's clause structure are
the only reliable answer to which is which, and the guard reads them from there.

#### The bridge asks for nothing of its own

Knowing what the seam takes raises the question the seam table does not answer:
is any of it taken only there? A name the theory declares, never uses in its own
five files, and that only a bridge file consumes would be unspent in a way none
of the reasons above covers. It would not be idle --- something consumes it ---
but it would become idle the moment the five bridge files were deleted, which
makes it a name the theory carries for an application rather than for itself.
That is a real possibility in any development where the applications came first.

There are none. Every one of the eighteen names the bridge reaches is also
consumed inside the theory's own files, so the declared names fall into exactly
three inhabited classes and a fourth that is empty: five idle, thirty-eight
consumed only within the theory, eighteen consumed on both sides, and nothing
beyond the seam. The empty class is pinned as `LAYER_SEAM_ONLY` and the audit
compares it along with the rest, so a later proof that reaches across for
something the theory itself never used shows up as a change of structure rather
than as a quiet growth of the interface.

The corollary is worth stating separately, because it is what makes the bridge
detachable. Deleting all five bridge files changes nothing the sweep reports
about the theory: the idle set stays at five, and the seven singly-spent names
stay singly spent, since a sole consumer in a bridge file would have been a
seam-only name and there are none. All seven sole consumers are in `L0Ground`,
`L1Relations` or `L2Operations`. So the bridge is an application of the theory
in the strict sense that the theory's own measurements do not depend on it.

An empty table proves nothing by itself, so the guard does not stop at reading
it. It builds a sweep in which one name is seam-only and requires the reduction
to report it, because otherwise deleting the computation and writing the answer
in its place would pass. Building that sweep turns out to need care of the same
kind the earlier fixture needed: a file counts as wholly consuming only when
every declaration in it consumes something, so the theory side of the synthetic
sweep has to be a whole file rather than one declaration in it. Getting that
wrong produces two seam-only names instead of one, which is how the first
version of the guard announced the mistake.

#### The language is closed; the proofs are not

The seam runs one way by construction --- it is what the development takes from
the theory --- and the obvious next question is what the theory takes back.
`LAYER_WHOLLY_CONSUMING` says that every declaration in the five files is about
the theory. It does not say the five are self-contained, and they are not.

Of the five, three import nothing but each other. `L1Relations` imports
`Hypermath.Trace`, which is one of the fourteen files that consume nothing, and
uses it: after the import line `Trace` appears eleven more times in the
derivation entries of §VI, five of them `Trace.length` and the rest its
constructors and `Trace.compose`. `L3Ordinatics` imports `Ordinatics`, which is
a different repository, and that one is a dependency edge rather than a
citation --- the
structure it takes has fields, and changing them breaks this build.

So the theory's *proofs* leave its five files at exactly two places. Its
*statements* leave them nowhere. No field of the clause structure mentions
`Trace`, and neither does the type of any of the sixty-one declared names. The
two facts are worth holding together, because the second is what makes the first
harmless: the clause list can be read, and a countermodel for it built, without
`Hypermath.Trace` existing at all. That is precisely the licence every
countermodel in this document has been using --- declare a carrier, declare a
`FullAxioms` over it, and be a countermodel for the real theory --- and until now
it was a licence nobody had checked.

Checking it needs one carve-out and it is worth saying why. Stated as "no clause
mentions a name declared outside the five files", the claim is false twice over
for reasons that are not about the theory: the clause statements are read out of
`TransportCountermodel.lean`, whose own re-declarations of the vocabulary are
not outside anything, and `ContextualComposition` declares a `compose` on
`Evidence` that collides with the theory's declared `compose` on paths. Name
collisions are not dependencies. The guard states the claim about `Trace`, which
is the only file a theory file actually imports.

#### Two rows of the evidence table were counting by hand

`docs/verification.md` is where this repository says what its checks establish,
one row per surface. Two of its rows cite counts that appear nowhere else in the
repository: seven parameter-relative production proofs on the finite-trace row,
and thirteen parameter-only results with four source-relative ones on the finite
arithmetic row. The phrases occur once each, in that file, and no table, guard or
note derived them.

Both are correct, and both are equivalence classes of `PROVED_DEPENDENCIES`
rather than tallies. The seven are exactly the declarations whose report is
`Congruent`, `Form` and `f2f` and nothing else --- `selfReadLength`,
`dEntryStepLength`, `dEntryEndpointIteration`, `dEntryNoSteps`, `dIsReflexive`,
`dIsTransitive` and `reflexionTraceComposeIdentity`. Checking them cost nothing;
what cost something was noticing that nobody ever had.

The arithmetic row turns out to be one group under two conditions rather than
two kinds of result. All seventeen rest on the signature parameters. The four
are the ones whose report *also* names an axiom of Lean's foundation ---
`Classical.choice` for `finiteOrbitDecode_spec` and `finiteOrbitEquivalence_laws`,
and choice with `Quot.sound` and `propext` for
`finiteActionCompatible_iff_exists_exact` and `hostFiniteAction_exact`. Strip the
foundation axioms from any of the four and what remains is the bare signature, so
the split really is a partition of one group and not a distinction between two.

That is the half a rewrite moves, and it moves both numbers at once: a proof that
stops needing choice takes the four to three and the thirteen to fourteen. The
guards hold the split and the prose together, so the row cannot go on saying
seven while the table says eight.

Finishing the table was then worth doing, because the same question can be asked
of every row that cites a number and the answers are not uniform. The
observation row --- twenty-four reports, twenty-two naming no foundation axiom
and two naming choice --- was already joined to its table by a guard written
when that row was measured. The finite-action row's eleven were joined when the
milestones were. The two that were not joined to anything are the twenty-three
reports of the ground-syntax surface and the twenty-six of the composed ground
calculus, both of which are simply sizes of tables the audit already replays.

All of them compute now. Their splits are pinned too, including for the two rows
whose prose cites no split, so that a report in either group gaining an axiom is
visible where the row would not have mentioned it. The evidence table is the
document this repository offers as its summary; it should not be the one place
in it that is written from memory.

#### A measurement checks the part of its index it uses

Every number above is read through one table. `LAYER_AXIOM_HOME` maps each of
the sixty-one declared names to the file that declares it, and the sweep is
meaningless without it: a report is a list of axiom names, and turning that into
a statement about layers is exactly this map.

The names in it are anchored to the Lean source three times over. Twenty-six are
source parameters, and a guard already required `SOURCE_PARAMETERS` to name only
things the layers declare. Thirty-four are fields of the model's clause
structure, and pinning the seam above made that intersection's size a checked
quantity. That is sixty of the sixty-one, and the one left over is `ordinatics`,
which has a guard to itself because it is the only bundled clause declaration.
Rename any declared name in the source and something fails.

The homes were anchored by nothing, and the gap in the coverage was not
uniform. A home is used only when the name it belongs to turns up in a report.
The support rows, the seam and the wholly-consuming set all compute over names
that something consumes, so the home of a consumed name is checked constantly
and by accident: move it and the computed support stops matching the pinned
support. An idle name turns up in no report at all. Its home participates in
nothing, so nothing can contradict it.

Moving `pathStep` from `L2Operations` to `L1Relations` in the table --- leaving
the Lean source untouched, so the claim becomes simply false --- left the whole
suite green at four hundred and ninety passed and would have left the audit
green too. The same held for all five idle names.

That is the wrong way round. The idle names are the ones this document reasons
about hardest; three of the five have a countermodel written to explain why
nothing spends them, and each of those explanations is about the layer the
clause sits in. The argument that `closeFormClosureOpaque` points the wrong way
is an argument about what else `L1Relations` declares.

The rule underneath is worth stating plainly, because it is not special to this
table. **A measurement checks the part of its index that it uses, and the part
it does not use is where the index can be wrong.** "Unspent" means "not used".
So the idle set was the index's blind spot for precisely the reason it is this
document's subject, and the coincidence is not luck --- any measurement that
makes unusedness its subject will have the same shape.

Reading the map back out of the source costs one glob, and it closes the gap for
all sixty-one at once rather than for the five that needed it.

#### A result that was credited to a theorem that had gone

The roster guard reads these documents for guard names. Pointed at everything
else they name, it finds a table row in `CYCLE_WITNESSES.md` crediting a
theorem the sources do not have. That one is not a rename. The theorem's
subject changed underneath it: the deriver was moved to the limit, whose cycle
takes three applications to return rather than two, and the target's last
conjunct asks for a two-step return. The model that used to satisfy the
original target refutes it now. Only that conjunct changed --- the other three
still hold --- so what the model separates is strictly more than it used to,
every clause holding while the target fails.

The cost was not the row. A section of that note argued from the model as a
witness that the target could hold while the cycle's execution went
unpreserved, and the closing of that route left the argument with no witness at
all: both model files that interpret the target now refute it. The row was the
visible end of a claim that had quietly become unsupported, which is why the
note now says what closed the route instead of carrying the conclusion.

The obvious guard --- every name in code style must exist here --- is wrong,
and the sweep that found the row proves it. Fourteen names would not resolve
and all fourteen were correct. Some point out of the repository entirely, at
CompCert, at the interpreter a dated probe was run against, at the verifier
package. One points at the ordinatics dependency. One sits in a column headed
*Previous declaration*, where being gone is the whole content of the cell, and
one names a theorem a numbered plan proposes to write. Pointing outward,
backward and forward are things these notes do correctly and often.

What made the bad row checkable was not the name but the grammar around it. A
note that points at a name says nothing this repository can be held to; a note
that credits one --- it proves, it checks, it refutes --- is describing work
done here. That distinction is doing the same job as the convention about test
names a few paragraphs above, and it is worth stating once in general: a
document can be held to exactly the claims it makes in the present tense about
its own subject. The rest of what it says is pointing, and pointing is allowed
to leave.

#### The roster was the last thing here kept by hand

Every increment in this section ends the same way: the new guards are named in
the roster above, and the total at the top of it goes up by one or two. That
number was written by hand each time and checked by nothing, which makes it the
last hand-kept count in a document whose subject is that hand-kept counts drift.

It had not drifted --- forty-four was right --- but something else had. One of
the guards named above had been renamed, and the note went on naming it the way
it was before. It is `test_each_condition_is_either_refuted_or_derived` now, and
it acquired that name when a condition could first be answered by a derivation
rather than by a model; the changelog records the change, under the name the
guard had at the time, which is where a reader should look for what a retired
name used to mean. The new guard checks the same coverage and more, so nothing
was ever unheld. What was wrong is the name a reader would have gone looking
for, and a pointer into a test suite is exactly the kind of claim a reader
cannot check cheaply.

That fixes the convention as well as the pointer: a guard's name set in code
style in these documents is a claim that the guard exists under that name today.
A retired name is therefore not written that way here, which is why the one just
described is not spelled out --- the sentence would assert the opposite of what
it says.

Both halves are now computed: every guard named in any of these documents has to
exist, and the roster's total has to equal the number of distinct guards the
roster names --- and so does every heading inside it. The headings were worth
the extra work. The total was right; one heading was not. "One holds the
admission" stood over a pair, because the second guard was added to that block
later and the word above it was not. A correct total over a wrong part is the
most durable kind of bookkeeping error, since the only thing anyone checks is
the total, and it is the reason the sum was not enough on its own.

Making the headings mean something costs one freedom: a block may no longer
mention a guard that belongs to another block, since the count runs to the next
heading. That is a real constraint on the prose and it is worth paying, because
a heading that says how many and then names a different number is exactly as
useless as no heading. The one file deliberately left out is the changelog. A changelog
entry describes a release, and the name a guard had at that release is the right
name for the entry to use --- the rename above is recorded there, under the old
name, in the entry that made it. Holding history to today's names would be the
error and not the fix, which is worth saying because a check over all the
markdown in the repository is the obvious thing to write and would be wrong.

There is a general shape here, and it is the one this whole section keeps
running into. A measurement is trusted in proportion to how much of it computes,
and the parts that do not compute are never the parts anyone is thinking about
--- they are the scaffolding around them. The index of homes, the sizes in the
evidence table, the audit's behaviour on input it does not recognise, and now
the roster of guards: none of these is a result. All four were wrong or
unfalsifiable while every result in the document was pinned to a live sweep.

#### A failure that ended the run instead of failing a check

The audit's contract is a report. Every check gets a status and a reason,
including --- especially including --- the checks that fail because the evidence
is not what the review says it is. That holds because each probe group decides
its validity by comparing the records it was handed against a reviewed table,
and a comparison cannot raise: an axiom nobody has reviewed simply makes the
comparison false, and the group is reported as failed.

The layer sweep is the one group that does not work that way. It cannot compare
against a table of its own, because what is reviewed about it is a reduction of
seven structural facts rather than eight hundred dependency lists. So it reads
its records through the home table instead --- and a name not in that table
raised a `KeyError` from inside the lookup, which is not one of the failures the
audit is written to catch. A sweep naming an unreviewed axiom ended the run with
no report at all, rather than with a failed row saying why.

This is not a hypothetical. The most ordinary way to produce it is to add a
clause to the theory and not add it to the home table, which is a routine step
in the middle of a routine change. The test suite would have caught that, since
the index guard above reads the homes back out of the sources; but the audit is
the artifact this repository offers as evidence to someone who is not running
the suite, and it would have died rather than reported.

The reduction now raises the same failure every other group produces, naming the
axioms it did not recognise. The guard that holds it asks the question of every
group rather than of the one that had the hole --- feed each a record set naming
an axiom that appears in no reviewed table, and require a rejection rather than
a crash --- and it reads the kinds of failure the audit catches out of the
audit's own source, so narrowing that list fails here too.

Which axioms count as the foundation was, until now, written down twice: once
as the list the main report is allowed to name, and once in the sweep's own
reduction, the two agreeing up to where the admission marker was added. Neither
referred to the other. The second is now derived from the first, which is the
smaller version of the same move the rest of this section is about --- a fact
restated in two places is two facts to keep right, and the only way to find out
they disagree is to be unlucky.

What made the hole invisible for as long as it existed is that it lives in the
difference between two ways of being wrong. Every guard in this document asks
whether the measurement says something true. This one asks whether the
measurement can say anything at all when its inputs go outside what it knows,
and nothing in a suite of green checks distinguishes an answer that is right
from an answer that would not have arrived.

#### The finite-orbit results rest on the signature alone

The milestone partition put eleven of the sixty-eight proved declarations in
`FiniteAction.lean` and said nothing about what they say. Their reports do.
Every one of the eleven names `Form`, `f2f` and `ground` --- the bare signature
--- and no clause of the theory at all.

That is by construction: `Hypermath.FiniteAction` is developed over an
arbitrary pointed map, and the eleven are its specializations. But the
consequence is worth stating, because it puts them outside the independence
program in both directions. No clause of this theory is needed for them, and no
countermodel to any clause can refute them. They are theorems about an
arbitrary self-map on a pointed type that happen to be instantiated here.

### The last connective: the hub is two arrows, not two equivalences

The normal form of the section above splits conjunctions and stops. One
connective was left, and it is the one the whole residue is written in.
`three_implications_are_two_equivalences` compared three arrows against two
biconditionals --- an implication on one side and a biconditional on the other,
which is four implications counted as two fields. The two sides were never in
the same vocabulary, so the comparison could not say what it looked like it was
saying.

Splitting them says it. Two of the four implications are free, and they are free
for the reason this note has now named three times: **the proof lives in another
group.** `E x x` gives `C x x` by the filtration, which is nowhere near the
diagonal, so `E x x → Reach` follows from `C x x → Reach` and `Reach → C x x`
follows from `Reach → E x x`. Neither ever has to be stated.
`the_hub_is_two_implications` takes the filtration clause as its one hypothesis
and says exactly that.

So the residue, in one connective, is

| the clause list says | the condition list says |
| --- | --- |
| reach into congruent | congruent into reach |
| congruent into equal | reach into equal |
| equal into reach | |

and `three_arrows_are_two_arrows` states the equivalence with nothing else in
scope but the filtration. The triangle goes around; the hub goes in one side of
reach and out the other. `conditions_are_eight_split_conditions` spends both
biconditionals without changing the count --- two leave, two arrive --- and
`nine_clauses_are_eight_split_conditions` is the whole prefix reduction with no
connective left hiding anything: nine implications against eight.

**So the difference of one is real.** It survived splitting conjunctions and it
survives splitting biconditionals, and there is nothing left to split. What it
is not is a difference in strength, and what it is not either is a redundancy:
three arrows around a triangle are irredundant --- the three models of the cycle
say so --- and the two arrows are irredundant too, by two theorems that were
written before the list they belong to existed.
`the_descending_half_is_not_derivable` and `the_rising_half_is_not_derivable`
sit inside the two diagonal models, each refuting exactly one of the two arrows
that survive, and the second one's docstring says what they are for: *between
them these two say the sharp list is irredundant where the sharpening happened.*
They were written for a sharpening that had not happened yet.

That leaves the cleanest statement the reduction admits, and it is not about a
number:

> Two irredundant lists, of three statements and of two, saying the same thing
> in the same connective about the same three predicates. Irredundance does not
> pin a count. It never did, and the whole distance from forty-four clauses to
> here is the distance between a list with consequences in it and a list
> without --- not the distance between a list and its shortest form.

For most of this note that paragraph was a reading rather than a result. Five
models said the five things it needs and no statement said all five, and the
gap was not cosmetic: irredundance of two lists over *different* backgrounds
would be two unrelated facts dressed as one, and nothing had checked that the
backgrounds agree. `two_irredundant_lists_of_different_lengths` checks it and
says the paragraph in one statement --- the equivalence over `SixSharedClauses`
at every carrier, then five denials of a uniform derivation, three for the
triangle and two for the hub.

The backgrounds do agree, and the reason they do is worth keeping, because it is
luck that could have gone the other way. Each of the two diagonal models carries
the *other* diagonal condition in its original biconditional form, which is
stronger than the arrow the hub actually asks for. So the models written to
refute two biconditionals give the weaker, split background for nothing. Had
either model been written to carry only what it needed, the hub's irredundance
would have been over a background the triangle's models do not satisfy, and
there would be no comparison to make.

The denials are stated as `¬ ∀ (α : Type) ...`: no derivation of a member from
the six and the rest can be uniform in the carrier, because each conjunct names
a carrier where the six and the rest hold and the member fails. That is what the
five models were always saying, and saying it this way is what makes them five
conjuncts of one sentence instead of five separate observations.

### What irredundance was standing in for

The paragraph above is true and stops one step short of what it reaches for.
Irredundance is a property of *one* list: no member of it follows from the
others. Two irredundant lists can have different lengths --- which is exactly
what `two_irredundant_lists_of_different_lengths` exhibits, so the theorem
cannot be the reason the lengths differ. What pins a count is **minimality**,
and minimality is a claim about every list, not about one.

Stating it needs a vocabulary, and the vocabulary is smaller than it looks.
Between the three diagonal predicates there are six arrows. One of them is
already a shared clause: `filtrationSimCong` at `y := x` is `E x x` into
`C x x`, free at every setting. Five are left to say, the clause list picks
three of the five and the condition list picks two, and the question is whether
any other choice of two --- or any one, since a pair may repeat --- says the
diagonal over the six.

`Setting` bundles a carrier with the five data a clause list quantifies over,
which is what lets a statement range over models instead of over
carriers-and-relations one binder at a time.
`no_other_pair_of_arrows_is_the_hub` then says it directly: for every ordered
pair of the five arrows other than the hub's own, no derivation of the hub from
that pair is uniform in the setting. Fifteen unordered pairs, one of them the
hub, and fourteen to refute.

**The fourteen cost nothing.** Four settings cover them, and all four were
already in the file --- three of the `Drops*` models and one of the `Needs*`
models, each written to refute something else:

| setting | the arrows it has |
| --- | --- |
| `chainTrue` | congruence into reach, equality into reach, congruence into equality |
| `chainBoth` | reach into congruence, congruence into reach, equality into reach |
| `limitFree` | reach into congruence, reach into equality, congruence into equality |
| `limitEq` | reach into congruence, reach into equality, equality into reach |

Three of the four suffice for thirteen of the fourteen pairs. The one they miss
is the pair that looks most like the hub: reach into equality together with
equality into reach, which is one of the hub's own two arrows and its mirror.
Refuting that pair needs a setting where equality tracks reach in *both*
directions and congruence still does not descend --- and that is exactly
`NeedsCongruentDiagonalIsReach`, the one model whose whole purpose is to hold
the simulation diagonal at `Reach` while widening congruence to everything. The
model built to refute the eighth condition is the only one that can refute the
pair nearest the hub.

The corollary is the difference between the two lists, stated without a number:
`no_two_of_the_triangle_suffice` says each of the three pairs drawn from the
clause list has a countermodel. Both lists are irredundant; only the condition
list is minimum. `the_hub_is_the_unique_minimum` puts the two halves together,
sufficiency and every refusal, and that is the residue with nothing left over.

One honesty note, because the claim is easy to over-read. This is minimality
**in the arrow vocabulary** --- among sets drawn from the five statements
`holds` names. It does not say that no single cleverly worded statement is
equivalent to the hub. A conjunction is a statement, and nothing here rules out
finding a name for one. What it does rule out is the thing the count was being
read as ruling out anyway: that some other two of the arrows, or some one of
them, would have done.

The four-times-repeated shape is worth collecting, because it is the only rule
in this note that has predicted rather than explained. A redundancy whose proof
lives in another group cannot be found by looking inside a group, and cannot be
repaired inside one either: `nineteen_iff_seventeen` had to be stated at the
joint, `axLimitDerives` came out because the operations proved half of it,
`three_of_the_fourteen_are_derivable` used the filtration to remove prefix
clauses, and now two of the four diagonal implications come out because of a
filtration clause that no diagonal condition mentions. **Every redundancy this
note found late was a cross-group one, and every one it found early was not.**

### A floor is not a measurement, and three of them said they were

One guard was found computing three exact numbers and stating only that each
was large enough. The next question is how many others do it, and it can be
answered rather than guessed: every `assert` in `tests/` that compares an
expression against a whole number had a line inserted above it recording what
that expression was worth, and the suite was run once with all of them in
place.

Fifty-four such comparisons exist, and the run reached every one of them. The
distance between the bound and the value runs from nothing at all up to three
times the bound. Thirteen sit exactly on their value, which is a measurement
written one-sidedly: it notices the quantity falling and says nothing whatever
about it rising. One is a ceiling standing at nearly four times what it holds.
The rest sit somewhere below, and that gap is not a margin of safety. It is how
far the quantity may move with the guard above it still passing, and where the
quantity is a reader's yield, it is exactly the amount of blindness that reader
is allowed.

That distinction matters because a floor does have an honest job. A scan that
matched nothing reports every symbol free, every name uncited, every obligation
discharged, and the guard above it passes on an empty set. A floor catches
that, and nothing else catches it. What a floor cannot do is say what the
number is, and the two are easy to confuse precisely because the floor stands
where the number would go.

Three of the fifty-four say in a comment what they are for, and all three claim
the second job while doing the first.

| what the reader yields | the floor | the value | what the comment claimed |
| --- | --- | --- | --- |
| credited names | 140 | 214 | prose drifting out of the regex's reach makes the count fall and this fail |
| cited paths | 150 | 208 | a citation in a shape neither regex reaches makes the count fall and this fail |
| clause totals | 45 | 55 | both arms have to run, or half of the split is untested code |

The third is the clearest, because the line directly under it does the same job
correctly. `subsets` is held by its own truth and by nothing else, which is
what "the arm ran" means; `compared` was held to forty-five, which asserts that
the arm ran and that fifty-four of its comparisons besides took place. It now
matches its sibling, and the two reach floors above it hold the reader.

The first was worth following, because the drift its comment describes is not
hypothetical. Eight hundred and fifty crediting verbs stand in these notes. Two
hundred and seven of them had a name in code style directly before them, which
was the only shape the reader admitted; ninety-one more had one in front of
them that it did not connect. Most of those are ordinary prose --- the subject
is a pronoun, or a noun phrase, or the verb is `names` doing duty as a plural
noun. But some are plain credits with something small in the way:

- `check_seq` also proves, `congruentPath_is_not_an_equivalence` already
  refutes, `self_derivation_holds` separately proves --- an adverb.
- the `joint_state` theorem proves, the `axSuccExtends` clause gives --- the
  name used as an adjective for the noun it names.
- `Hypermath.commonWitnessesComeFromCommutativity` (L2 §VII.b) proves --- a
  citation between the subject and its verb.

Seven names are credited across one of those three shapes and every one stood
outside `test_every_name_the_notes_credit_with_a_result_exists`, which is the
guard whose whole subject is that a credited name must exist. None of the seven
is missing, so nothing in these notes was wrong; what was wrong is that the
floor was named as the thing that would have said so. The reader now admits the
three shapes, the words it admits are only the words these notes write, and
each shape is asserted to be reached, so a branch that carries nothing is a
thing this repository will notice rather than keep.

What is deliberately not done is to pin the reach. Fifty-five clause totals and
two hundred and twenty credits are living numbers across living documents, and
pinning them would fail on correct edits and teach the next reader to retype a
number instead of reading it, which is the habit these notes exist to break.
The floors stay floors. What changed is that they now say so.

### Nine counts inside the checking apparatus, and every one was wrong

Every count in this project is held to a computation, except the ones written
in the guards that do the holding. A guard's docstring is prose like any other
prose, and four of them in `tests/test_declared_counts.py` state what their
corpus is. Nothing read any of those numbers. On the day they were checked,
every one of them was wrong:

| what it counts | the docstring said | the sources had |
| --- | --- | --- |
| paths the documents cite | 204 | 208 |
| of them that resolve | 198 | 203 |
| of them that do not | six | five |
| identifiers the notes cite | 847 | 928 |
| of them that do not resolve | 51 | 47 |
| names the Lean comments cite | 309 | 314 |
| lines of comment prose in `lean4/` | 3,586 | 3,624 |
| of those carrying the word discharge | 52 | 54 |
| documents claiming a discharge | 89, across 22 files | 105, across 20 files |

The interesting part is not that they drifted. It is what each of them sat on
top of. Two --- the unresolved paths and the unresolved names --- disagreed
with a table twenty lines below them in the same function, and that table is
compared exactly, element by element, every time the suite runs. So the guard
was holding one number to the sources while its own first paragraph stated
another, and the two had been apart long enough that nobody could say when they
parted. The rest sat over floors, at forty, at a hundred and fifty, at two
hundred and fifty, at seven hundred, at fifteen, and every floor was true the
whole time.

One of the drifts ran backwards. The documents that claim a discharge went from
twenty-two to twenty while the claims in them went from eighty-nine to a
hundred and five: prose was consolidated, and the guard's floor of fifteen
could not have reported a fall to sixteen any more than it could report the
rise. A count that only grows is at least legible from the outside. A count
that moves both ways under a floor is not legible at all.

The last row then moved again while this section was being written, because
three of the lines above carry the word being counted. What the guard pins is
109, not the 105 the table records, and the difference is this paragraph's
neighbours. It is worth saying once that a measurement can be moved by its own
record, and worth saying that the right response was to retype the number
rather than to exempt the document that states it.

That reader is a substring reader: it takes every line carrying the word, not
every line making the claim, and a good fraction of the ones here are prose
about the counting. Wide is right for it, because the guard downstream asks
each line whether the names on it exist and a line naming none costs nothing;
under-reading would be the hole. What was wrong was the word in the reader's
own first line, which said *claims something is discharged* and meant *carries
these nine letters* --- the same species as the counts above it, one level
further in.

`_states` is the repair and it is four lines: take the guard's own docstring,
find the sentence, read its numbers, compare them to what the body just
measured. The failure message quotes the sentence and gives the sources'
numbers beside it, so the fix is to retype a sentence that is now wrong, which
is the only kind of retyping this repository wants. Where a number could not be
reproduced --- how many comment lines sit inside doc comments, how far five
guards in another module reach --- the sentence was rewritten to stop asserting
it rather than left standing with a figure nothing reads.

What this does not do is hold every numeral in every docstring. Eleven more
sentences in these modules carry a number in the past tense, and they are
history: what a reader returned before it was fixed, what a count used to be,
how many declarations a key collision lost. Those are the sentences this
repository exists to keep. The rule that separates them is tense, and the four
repaired here all opened in the present.

### Splitting a conjunction claims a count, and two of the splits never paid it

This project has a rule for when a list of conditions is a measurement, and it
is stated inside a guard rather than in any note: a field count is a
measurement only once every field has a model that drops it. Without that, the
count is a name. An iff whose right side is a structure with five fields is
exactly as true when one of the five follows from the other four, so the
biconditional cannot tell you whether you are looking at five conditions or at
four and a consequence.

The rule was applied to two structures. `Countermodels.lean` names eleven of
them, carrying fifty-five fields between them, and the nine outside
`CORNER_STRUCTURES` were not failing the rule --- they were outside it. That is
the same shape as the counts in the guards themselves: not a false statement
anywhere, and no statement at all where one was owed.

Read across all eleven, forty-five fields have a model that drops them and ten
do not. The ten are not a residue. They sort into two kinds, and nothing is
left over.

**Eight are halves of a split, where a drop model cannot exist.** When a clause
is split --- one clause in, two conditions out --- both halves are stated over
the same relations, so every model of the layer carries both and no model of
the layer drops either. The thing a split needs instead is a pair of models
separating the halves from each other, holding the layer's other conditions
fixed. That is the same claim a drop model makes, in the only form this
position admits, and `WitnessConjunctionDoesNotSplit` is this file's own proof
that the claim is not free: a conjunction can fail to be two clauses.

Two of the four splits in the file had already paid it.
`the_rising_half_is_not_derivable` and `the_descending_half_is_not_derivable`
separate the sharp split, and `no_two_of_the_triangle_suffice` separates the
prefix arrows. `compose_is_four_split_conditions` and
`sharp_transfinite_is_four_split_conditions` each state a count in their own
names --- four in normal form rather than three --- and each had only the
biconditional. `NeedsUnitalUpToCp` drops the whole conjunction and
`NeedsSuccEscapes` drops the whole conjunction; neither says anything about
which half is doing the work.

Both separations are two models apiece and both are small. For composition,
`keepLeft` and `keepRight` are the two projections: both strictly associative,
both with the same non-unit, differing only in which side the chosen element is
a unit on. For the transfinite layer, total congruence with simulation holding
at exactly one pair against congruence and simulation both empty: both absorb
the chain, both keep the limit out of finite reach, and the successor half each
one satisfies is the one the other refutes. Both pairs are stated with the
conditions the split does not touch held fixed, which is what makes them
separations rather than two unrelated failures.

All four new declarations report no axiom dependency at all. That is worth one
line, because `simp` reaches for `propext` on statements this small and the
first drafts of three of these proofs did. The countermodel probes are reviewed
against a pinned list of allowed kernel assumptions, so a proof that reaches
for a classical principle to show two halves differ would have been a fifth
thing to review rather than a model.

**Two are not conditions.** `someStartAtGround` and `someEndAtLimit` have no
drop model because no model of the whole can drop them: they are theorems of
the prefix and of the operations, for every limit and every successor at once.
The file knew this, at `two_of_the_nineteen_are_theorems_of_the_others`, and
said it where the joint count is made. What was missing was anything connecting
that fact to the field count of `TransfiniteConditions`, which is why the two
sat in the same bare list as the eight halves and looked like the same kind of
gap. They are the opposite kind: the halves are members nothing separated, and
these are non-members nothing flagged. `transfinite_clauses_are_five_conditions`
is still right, because it is a claim about one layer read on its own.

`test_every_condition_field_is_dropped_separated_or_implied` is the guard, and
it carries both tables. A field with no drop model that lands in neither table
fails it, which is the state the composition and transfinite splits were in
until the models were written; so does a table entry naming a declaration that
has gone; so does a field that gains a drop model and stays in a table, because
an account that is no longer needed is a claim about the sources like any
other.

What this does not do is show the halves independent over everything. Each
separation is stated over the other conditions of its own layer, and the two
models are not models of the eight prefix conditions. The claim is that the
split is a split, not that the resulting list is irredundant against the whole;
`two_of_the_nineteen_are_theorems_of_the_others` is the standing reminder that
those are different questions and that this corpus has already answered the
second one in the negative once.

### A measurement written seven times in one file, with a floor under every copy

Increment 54 built `_states` because four docstrings stated nine numbers
between them and every one of the nine was wrong. It then lived where it was
built, in `test_declared_counts.py`, and so did all five of its callers. The
instrument for holding a docstring's count could reach only the docstrings in
the file that defined it, and every other guard under `tests/` writes counts
into its prose too.

The survey was mechanical. An abstract-syntax-tree pass rewrites every
`assert <expression> <comparison> <integer>` under `tests/` into a call that
records the left-hand value and returns the same boolean, then runs the guards
and prints the value beside the bound; a second pass asks which of those bounds
the enclosing guard's own docstring also spells, in digits or in words. Eight
did. Two of the eight disagreed with the value outright, which is what a floor
is for: it admitted both. Reading the other six found two more stale numbers in
those same docstrings, neither of them the literal that had been flagged.

`tests/test_layer_boundary.py` had written one measurement seven times. Three
times in the module docstring, twice in `#:` comments beside `AMBIGUOUS` and
`BOUNDING`, and once in each of two guards. Every one of the seven said
sixteen. The value had been seventeen since the mention nothing had read was
found, and `assert len(comments) >= 16` stood in two of those guards.

One of the seven was worse than stale. "One hundred and thirty-six names are
declared by some layer above some other layer, and across all four files not
one of them stands in a statement of a layer below" --- one hundred and
thirty-six is the population *without* the ambiguity table, and with `step` in
the population the reader finds one hundred and fifty-two statements. The
sentence was false of the number it gave and true of the number it did not: the
guard beside it measures one hundred and thirty-four and asserted `>= 134`. A
number and a claim in one sentence, each right about a different corpus.

`tests/test_stated_process_rules.py` had the same shape with a sharper edge.
`test_the_skip_rubric_is_stated_the_same_way_twice` said "five of the eight
glosses are worded differently between the documents" under
`assert len(agents) >= 8`. The rubric holds nine categories and six glosses
differ. The guard *directly below it* records, in its own docstring, that the
rubric gained a ninth and why. A module whose entire subject is two documents
that can disagree carried two docstrings that did, and had no way to see it.

The two found by reading rather than by flagging are the same failure at one
remove. `test_a_header_count_of_a_section_is_the_count_that_section_has` opens
"Nine numbers, written into the header", lists eight of them, and asserted
`len(checked) >= 8`: a sentence and a list disagreeing inside the one docstring
whose whole subject is a header disagreeing with its file. And
`test_every_name_the_notes_credit_with_a_result_exists` ends by saying that
"214 against 140 is not a thing that notices" --- correctly, about a floor that
notices nothing --- while `checked` stood at 231. Appending this section moved
it again, which is the reason a live measurement belongs in a docstring a guard
reads and not, as this one also was, in a comment beside the floor.

So `_states` moved to `tests/_docstring_counts.py`, a module that is not a test
and can therefore be imported by any of them. It had to move rather than be
imported where it stood: `tests/test_declared_counts.py` imports
`agents_rubric` from `tests/test_stated_process_rules.py`, so the one module
that most needed the instrument
could not have taken it from there without an import cycle. Twenty-one numbers
across four files are now held, in fourteen calls. `AMBIGUOUS` became a
parameter of the reader, so the control its comment describes is run rather
than described. Five floors went away, because a count held exactly leaves a
floor beneath it nothing to say.

Two bounds went for a different reason. Both compared two moving quantities,
where a bound pins neither end and can hold for reasons unrelated to the claim
above it.

`assert max(kinds.values()) < len(comments)` said no bounding category covers
every mention, standing where "the categories distinguish" is the claim. It
passed with nine mentions to spare, and would have gone on passing if two
categories had come to take exactly the same mentions and say one thing twice,
or if one had become a strictly coarser reading of another. What is held now is
that no two categories take the same mentions and none takes a subset of
another. That implies the bound it replaces: no category is empty, so one
covering every mention would contain every other.

`assert len(opened[index]) > len(cited) - 1` was not weak but dead.
`test_an_inventory_cites_only_rows_that_open_a_residual`, the guard above it,
already holds every cited row to be a row that opens a residual --- so the
inventory is a subset of the residuals and the cardinality follows. The bound
could not fail while that guard passed. In its place stands the one thing an
exemption list can get wrong on its own: `UNLISTED` records that L1 opens a
residual its own inventory does not name, and it is *subtracted* from what the
guard finds, so closing that gap would leave the entry subtracting from nothing
and the guard green while the record said something no longer true. Every entry
in `UNLISTED` must now still be a gap.

Four of the eight floors were read and found sound, and are recorded rather
than repaired. `test_layer_ledger.py` says that L1 has 25 rows, which it does;
the `assert len(cited) >= 25` beside it counts citations, of which there are
forty-one, and the shared literal is a coincidence of two different quantities.
`test_every_skip_this_repository_takes_names_a_rubric_category` says "all three
skips failed it when it was first applied" above `assert len(skips) >= 3`,
where there are now five skips --- but the sentence is dated and its tense is
past, so it is history and not a count of anything current. The other two state
what they measure exactly.

What this does not do is hold the numbers in this document. `_states` reads a
docstring, and a note is not a docstring. Four passages here carried seven
stale numbers between them --- the mention count three times, the two category
totals, and the rubric's five-of-eight --- in the ledger whose entire subject is
numbers going wrong, and they were retyped by hand in this increment because
nothing could have caught them. The notes' own counts are the largest unread
population this series has found, and no guard is proposed for them yet.
