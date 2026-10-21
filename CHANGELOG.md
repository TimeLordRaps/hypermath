# Changelog

## Unreleased

Layer-stack audit: the cross-module discharge pointers were unchecked, and three
of them were false. Two admissions turned out to be provable, four turned out to
be independent of the declared clauses, and the prose now says which is which.

- Admissions reduced from ten to eight. `simulationPairExists_L1` and the inner
  obligation of `nc4_L1` are proved outright in `L1Relations` §IV.b, from the
  ground semantics clause and the two filtration axioms; neither needed the
  ordinal machinery the old forward references pointed at.
- `definitionOfGround_L1` added, so the `L0Ground` forward reference for
  L0 step 24 resolves to a closed proof for the first time.
- `HypermathFullAxiomModel.directionality_holds` added: directionality of
  `Derives` holds in the 39-clause model and fails in the 24-clause one
  (`HypermathCountermodel.directionality_claim_fails`), so it is independent of
  the clauses. The §V proof sketch that claimed to discharge it read the
  filtration backwards, which `reverse_filtration_fails` shows is unavailable.
- `HypermathCountermodel.IrreflexiveSimilar` added: a model of all 24 L0 and L1
  clauses in which `Similar` is neither reflexive nor symmetric. The clauses only
  ever assert similarity of an image, and a chain head is nobody's image. This
  also settles `orbitReflexionQuotient`, via `column_quotient_claim_fails`, which
  holds for every relation in place of `D`.
- `HypermathFullAxiomModel.congruentPath_symmetry_independent` added:
  `FullAxiomsWith` is `FullAxioms` with the interpretation of `congruentPath`
  left open, and the same structure satisfies it under a symmetric and an
  asymmetric reading. L3 census step 17 claimed `congruentPathInternals`
  discharged an L2 frame; no layer can.
- `HypermathCountermodel.AsymmetricCongruent` added: a fourth model of all 24
  L0 and L1 clauses in which `=~` is not symmetric. Three clauses constrain
  `Congruent` -- bounded below by `Simulation`, above by `Similar`, diagonal
  fixed by `Substance` -- and none of them relates `x =~ y` to `y =~ x`, so
  equality plus one ordered pair satisfies all of them.
  `congruent_symmetry_independent` pairs it against the Bool model.
- `HypermathFullAxiomModel.tuple_reading_consistent_and_conditional` added,
  pricing the obvious repair for `congruentPath`. Defining it as the documented
  four-tuple agreement satisfies all 39 clauses and coincides with the model's
  own reading, but its symmetry is exactly symmetry of `=~`, which is itself
  undeclared. Defining the parameter relocates the missing assumption to a more
  basic and more widely useful place; it does not remove it. The earlier note
  that the four-tuple reading "is symmetric" was too quick, and is corrected.
- Three false discharge pointers corrected. `L1Relations` pointed at
  `L3Ordinatics.simulationPairExists`, which was withdrawn and no longer exists;
  the L3 census claimed `driverCycleIsClosed`, which never existed; the `deriver`
  docstring claimed its cycle was discharged in `L3Ordinatics`, which carries
  only a conditional.
- Clause and assumption counts corrected repository-wide. The notes said "38
  logical clauses" in twenty-eight places and "67 declared assumptions and 11
  admissions" in nine; at that repair the sources had 39 clauses, 61 declared assumptions
  (26 source parameters and 35 logical axiom declarations, the single
  `ordinatics` interface projecting to five clauses) and 8 admissions.
  `tests/test_declared_counts.py` added, measuring all of it from the Lean
  sources and failing if any Markdown file disagrees.
- **All eight admissions are now classified, and the eighth was refuted by a
  model already in the tree.** `L2Operations.plusAndAdditionallyAreDistinct` was
  the one row of the eight still reading "open, and blocked".
  `HypermathTransportCountermodel` defines `Congruent` as `True` and certifies
  all 39 clauses; it was built for a cycle-without-reproduction result and had
  never been pointed at this admission. `no_incongruence_is_derivable` states
  the general fact --- the clauses have a model in which `=~` is total, so they
  prove no instance of `¬ (x =~ y)` at all --- and
  `HypermathFullAxiomModel.full_clauses_with_distinct_operations` supplies the
  consistent half. Independent, not unfinished. The subgoal alone would not have
  settled it: the statement is existential over the pair, so only totality of
  `=~` closes off the other pairs.
- **`+` and `additionally` are declared by the same clauses, character for
  character.** `axSeq` and `axCoop` are one proposition written twice;
  `axSeqIdentityR`, `axSeqIdentityL` and `axCoopIdentity` are one proposition
  written three times. Five declarations, two propositions.
  `Hypermath.sequencingClausesAreCooperationClauses` (L2 §VII.a) is the kernel
  check --- it states one proposition twice and inhabits the left copy from the
  sequencing declarations and the right copy from the cooperation ones, so the
  printed statement is `And X X`. `nc1_L2` and `nc2_L2`, the graduation
  obligations for the two operations, have carried the identical statement one
  line apart since they were written.
- The one remaining pair does not separate them either. `axCoopComm` is
  unconditional; `axSeqAsymm` fires only on `¬ (a =~ b)`, and no instance of
  that antecedent is derivable from any of the 39 clauses.
  `HypermathTransportCountermodel.sequencing_asymmetry_never_applies` and
  `nothing_separates_the_two_operations` state it in the model where `=~` is
  total. So `plusAndAdditionallyAreDistinct` was never close: it asks the clause
  set to distinguish two operations declared with the same obligations, using
  the one clause it can never fire. The repair is a declared distinctness clause
  at `=~`; strengthening `axSeqAsymm` is not, because its antecedent is the
  problem.
- **The operation layer is characterised too: seven clauses, three conditions.**
  `FreeFiltration.operationAxioms_iff_conditions` states the seven over
  arbitrary `S` and `C` on an arbitrary carrier and proves them equivalent to a
  congruent pair of common witnesses, one witness congruent to each Form, and
  incongruent witnesses for incongruent Forms. No operation clause mentions `E`,
  so everything the clause set says about simulation is already in the eight
  prefix conditions. `prefixWithOperations_iff_conditions` composes the two:
  **31 of the 39 clauses, eleven conditions, arbitrary carrier, no axioms.**
  What is left outside are the three path clauses (§XIV) and the five
  transfinite projections of the single `ordinatics` instance.
- **The eleven are not eight plus three.** `ext_conditions` satisfies the eight
  and the three operation conditions are unsatisfiable there ---
  `operations_exclude_the_unreached_point`. Condition 10 at the unreached point
  needs a witness similar and congruent to it, nothing is similar to it but
  itself, and at anything unreached the diagonal conditions withhold congruence.
  So the operation layer constrains nothing new about `≡` and still shrinks the
  model class, and every freedom in the note proved against 24 clauses has to be
  re-checked against 31 --- including
  `congruent_reflexivity_needs_an_unreached_point`, which is a statement about
  the prefix.
- **And four of the seven operation clauses are not merely duplicated but
  derivable.** `axCoopComm` produces two common similarity witnesses for every
  pair; keeping the first is exactly `axSeq`, which is exactly `axCoop`.
  `Hypermath.commonWitnessesComeFromCommutativity` (L2 §VII.b) proves both
  operation propositions with `#print axioms` naming `axCoopComm` and
  `axCoopIdentity` and neither `axSeq`, `axCoop`, `axSeqIdentityR` nor
  `axSeqIdentityL`. Those four declarations can be deleted with no loss. What is
  left of the layer is three clauses, one of which never fires.
- **Three of the 26 declared symbols are mentioned by none of the 39 clauses:**
  `pathLength`, `pathStep`, `pathTrace`. Nothing about them alone is derivable
  and no model is needed to establish it. `pathLengthArithmeticClaim` and
  `compositionLengthAdditiveClaim` were each refuted by construction; the
  incidence table says neither was reachable to begin with. Five more symbols
  are mentioned by exactly one clause, and in four of those the clause is the
  one that defines them; `pathStart` and `pathEnd` appear only inside
  `axLimitDerives`, only at the one path it asserts to exist.
- That is why the definition route relocates rather than removes. The documented
  reading of `congruentPath` is agreement on `(start, end, path trace,
  quantification)`, and all four of those components are symbols the clause set
  does not constrain. It also explains `axComposeNonempty`, whose docstring
  claims a path "connecting any two Forms" while its statement binds `∀ x y` and
  never uses them --- saying what the docstring says would need `pathStart` and
  `pathEnd`.
- **`congruentPath` is not declared to be reflexive or transitive either, and
  the reason the question looked settled is that `FullAxiomsWith` held `compose`
  fixed.** With `compose` pinned to `+`, `p + (q + r)` and `(p + q) + r` are the
  same numeral, so `axComposeAssoc` degenerates to `cp x x` everywhere ---
  forced by the carrier, not by the clause.
  `HypermathFullAxiomModel.PathClauses` (§XIV) opens `compose`, `pathGround` and
  `congruentPath` together, which the incidence table licenses: exactly three
  clauses mention any of the three, and no other clause has to move.
  Composition that costs a step (`p + q + 1`, unit `0`, congruence
  `(x = y ∧ 2 ≤ x) ∨ x = y + 1`) satisfies all three clauses and reaches neither
  `0` nor `1`; `congruentPath_is_not_an_equivalence` reads reflexivity, symmetry
  and transitivity failures off that one gap, and
  `path_clauses_decide_nothing_about_congruence` puts the model's own reading
  beside it.
- **So `compose` is not a monoid up to anything.** "Associative and unital up to
  `congruentPath`" reads as a quotient monoid, and that reading needs the
  relation to be an equivalence. The clause set does not say it is, so those two
  clauses assert strictly less than their names suggest.
- Second time this cycle that what was *held fixed* decided the answer, after
  the ground carrier in `prefixAxioms_iff_conditions`. A model answers a question
  about a symbol only as far as the rest of the model is free; before believing a
  clause forces something, vary the symbols nobody is asking about.
- The prose scan now treats an inline code span like a quotation. `p + q + 1`
  is arithmetic, and the `1` was being read as a count of whatever noun came
  next. No total in these notes is written inside backticks --- the 31 code
  spans holding a number are all literal values --- so the only thing the rule
  can suppress is a false report. Checked by injecting four stale totals in
  ordinary prose and confirming all four still fail.
- `tests/test_declared_counts.py` also pins that those same three clauses are
  the whole cover of `compose`, `pathGround` and `congruentPath`, so a fourth
  clause naming any of them puts §XIV's reasoning out of date.
- **The incidence count is a first step, not an answer.** A symbol no clause
  mentions is free and nothing more need be checked. A symbol exactly one clause
  mentions can be either completely determined or almost completely free, and
  which one it is depends on the shape of that clause rather than on the count.
  Both cases are now proved over an arbitrary carrier with no model:
  `FreeFiltration.determined_by_its_closing_clause` (two relations satisfying the
  same biconditional are equal, so a symbol whose only clause is a close has no
  freedom at all) and `FreeFiltration.endpoints_free_off_one_path` (an
  existential clause pins its symbol at its own witness and leaves every other
  value arbitrary, which is what `axLimitDerives` does to `pathStart` and
  `pathEnd`). `FreeFiltration.incidence_one_is_two_cases` states them together.
  Dropping the exclusion of the witness from the second makes its proof fail, so
  the freedom really is everywhere-but-one rather than everywhere.
- **What the weak reading of `ax-deriver-at-limit` would cost is now priced
  against this layer's own clauses, and this layer cannot pay it.**
  `WeakPositionPrice.notFiniteByTransitivity` and
  `WeakPositionPrice.derivedByPathByBridge` state, over an arbitrary carrier,
  the two routes that replace `Transfinite`'s rewrites when the position is
  stated at `==` rather than `Eq`; between them they need transitivity of `==`,
  the `==`-into-`=~` bridge, and symmetry and transitivity of `=~`.
  `WeakPositionPrice.the_weak_position_is_unaffordable_here` supplies the
  verdict: the bridge is a prefix clause and holds everywhere, and each of the
  other three is refuted by a model of all 24 clauses. Both consequences are
  lost under the weaker reading here too.
- **A correction, and the reason it matters.** The mechanization note in
  `L3_ordinatics.hm` claimed this layer may state the clause at `==` because
  "both costs are already paid here". They are not paid, and the three
  refutations that say so --- `FreeSimulation.simulation_transitivity_claim_fails`
  and the two in `AsymmetricCongruent` --- predate the claim and live in the
  same file as it. The note now records what is proved: the argument from
  L0's closure of `==` describes the intended reading, not a consequence of the
  clauses that mechanize it, and the Lean states the position at `Eq` because
  `==` as declared does not support the rewrites the position exists to license.
- **Ten of the 39 clauses hold of nothing, so the reduction actually performed
  is twenty-nine to nineteen.** `FreeFiltration.the_closes_are_definitional`
  proves all ten with no carrier, no relation and no hypothesis --- each is
  `Iff.rfl`, because the free reading defines every auxiliary predicate to be
  what its closing clause asserts. `prefix_is_its_fourteen_contentful_clauses`
  removes them and `twenty_nine_clauses_carry_the_content` restates the
  characterisation over what is left. The namespace note said seven; seven is
  the `*Opaque` family, and `closeStructContinues`, `closeStructDistinct` and
  `closeStructOrbits` are three more of exactly the same kind. Corrected. The
  ten are not free in hypermath --- in the layers those predicates are opaque
  parameters and these clauses are what pins them --- so what the number
  measures is how much of the clause set was spent defining its own vocabulary.
- **`three_of_the_fourteen_are_derivable` added**, so that "contentful" is not
  read as "irredundant": `axGroundSelf` is `filtrationCongSim` applied to
  `axGroundSubstanceAx`, `axGroundSyntaxAx` is `axSim` at one step, and
  `axFormClosesLoop` is `filtrationSimCong` rearranged. Whether the clause list
  is irredundant anywhere has never been measured clause by clause.
- **It has now, for the eight conditions: none of them follows from the other
  seven.** `conditions_iff_the_eight` names each field of `Conditions` as a
  proposition of its own, and eight models refute one apiece while satisfying
  the rest --- `NeedsSimIntoCong`, `NeedsCongIntoSim`, `NeedsImageSimilar`,
  `NeedsImageSimilarToGround`, `NeedsDoubleImageSimilar`,
  `NeedsImageNotSimulatingGround`, `NeedsCongruentDiagonalIsReach` and
  `NeedsSimulationDiagonalIsReach`. The three similarity conditions are
  indistinguishable on symbols --- each mentions `S` and `f2f` and nothing else
  --- and are independent because they demand the relation at three different
  families of pairs, which no scan over symbol occurrences can see.
- **One of the eight cannot be refuted on the chain.**
  `reached_points_are_self_congruent` derives half of `CongruentDiagonalIsReach`
  from the other seven, so refuting it needs a point congruent to itself that
  `Reach` does not reach, and the chain has none. The model is the extended
  carrier with `~~` and `≡` unchanged and `=~` widened to plain equality.
  `self_simulating_points_are_reached` is the mirror half.
- **Irredundant is not minimal: `conditions_iff_six_and_two_implications`
  added.** The two diagonal biconditionals can be replaced by one implication
  each --- `C x x → Reach x` and `Reach x → E x x` --- and `SharpConditions`
  states the result. Which halves survive is forced by the direction of the
  inclusion, and the same two models refute the surviving halves
  (`the_descending_half_is_not_derivable`, `the_rising_half_is_not_derivable`).
- **The canonical clause list is now joined to the characterisation by a
  theorem, not by a name.** `CanonicalAxioms` carries the 39 fields of
  `TransportCountermodel.FullAxioms` into `FreeFiltration` with the ten
  auxiliary predicates left as parameters, and
  `the_canonical_clauses_are_the_free_ones` proves that reading them at the free
  definitions gives exactly `PrefixAxioms ∧ OperationAxioms ∧ ComposeAxioms ∧
  TransfiniteAxioms`. The proof is field projections and no tactic, and it
  depends on no axioms, so the correspondence is definitional clause by clause
  rather than merely provable.
- **The four clause structures agree by statement, not only by name.** Three of
  them state all 39 clauses character for character; `FullAxiomsWith` differs in
  exactly the three clauses that mention `congruentPath`, by exactly
  `congruentPath → cp`. `test_the_clause_lists_agree_word_for_word` and
  `test_the_canonical_list_is_the_declared_one` hold both, and the `countermodel`
  audit group grows from seventy-nine to eighty dependency reports.

- **None of the three operation conditions follows from the other two over the
  eight.** `operationConditions_iff_the_three` names them --- `PairedWitnesses`,
  `IdentityWitness`, `ApartWitnesses` --- and three models refute one apiece
  while satisfying `Conditions` and the other two. Each comes with a lemma
  saying where its condition is already proved, and the lemma is what fixes the
  model: `reached_points_are_their_own_identity_witness` forces a point off the
  chain, `a_reached_common_predecessor_pairs_them` forces every common
  predecessor off it as well, and `mutual_predecessors_are_apart_witnesses`
  forces a thin `~~` instead. The models adjoin two, four and one point
  respectively, and the freeness lemma is why in each case.
- **The independence here is a trade between two relations, not within one.**
  Apartness is free where `~~` is fat; pairing is free where `Reach`, and so
  `~~`, is fat. What makes one of the three free is what makes another
  refutable, which is a kind of separation none of the eight showed and none the
  incidence table can see --- all three mention the same two relation symbols.
  The `countermodel` audit group grows from eighty to eighty-seven dependency
  reports, and `test_each_condition_has_a_model_named_for_it` and
  `test_every_model_names_its_whole_group_and_denies_one` now read both condition
  structures, so neither group can gain a condition without gaining a model.
  `test_the_operation_props_are_their_fields_word_for_word` holds the three
  standalone Props to their fields as text, which the Lean biconditional does
  not: it is proved up to definitional equality, and that leaves the bound
  variable names --- the ones the prose points at --- free.

- **None of the three composition conditions follows from the other two
  either, and the answer is cheap for a reason.**
  `composeConditions_iff_the_three` names them --- `AssociativeUpToCp`,
  `UnitalUpToCp`, `SomeNonUnit` --- and the three models are small algebras with
  no carrier in them at all: a composition that doubles its left argument,
  addition with the unit misdeclared as one, and the one-path world. A model
  refuting one of the operations had to satisfy the eight filtration conditions
  first; nothing here has to be satisfied first, because the path symbols are
  disjoint from everything else. That is the second consequence of the
  disjointness `lists_join_freely_exactly_on_disjoint_symbols` read off the
  incidence table: disjoint symbols make the join free, and they also make the
  list's own internal question cheap.
- **`NeedsSomeNonUnit` prices the clause with two inert binders.**
  `axComposeNonempty` was already known to say only that something is not the
  unit; the model shows that dropping it leaves the composition layer satisfied
  by a structure with one path. `no_non_unit_collapses_cp` says the same thing
  abstractly: refuting the condition makes `congruentPath` relate every pair,
  given symmetry and transitivity --- which
  `congruentPath_is_not_an_equivalence` shows the clause set withholds.
- **Five of the fourteen models now depend on no axioms whatsoever**: the three
  composition ones and the two among the eight that read every relation as a
  constant. The other nine reason about positions on the chain, where `simp` and
  `omega` bring `propext`. The `countermodel` audit group grows from
  eighty-seven to ninety-four dependency reports, all fourteen condition Props
  are checked to copy their fields character for character
  (`test_every_condition_prop_copies_its_field_word_for_word`), and
  `test_every_model_names_its_whole_group_and_denies_one` --- renamed, because
  the groups are now of eight, three and three --- requires an operation model
  to carry `Conditions` whole and a composition model not to.

- **Two of the nineteen conditions are theorems of the other seventeen, so the
  characterisation is not minimal.**
  `someStartAtGround_is_implied_by_the_eight` proves the first from
  `imageSimilarToGround` --- the image of the ground is the witness --- and
  `someEndAtLimit_is_implied_by_the_operations` proves the second from
  `identityWitness`, which hands over something congruent to every point and so,
  in particular, to the limit. `two_of_the_nineteen_are_theorems_of_the_others`
  states both at once, for every limit and successor. Neither proof is longer
  than a line and neither needed a search; they were missed because the
  transfinite conditions had only ever been asked about as a block.
- **A fourth way independence can fail, and the incidence table cannot see it.**
  The three failures already recorded are about symbols: unmentioned, mentioned
  once, or disjoint between two lists. This one is about binders.
  `SomeEndAtLimit` names a point where `IdentityWitness` quantifies over points,
  and a condition that names a point is implied by any condition of the same
  shape that quantifies over them. `SomeStartAtGround` is starker still: it
  mentions no transfinite symbol at all, so it is a prefix condition that was
  written down inside the transfinite structure.
- **The three transfinite conditions that survive are independent of all
  eighteen others.** `NeedsLimitAbsorbsTheChain` thins congruence below the
  limit, `NeedsLimitNotSimulatedFinitely` adds one simulation pair from the
  ground to the limit, and `NeedsSuccEscapes` sets the successor to `id`. Each
  satisfies the eight prefix conditions, the three operation conditions, the
  three composition conditions and the four transfinite conditions that are not
  its own. No earlier model in the file satisfies more than ten. Two of the
  three are one edit away from `LimitAdjoined`, which proves all nineteen.
- **This does not contradict `nineteen_is_not_fourteen_plus_five`.** That result
  says the transfinite list is not free over the other fourteen, and what
  obstructs it --- `spanned_carriers_admit_no_limit` --- obstructs
  `limitNotSimulatedFinitely`, one of the three that survive. Failing to be free
  over a list and containing members implied by it are different properties, and
  running the two together is what hid the redundancy.
- **The `countermodel` audit group grows from ninety-four to one hundred and
  four dependency reports**, of which sixty-one depend on no axioms at all. The
  rule the composition group left --- a model is axiom-free exactly when it never
  looked at a carrier --- predicted correctly here: all three new models look at
  one, all three depend on `propext`, and the axiom-free five are still the same
  five. `test_each_condition_has_a_model_named_for_it` is now
  `test_each_condition_is_either_refuted_or_derived`, because a condition may
  now answer with a derivation instead of a model, and it checks that no
  condition answers with both.

- **The two redundant conditions are now spent, not just noted.**
  `nineteen_iff_seventeen` states the sharpened characterisation, and it has to
  be stated at the joint rather than inside `TransfiniteConditions`, because the
  proofs of the two conditions it drops live in two other groups. A redundancy
  found across groups cannot be repaired within one. With `someStartAtGround`
  goes the last transfinite mention of simulation, so the sharpened layer speaks
  only of congruence, of equality and of the successor.
- **One more clause comes out of the clause set, and it is not a definitional
  one.** `twenty_eight_clauses_carry_the_content` drops `axLimitDerives`, which
  unlike the ten closes is a real statement about a carrier. It hid because it
  binds two halves under one witness: neither half can be matched against
  anything while the witness ties them together, and once the binder is pinned
  each is an instance of a clause that quantifies where this one names.
- **The question this note left open is answered: the clause set has now been
  measured clause by clause.** `eleven_prefix_clauses_carry_the_content` removes
  the three that `three_of_the_fourteen_are_derivable` had proved derivable and
  never removed; `the_deriver_binder_is_inert` removes the last transfinite
  clause, the second inert binder in the file after
  `compose_nonempty_binders_are_inert`; and
  `twenty_clauses_are_seventeen_conditions` puts the four layers back together
  at that point. Eleven was not minimal either:
  `nine_prefix_clauses_carry_the_content` removes two more clauses and two
  thirds of a third, since the diagonal cycle reaches the ground without being
  told to and two of `traceLevels`' three conjuncts are filtration clauses read
  at an image. Thirty-nine clauses, twenty-nine contentful, eighteen needed,
  seventeen conditions.
- **Three of the four layers turned out to be their own conditions.** The
  operations are seven names for four statements, and the fourth is a projection
  of a fifth clause, leaving three that are `OperationConditions` character for
  character. The composition is three statements carrying two inert binders. The
  transfinite layer is three statements carrying one inert binder and one clause
  implied from beneath. The whole remaining distance between the clause set and
  the conditions is the prefix layer, and it comes to one cycle: six of the nine
  prefix clauses are conditions written out identically, and
  `three_implications_are_two_equivalences` shows the rest is three arrows around
  a triangle against two arrows to a hub --- once both sides are written in one
  connective, which they were not until `the_hub_is_two_implications`.
- **In three of those cases the proof of the reduction was already in the file.**
  `operationConditions_of_operationAxioms` reads exactly three fields of its
  argument and always has; the other four are rebuilt by the reverse direction.
  That is a complete proof that seven clauses are three, written before anyone
  asked the question. If one direction of a bridge consumes only a sub-list and
  the other rebuilds the whole list, the sub-list carries the list --- cheaper
  than a countermodel and checkable by reading which fields a proof mentions.
- **The nine prefix clauses are irredundant, and only the cycle needed new
  work.** Six of the nine are conditions written out identically, so the model
  refuting each of those six is one the file already had; the three arrows are
  not conditions and inherit nothing. `nine_is_six_and_a_cycle` splits the nine
  so the arrows can be stated alone, and `DropsReachIntoCongruent`,
  `DropsCongruentIntoSimulation` and `DropsSimulationIntoReach` refute one arrow
  apiece while carrying the six and the other two. The first two read every
  relation as a constant and need no carrier: breaking a cycle only requires two
  of its points to disagree everywhere. Only breaking the arrow back to reach
  needs something built, because it means exhibiting somewhere reach does not go.
  They are filed under `Drops` and not `Needs` because the condition coverage
  test requires every `Needs` namespace to name a declared condition, and an
  arrow is not one.
- **The count was never in normal form, and the difference was.** Two of the
  eighteen clauses and two of the seventeen conditions are conjunctions, so the
  two sides had been compared in a form the note's own rule says to split first.
  The rule cannot be *always split*: `the_unit_clause_is_two` and
  `the_successor_clause_is_two` take apart a conjunction under a `∀`, and
  `WitnessConjunctionDoesNotSplit` shows that one under an `∃` does not come
  apart at all --- which is the shape of all three operation conditions.
  `TransfiniteConditions` had found the same fact from the other side, where
  pinning a witness separated one clause into two conditions; this is its
  converse. In normal form the lists are twenty and nineteen, by
  `twenty_split_clauses_are_nineteen_split_conditions`. Both counts move by two
  and their difference does not, which is the point: a count of fields is a fact
  about a way of writing, and conjoining any two conditions would give eighteen.
  What survives the convention is the difference of one, and that is the
  triangle against the hub.
- **The last connective: the hub is two arrows, not two equivalences.** A
  biconditional is two implications, so the residue had been compared in two
  vocabularies --- three implications against four counted as two fields. Two of
  the four are free, and free for the reason the note has now named three times:
  the proof lives in another group. `E x x` gives `C x x` by the filtration, so
  neither `E x x → Reach` nor `Reach → C x x` need be stated.
  `the_hub_is_two_implications` takes that one filtration clause as its only
  hypothesis; `three_arrows_are_two_arrows` states the residue with nothing else
  in scope; `conditions_are_eight_split_conditions` spends both biconditionals
  without moving the count, and `nine_clauses_are_eight_split_conditions` is the
  prefix reduction with no connective left hiding anything. The difference of one
  is real: it survives every splitting there is. And both lists are irredundant,
  the three arrows by the cycle models and the two by
  `the_descending_half_is_not_derivable` and `the_rising_half_is_not_derivable`,
  which were written for a sharpening that had not happened yet. Two irredundant
  lists of different lengths for the same content --- irredundance does not pin a
  count, and the distance from thirty-nine was never a distance to a shortest
  form.
- **The axiom rule is false as stated, and the reports are reports about
  vocabulary.** The composition group's rule --- a model is axiom-free exactly
  when it never looked at a carrier --- was cited three times as a prediction
  that came true. `WitnessConjunctionDoesNotSplit` looks at a carrier and
  depends on nothing. `AxiomsMeasureVocabulary` shows what the reports track:
  two theorems, one statement about one model, proved by naming a core lemma and
  by constructor injectivity, depending on `propext` and on nothing. Measured
  across the file, no model whose proofs use `omega`, `simp`, `simpa`, `subst`
  or `rw` is axiom-free, and of the five that avoid all five and still depend on
  something, four do so solely through `Nat.succ_ne_zero` and the fifth inherits
  from a model it cites. The predictions kept coming true because building a
  carrier forces automation and automation carries the axiom, not because the
  criterion was right. Four of the file's `propext` dependencies are removable by
  editing one identifier, with no model changed and nothing reproved.
- **The cost table makes three claims checkable that were not.** The note's claim
  that four `propext` dependencies are removable by editing one identifier was a
  claim nothing could check. The `AxiomsMeasureVocabulary` pair --- two proofs of
  one statement, one costing `propext` and one costing nothing --- was watched
  only by a test that the halves state the same fact, which they still would if
  the expensive half were reproved by hand; the audit now rejects that edit and
  names the report whose cost moved. And the five reports that depend on
  `Classical.choice` turn out to be the limit-adjoined model and exactly what
  cites it, so choice enters the file in one construction and reaches nothing
  else --- true all along, and unsaid because nothing had written down where the
  axioms are.
- **The closing claim was a reading of five models and is now one statement.**
  `two_irredundant_lists_of_different_lengths` says that the triangle and the hub
  carry the same content over `SixSharedClauses` at every carrier, and that
  neither has a removable member --- five denials of a uniform derivation, three
  from the arrow models and two from the diagonal models. The gap this closes was
  not cosmetic: irredundance of two lists over different backgrounds would be two
  unrelated facts, and nothing had checked that the backgrounds agree. They agree
  because each diagonal model happens to carry the other diagonal condition in
  its stronger biconditional form, so a model written to refute a biconditional
  supplies the weaker split background for nothing.
  `test_the_two_lists_are_the_same_two_lists_in_both_theorems` checks the part
  Lean cannot: that the five conjuncts are five, that each mentions its whole
  list and nothing off it, that each drops a different member, and that the lists
  dropped from are the lists proved equivalent.
- **The list of required process checks had drifted by exactly the check whose
  failure fails the gate.** `layered_derivation` was added to the audit, wired
  into the replay gate and given a row in the bound-reports table, and left out
  of the sentence in `docs/verification.md` saying which checks a completed
  native execution requires --- which went on saying eleven, and naming eleven.
  Nothing compared that sentence to the audit. It now says twelve and names
  twelve, and `test_the_process_checks_the_note_lists_are_the_ones_the_audit_runs`
  reads the command table out of `audit.py` and the list out of the note and
  requires the names and their order to agree.
- **Sixty-eight proved production milestone declarations were measured; the
  eleven inside them never were.** `FINITE_ARITHMETIC.md` has said "including
  eleven finite-orbit/action results" while the only pinned number was the
  total, so the eleven could have been any eleven. They are the declarations in
  `FiniteAction.lean`, and the whole partition falls out of one measurement:
  every milestone name is declared in exactly one file, and the parts are
  forty-one in `L3Ordinatics.lean`, thirteen in `L1Relations.lean`, eleven in
  `FiniteAction.lean` and three in `L2Operations.lean`. A name that moved
  between files, or a number that drifted in either note, now fails
  `test_the_milestone_declarations_partition_by_the_file_that_declares_them`.
- **Choice was traced through one file; the census runs over all of them.**
  "Choice enters the file in one construction" above is a claim about
  `Countermodels.lean`, and every dependency table is pinned the same way now,
  so the same measurement runs everywhere. Thirty reports name
  `Classical.choice`: five in `countermodel`, eighteen in `full_model`, two in
  `observation`, one in `record_encoding` and four among the sixty-eight
  milestone declarations. Twenty-six name it beside both `Quot.sound` and
  `propext`; four name it without either, and all four are places where a
  decoding is asserted to exist. Only the safe direction is claimed --- whatever
  brings the other two axioms into the twenty-six, it is not what brought choice
  into these four --- because the section above is a record of what happens when
  axiom reports are read as a criterion. `test_where_the_choice_principle_enters`
  holds the census in both directions.
- **An exact cost claim made before anything could check it turns out to be
  true.** `docs/verification.md` has said "24 observation reports: 22 axiom-free,
  two with classical choice" since before `OBSERVATION_DEPENDENCIES` existed.
  The table agrees, and `test_the_observation_row_reports_the_costs_it_claims`
  now reads the sentence and the table together. `OBSERVATION_DEPENDENCIES` is
  also the only table in the repository where choice arrives unaccompanied.
- **The cost table in `CLAUSE_INDEPENDENCE.md` had gone stale by five reports.**
  It still read one hundred and thirty-five in four shapes after the minimality
  models were registered. The four shapes are unchanged and the totals are not:
  one hundred and forty reports, ninety free, thirty-two `propext`, thirteen
  `Quot.sound` with `propext`, five with `Classical.choice` as well.
- **The independence program had only ever measured a lower bound.** An
  independence result says a clause cannot be dropped. Nothing said whether
  anything uses it. `lean4/LayerConsumptionChecks.lean` and the thirteenth
  process check, `layer_consumption`, add the other bound: an axiom report
  names the Lean foundation axioms a proof costs *and* the declarations of this
  theory it uses, and the second is an exact transitive use-set that was being
  printed and discarded. The sweep covers all 782 public declarations in
  `lean4/Hypermath/`. Its individual lists are not pinned --- only the shape is,
  so a rewritten proof moves nothing and an architectural change moves
  everything.
- **The layer stack is a diamond, not a chain.** Every one of the seventeen
  declarations in `L2Operations.lean` was checked and none consumes an
  `L1Relations` declaration; none of `L1Relations` consumes an `L2Operations`
  one. The two middle layers are incomparable, siblings over `L0Ground`, and
  `L3Ordinatics` is the only place in the development where both are consumed
  at once. The import graph is a path and was the only evidence there had ever
  been, and an import is permission to use rather than use. The claim the order
  exists to make does hold: no file consumes a declaration from a layer that
  comes after it.
- **Five declared names are consumed by nothing.** `axComposeAssoc`,
  `axSeqIdentityL` and `closeFormClosureOpaque` are clauses the theory asserts
  and no statement or proof anywhere in `lean4/Hypermath/` mentions;
  `pathStep` and `pathTrace` are symbols it declares and never reasons about.
  A clause can be independent and idle at once --- underivable from the rest,
  with a countermodel to prove it, and still not needed by anything proved so
  far. `Countermodels.lean` already knew a narrower version of this: no clause
  mentions `pathLength`, `pathStep` or `pathTrace`. The two measurements
  disagree about `pathLength`, which no clause mentions and
  `compositionLengthAdditiveClaim` consumes.
- **The eleven finite-orbit results rest on the signature and no clause.** The
  milestone partition named them by their file; their reports say what they
  are. Each of the eleven consumes `Form`, `f2f` and `ground` and nothing else,
  so they hold of an arbitrary self-map on a pointed type. No clause of this
  theory is needed for them and no countermodel to a clause can refute them,
  which places them outside the independence program in both directions.
- **One of the five idle clauses now has a reason.** `axComposeAssoc` asserts
  associativity up to `congruentPath`, and associativity is spent by chaining:
  four factors need two rebracketings with a transitivity step between them.
  Nothing anywhere declares `congruentPath` transitive. `ComposeNeedsTransitivity`
  in `lean4/Countermodels.lean` states both halves --- with transitivity the
  four-fold law follows from the clause by itself, and without it the clause
  holds in a model of bracketings where the four-fold law fails. The guard on
  the pair compares its two halves character for character, so a negative half
  that denied something weaker than the positive half proves is rejected rather
  than read as an isolation of transitivity.
- **And the converse is stated rather than assumed.**
  `four_fold_without_transitivity` satisfies the three clauses and the four-fold
  law with a relation that is not transitive, because its composition is
  associative outright and the clause is discharged by equality. That places
  `congruentPath_is_not_an_equivalence`, which refutes transitivity from these
  same clauses and whose model is that case exactly: both four-fold bracketings
  are the same numeral there, so it leaves the consequence the clause exists to
  deliver untouched. Six reports, all free of every axiom; the countermodel
  totals move with them to one hundred and forty-six reports and ninety-six
  free, the other three shapes unchanged.
- **The third idle clause is idle for a third reason.**
  `closeFormClosureOpaque` is strictly stronger than `axFormClosesLoop`, which
  is consumed: relative to the triangle and the ground clauses it is that
  clause plus one implication out of `FormClosure`, and
  `the_other_clauses_do_not_give_the_close` exhibits a carrier where everything
  else about form closure holds and the close fails. `FormClosure` is the
  antecedent of no arrow in any clause, so the surplus has nowhere to be spent.
  Three reports, all free; the countermodel totals move to one hundred and
  forty-nine reports and ninety-nine free.
- **An independence result explains why a clause cannot be dropped; this
  explains why one is never picked up.** Neither bound could ask the question
  on its own, which is what the sweep made available.
- **So "unspent" is four phenomena, not one:** duplicated, unchainable,
  pointed the wrong way, and unconstrained --- the last already recorded for
  `pathStep` and `pathTrace` by the zero row of the incidence table. All five
  names the sweep found now have a reason.
- **The idle set is a fact about these proofs, not about the clauses.** The
  sweep's binary refines to an incidence, and the structural step in it is the
  one from one consumer to none. `LAYER_SPENT_ONCE` pins the seven names a
  single declaration holds in play, and the audit's `layer_consumption` probe
  now compares it along with the support and the idle set.
- **Two theorems hold five of the seven.** `groundIsFormClosed` holds three and
  `dischargeIsAbstractionTier` holds two, so deleting two proofs would take the
  idle set from five to ten without changing a character of the theory --- and
  adding one clause to one proof takes it to four. What survives a rewrite is
  the reasons the previous entries prove, not the counts.
- **The form-closure fragment is one proof from wholly unused.** Four declared
  names speak form closure; one is already idle and the other three are held by
  the theorem `the_ground_closure_needs_only_the_loop` generalises. The
  idleness analysis applies to the rest of the fragment the moment that proof
  goes.
- **One declared name is applied only inside a proof that is not finished.**
  `axSeqAsymm`'s sole consumer is `plusAndAdditionallyAreDistinct`, which is
  admitted. The clause really is applied --- `exact axSeqAsymm _ _ (by ...
  sorry)` --- and the `sorry` is its hypothesis, so the sweep is right to count
  it and wrong to call it spent. It is the only name in the theory all of whose
  consumers carry `sorryAx`. `LAYER_HELD_ONLY_BY_ADMISSION` pins it, the guard
  checks both directions against the Lean source, and the row empties by itself
  when the admission is discharged.
- **And that admission is one the theory proves it cannot close.**
  `no_incongruence_is_derivable` gives a carrier satisfying all thirty-nine
  clauses where `Congruent` is total, and `sequencing_asymmetry_never_applies`
  reads off that the clause's antecedent holds of no pair there. Both predate
  the sweep; what the sweep adds is the uniqueness, which is a fact about all
  seven hundred and eighty-two declarations at once and so could not have been
  stated in a comment. This makes the fifth reason the strongest of the five:
  the other four describe the development and a new proof would undo them.
- **So the idle set is five by mention and six by proof.** That is a correction
  to the count in the entries above, which was measured with nine admitted
  declarations counted as proofs. The four reasons are unaffected --- they are
  reasons about the clauses, not about the proof state --- but "unspent" now
  has a fifth meaning, and it is the one `#print axioms` cannot see, since it
  reports an application whether or not the proof around it is closed.
- **A research note credited a result to a theorem that no longer exists.**
  `docs/research/CYCLE_WITNESSES.md` reported that the six-form model satisfies
  every clause *and* the original self-derivation target while having no
  preserving derivation path. That stopped being true when the deriver moved to
  the limit: its cycle takes three applications to return, the target's last
  conjunct asks for two, and the model now refutes the target instead. The
  note's opening thesis, a section heading, the body describing the deriver as
  `a1`, and a declaration-table row all still described the older model, and
  the note's thesis was read off a pairing --- the target holding while no
  preserving path exists --- that this model no longer supplies. The target
  itself remains satisfiable with every clause: `TransportCountermodel` proves
  it and bundles it with a real two-step cycle witness, which carries the
  thesis in a stronger form. The note has been corrected to state what is
  proved now, and to record the lost pairing as a cost of declaring the
  deriver's position. A new guard holds every name these notes credit with a result to
  something the sources or the Lean dependency declare; it fails on the row as
  it actually stood.
- **The separation that correction found missing has been rebuilt.**
  `lean4/TargetAtLimitModel.lean` is a five-form model whose limit sits on a
  two-cycle with the deriver at its head, and
  `full_clauses_and_target_without_nonzero_D` carries all 39 clauses, the
  original self-derivation target, and the absence of any positive-length
  `DEntry` together --- the pairing the six-form model lost when its deriver
  moved, now held at the *declared* position rather than the old one. The
  congruence classes are forced, not chosen: `axLimitIsLimit` makes anything
  derivable from every finite position derivable from the limit, the finite
  tail occupies two classes, so a two-form limit cycle must occupy those same
  two --- which leaves every apply edge in the model changing class, and that
  is what supplies the absence. The clause that constrains the limit is the one
  that hands over the separation. The two models stay complementary rather than
  redundant: a position returning in two steps has `f2f^1 x = f2f^3 x`, so no
  single model can show both this and the finite-action disagreement, which is
  the argument `FiniteActionCountermodel`'s header already made. Wired as the
  audit's fourteenth process check with eight exact dependency reports; the two
  propositions carrying the target's own content depend on no axiom at all.
- **The cycle certificate is provably stronger than the target, not just
  described as stronger.** `DriverCycleWitness` has said of itself since it was
  written that it is stronger than `selfDerivation`, with
  `selfDerivationOfWitness` proving one direction and the note recording the
  converse as "not supplied"; the only obstruction in the development,
  `no_driver_cycle_witness_at_finite_successor`, needs the deriver to be finite
  and so has had no instance since the deriver was declared to be at the limit.
  `TargetAtLimitModel.target_does_not_yield_a_cycle_certificate` refutes the
  converse: all 39 clauses, the target, the cycle's endpoint closure, and no
  inhabitant of the certificate. What is missing there is only the path --- the
  `closes` field is available, since it is the conjunct that yields the target
  in the first place --- so proving the target leaves the retained edges still to
  be supplied, which is the thesis the note is named for. The refutation needs a
  model with the target and without any simulation edge, which is why neither of
  the other two supplies it: simulation is equality here and apply fixes no
  form, so an edge wanting `y = f2f x` and `Simulation y x` wants a fixed point.
  The certificate's docstring now cites the separation instead of asserting it.
- **And so the certificate is independent of the clauses, not merely open.**
  `cycle_certificate_independent` pairs the transport countermodel, which
  satisfies all 39 clauses with an inhabited certificate, against the
  target-at-limit model, which satisfies all 39 with none --- the same idiom as
  `congruent_symmetry_independent`, two carriers differing only in the length of
  the cycle at the deriver's position, which no clause mentions. It costs
  `propext` alone: importing the transport countermodel brings the theory's
  axioms into scope and the report shows none of them reaching this proof.
- **The same stale credit stood in three notes, and nothing could have caught
  it.** `CYCLE_BOUNDARY.md`, `CONSTRUCTIVE_QUINE_SELF_CLOSURE.md` and
  `CYCLE_WITNESSES.md` each credited `FiniteActionCountermodel` with satisfying
  the self-derivation target, which stopped being true when the deriver was
  declared to be at the limit. In two of the three, the *conclusion* --- that
  the target is independent of the clauses --- lost its positive half entirely,
  since both models those notes cited now refute the target. The name guard
  added last increment cannot see this: the sentences credit a model with a
  *property*, and two of them name no declaration at all, so every backticked
  name in them still exists. `test_no_note_credits_a_model_with_a_target_it_refutes`
  reads each model's verdict out of the type of its theorem rather than its
  name, pins the four verdicts, and refuses a present-tense sentence crediting a
  refuting model with the target; it fails on all three sentences as they
  actually stood, and on a model flipping its verdict in Lean. The corrections
  keep the withdrawn credit visible rather than quietly swapping the file name,
  and the independence conclusions are now carried by models that hold it.
- **The obstruction was never about finiteness, and the two models disagree
  about exactly one law.** `no_driver_cycle_witness_at_finite_successor` reads
  as a statement about where the deriver sits, and the declaration of its
  position at the limit looked like an escape from it. It is not.
  `FiniteSuccessorAgreement` restricts `ordinalSucc x = f2f x` to positions
  reachable from ground because that is where the correspondence was first
  wanted, not because the argument needs it: `SuccessorAgreement` drops the
  restriction, and `no_driver_cycle_witness_of_successor_agreement` then rules
  the certificate out with no hypothesis about the deriver at all. The proof is
  the same one line --- `axSuccExtends` denies `Simulation (ordinalSucc x) x`,
  agreement rewrites that to `Simulation (f2f x) x`, and that is precisely the
  second component of a `SimulationStep`, so every simulation edge everywhere is
  refuted and every `SimulationEntry` has length zero. A declared position
  cannot evade a law quantified over all positions.
- **Which turns the independence into a single question.**
  `certificate_tracks_successor_agreement` shows the two models of the previous
  bullet differ in this law and not in the clauses: the target-at-limit model
  takes `ordinalSucc := f2f` and satisfies agreement outright
  (`successor_agreement_holds`, no axioms), and has no certificate; the
  transport countermodel's successor is not its apply
  (`transport_successor_disagrees`, by `decide` at `a1`), and its certificate is
  inhabited. So the pair is not two unrelated carriers that happen to disagree.
  Asking whether the deriver's cycle closes is asking whether stepping the
  ordinal is applying --- a question about what apply means, which is the one
  thing the substrate laws never say (`Transfinite.apply_is_free`). The
  certificate is independent of the 39 clauses because the clauses are silent
  about `apply`, and adding either law settles it in one direction.
- **A `Trace` could be built and measured but never read back.** Every function
  on it -- `cons`, `compose`, `map`, `length`, `edges` -- either constructs a
  trace or summarises one; nothing recovered an edge's evidence from a trace, so
  an argument about a trace of a stated length had to be made by induction with
  the endpoints left variable. `Trace.eq_of_length_zero` and
  `Trace.uncons_of_length_succ` are the missing eliminators, both axiom-free,
  and they are what lets a trace between two *named* forms be decomposed.
- **With them the cycle certificate is exactly three propositions.**
  `driverCycleWitness_iff` proves `Nonempty DriverCycleWitness` equivalent to
  `Simulation (f2f deriver) deriver`, `Simulation (f2f (f2f deriver))
  (f2f deriver)` and `driverCycleClaim`. The right-to-left half was already
  there as `driverCycleWitnessOfSteps`; the missing half is the one that makes
  the comparison with the target a measurement instead of a look at the fields.
  Since the third conjunct *is* the target, by
  `selfDerivation_iff_driverCycleClaim`, the gap between the two is precisely
  the two retained edges. The equivalence depends on four source parameters and
  no axiom at all: it unfolds the definitions rather than using the theory.
- **And the endpoint closure is the part the target already gives.**
  `SimulationTransitive` states transitivity of `Simulation` as a hypothesis --
  no clause asserts it, since every clause naming `Simulation` relates it to
  another relation and never to itself -- and
  `driverCycleWitness_iff_of_transitive` shows that under it the closure follows
  from the two edges, leaving the certificate equivalent to the edges alone.
  Both models of the independence result are transitive
  (`simulation_is_transitive`, and the transport countermodel's
  `simulation_is_equivalence`), so
  `cycle_certificate_independent_under_transitivity` carries the same
  independence with transitivity added to the clauses. The open question is
  therefore about the intermediate steps and never about the closure.
- **The certificate that existed was standing still, and now one moves.**
  `transport_cycle_is_degenerate` records that the transport countermodel, the
  positive side of both independence pairings and for most of this development
  the only inhabited certificate anywhere, has `f2f deriver = deriver`.
  `driverCycleWitness_of_fixed_deriver` shows what that costs: at a fixed point
  both retained edges and the closure are instances of reflexivity of
  `Simulation` at the deriver, so the certificate is free and witnesses no
  cycle. The independence results are unaffected and were never overstated in
  Lean, but a reader taking the pairing to mean *a cycle is consistent with the
  clauses* was reading more than it said, because the certificate type cannot
  distinguish an edge that moves from an edge that stays.
- **`lean4/Hypermath/NondegenerateCycle.lean` added**: seven forms, a finite
  tail reachable from ground and a two-form limit cycle `l0 -> l1 -> l0`
  carrying the deriver at `l0 == ordinalLimit`, with both cycle forms in one
  semantic class so the retained edges hold across a step that moves. It
  satisfies all 39 clauses, `apply_moves_the_deriver` is decidable, and
  `cycle_certificate_independent_nondegenerately` pairs it against the
  target-at-limit model, where apply also moves the deriver and no certificate
  exists. The independence is therefore not an artefact of a fixed point. The
  model is shaped by the same law the obstruction is about: `axSuccExtends`
  forbids `ordinalSucc` from being apply at the deriver, so the successor here
  sends everything outside the tail back to ground's chain.
- **Five independence claims were being asserted over one half of a pairing.**
  A countermodel is half of an independence result; the other half is a model
  satisfying the same statement, and only the conjunction licenses the word.
  Five claims in the notes had the word without the conjunction, in two
  different shapes. The self-derivation target was called independent while both
  cited models *satisfied* it --- satisfiability twice over, with the refuting
  model named in the same paragraph and described as a loss. Four rows of the
  admission table in `docs/research/CLAUSE_INDEPENDENCE.md` were marked
  `independent` while naming the refuting model alone, or naming both halves
  separated by a slash and leaving the conjunction to the reader. Nothing failed
  in Lean, because every theorem cited was true; what was wrong was the sentence
  over them.
- **The five are now declarations.** `self_derivation_independent`
  (`lean4/FiniteActionCountermodel.lean`), `similar_reflexivity_independent` and
  `similar_symmetry_independent` (`lean4/Countermodels.lean`), and
  `directionality_independent` and `distinct_operations_independent`
  (`lean4/FullAxiomModel.lean`), each stating
  `(ModelA.Axioms and P) and (ModelB.Axioms and not P)`. Two of them gained
  strength while being written: directionality and the distinctness of `+` and
  `additionally` were independent of the 24-clause L0/L1 prefix and are now
  independent of all 39 clauses, because the pairing had to be stated against
  `HypermathTransportCountermodel` --- `lean4/lakefile.toml` compiles only
  `lean4/Hypermath/`, so a top-level file cannot import another top-level file,
  and the library model is the one reachable from both sides.
- **The README's admission census disagreed with the table it summarizes.** It
  counted five admissions as independent and described
  `plusAndAdditionallyAreDistinct` as blocked on an undeclared clause; the table
  had marked it independent, and `distinct_operations_independent` now settles
  which is right. Six are independent, one is refuted outright, one is closed a
  layer later.
- **`test_an_independence_claim_names_a_pairing` added.** A theorem named
  `*_independent` has to state two parenthesized halves joined by the only
  conjunction at depth zero, with the negation in exactly one; a paragraph
  claiming independence from the clauses, if it cites a declaration at all, has
  to cite one so named. The shape rule is what separates the two errors above
  from a correct statement --- both of them contain a conjunction and a
  negation, so any weaker reading passes them.
- **The nine-cell grid is nine declarations.** The table of three relations by
  three properties in `docs/research/CLAUSE_INDEPENDENCE.md` wrote `independent`
  in all nine cells, and four of them were declarations. The five that were not
  followed from the freedom theorems in the same section, which settle whole
  rows at once and are stronger than any cell --- the reading was sound, and
  that is what made the gap invisible. `similar_transitivity_independent`,
  `congruent_reflexivity_independent`, `simulation_reflexivity_independent`,
  `simulation_symmetry_independent` and `simulation_transitivity_independent`
  close it, each pairing the Bool model at the head of
  `lean4/Countermodels.lean` --- where `~~` and `=~` are `True` and the
  simulation relation is equality, so all nine properties hold at once --- with
  the model that refutes the cell. All five cost `propext` and `Quot.sound`.
- **The grid names follow a convention that is itself checked.** The nine are
  `<relation>_<property>_independent` over `similar`, `congruent`, `simulation`
  and `reflexivity`, `symmetry`, `transitivity`, which renamed two theorems from
  the increment above, and `test_the_nine_cell_grid_is_nine_pairings` builds the
  nine names from the two lists rather than reading them from a third. A tenth
  cell now needs a name of that shape and a theorem of the pairing shape before
  it can be written into the table.
- **What the 24 clauses say about `~~`, which nothing had asked.** Every
  characterization in `lean4/Countermodels.lean` holds the bottom relation
  fixed: the two freedom theorems fix two relations to answer about the third,
  and `total_similar_leaves_exactly_three_conditions` fixes `~~` total to answer
  about the two above it. The relation the others are measured against was never
  the subject. Taking the upper two to their minimum instead --- both equality,
  which the freedom theorems say is allowed --- gives
  `minimal_upper_relations_leave_five_conditions_on_similar`, an axiom-free iff
  on an arbitrary carrier: `~~` is reflexive, relates every image to its source
  and to ground, relates every double image to its source, the ground chain is
  `~~`-cofinal, and forming never returns to ground. Five conditions on `~~` and
  one on forming, against three at the other corner. **The upper two relations
  are free above equality and `~~` is not free at all**, so the filtration's
  content is at the bottom and not, as its shape suggests, at the top.
- **All six of those conditions are irredundant.** An iff says what the
  conditions are and nothing about how many facts they are, so the comparison
  above --- five conditions against three at the other corner --- needed six
  models before it was a measurement. `five_hold_without_similarReflexive`,
  `five_hold_without_imageSimilar`, `five_hold_without_imageSimilarToGround`,
  `five_hold_without_doubleImageSimilar`, `five_hold_without_chainIsCofinal` and
  `five_hold_without_formingAvoidsGround` drop them one at a time. Four are
  relations on the chain; two are not available there at all. Cofinality needs
  the carrier with an adjoined point, and forming returning to ground needs the
  one-point carrier --- so the carrier had to be left open for a second reason,
  which was not among the reasons it was left open. This also relocates
  `Hypermath.globalCongruentReflexivityIsCofinality`: the chain reaching
  everything is not a consequence of what the clauses say about `=~`, which is
  why it survives trivialising both upper relations.
- **`SimilarConditions` and a guard over its fields.** The six are a structure
  now, and `test_the_lower_corner_conditions_are_each_dropped` builds the six
  theorem names from its field names, so a seventh condition needs its model
  before the structure typechecks against the guard.
- **The other corner said three in its name and four in its statement.**
  `total_similar_leaves_exactly_three_conditions` collapsed the eight
  conditions with `~~` total, and the right-hand side of its iff carried four
  conjuncts: `≡ ⊆ =~`, `=~` reflexive, `≡` reflexive, and `≡` denying every
  image at ground. The sentence that read it off in this file and in
  `docs/research/CLAUSE_INDEPENDENCE.md` said "both reflexive", which is two
  conditions spoken as one, so the name and the prose agreed with each other
  and neither agreed with the theorem. Nothing was false anywhere:
  `congruent_reflexivity_is_not_a_fourth_condition` derives reflexivity of `=~`
  from the other two, so the iff held with the conjunct and holds without it.
  The statement now has three conditions and the name is a measurement.
- **`TotalSimilarConditions`, and the three are irredundant.**
  `two_hold_without_simulationIntoCongruent` takes `≡` to be equality with one
  extra pair from ground to the first rung, `two_hold_without_simulationReflexive`
  takes `≡` empty, and `two_hold_without_imageNotSimulatingGround` takes `≡` to
  relate everything into ground. All three are axiom-free. The comparison the
  note draws between the corners --- five conditions on `~~` at one, three on
  the pair at the other --- is now between two measured counts rather than
  between two ways of writing a list.
- **Both corners are guarded by one test, and by a second over their shape.**
  `test_the_lower_corner_conditions_are_each_dropped` became
  `test_each_corner_condition_has_a_model_that_drops_it`: it reads the fields of
  both corner structures and builds each drop name from the field and from how
  many fields remain, so neither corner can gain a condition without a model.
  `test_a_corner_states_its_conditions_as_a_structure` requires the right-hand
  side of both iffs to be a structure and not a conjunction. That is the shape
  that let the fourth conjunct in --- a conjunct can be added to a conjunction
  with no other change anywhere, and a field cannot be added to a structure
  without a name and a model.
- **The reader those guards use was reading prefixes.** Three guards over
  `lean4/` take a theorem's statement by cutting its text at the first `:=`.
  Lean spells a named argument the same way --- `ComposeAxioms (Form := Path)`
  --- so twenty-eight statements were being cut inside a bracket, and
  `four_fold_without_transitivity` was taken to say `ComposeAxioms (Form`. A
  truncated statement is still a string: it splits, it has a head, it answers
  every question a guard asks it. `_before_proof` now cuts at the first `:=` or
  `where` outside every bracket, and
  `test_every_statement_the_guards_read_is_a_whole_statement` requires balanced
  brackets and no `where` in what the reader returns.
- **One of the three was failing open, which was checked rather than assumed.**
  Giving the upper corner the right-hand side
  `TotalSimilarConditions (C := C) E ∧ (∀ x, C x x)` --- no parentheses needed,
  since `↔` binds looser than `∧` --- cut it to `TotalSimilarConditions (C`,
  which has a structure at its head and no conjunction in it, so
  `test_a_corner_states_its_conditions_as_a_structure` passed on exactly the
  defect it was written to catch. It fails on that statement now. The guard
  above is the durable part: it does not know what any theorem says, only that
  what the reader hands over is a whole one.
- **The upper corner was a chain theorem that never used the chain.**
  `total_similar_leaves_exactly_three_conditions` was stated over `Chain`, and
  its docstring gave the carrier as the reason the two diagonal conditions turn
  into plain reflexivity. That is the wrong reason.
  `total_similar_makes_reach_total` added: the ground chain reaches every Form
  as soon as `~~` is total, on any carrier, from no condition at all, because
  `Reach` asks for an iterate of ground that the relation connects to `x` and a
  total relation connects the first one. The corner is now stated over an
  arbitrary carrier and an arbitrary ground and forming, like the other one, so
  the comparison between them is between two statements of the same kind.
- **Two routes to cofinality that had been read as one.**
  `reach_is_total_on_the_chain` gets the ground chain reaching everything out of
  the carrier and needs the third condition to do it;
  `total_similar_makes_reach_total` gets it out of the relation and needs
  nothing. Treating the first as the reason for the second is what put the chain
  into a theorem that never used it. It also explains the shape of the two
  corners: the upper one is carrier-free because a total `~~` empties `Reach`,
  and the lower one is not because equality at the top turns `Reach` into
  cofinality exactly, which is `five_hold_without_chainIsCofinal`.
- **What the eight forbid, which nothing in the file had asked.** Every earlier
  result exhibits relations --- freedom at the top, a count at each corner, a
  model per grid cell --- so the clause set read as though it ruled almost
  nothing out. `ground_is_not_a_fixed_point`: in any model of the eight, on any
  carrier, `f2f ground ≠ ground`. If forming fixed ground the second condition
  would put ground under `~~` with itself, the ground chain would reach ground
  at its zeroth iterate, and the eighth condition would give `≡` on the diagonal
  there, which the sixth denies. Three of the eight, and nothing else.
- **`~~` is never equality.** `similar_is_never_equality`, immediately: equality
  makes the second condition say forming is the identity. The two relations
  above `~~` may both be equality --- that is the lower corner --- and the one
  below them may not be, so "`≡` and `=~` are free above equality and `~~` is not
  free at all" was understating it. `~~` is kept off the bottom of the lattice
  of relations entirely: **the clauses require the filtration to identify
  something.**
- **The inclusion `≡ ⊆ =~ ⊆ ~~` is always strict, and strict at neither link by
  necessity.** `similarity_is_not_contained_in_simulation` derives the composite
  strictness from conditions 3 and 6 with no model at all, and
  `the_three_relations_are_never_all_one` is the corollary worth naming: the
  clause set cannot be read as one relation under three spellings.
  `congruent_may_equal_similar` is a new model where `=~` is `~~` outright, and
  `neither_inclusion_is_forced_to_be_strict` pairs it with `ext_conditions`,
  where `=~` is `≡` instead. Either link may collapse; both may not.
- **The file already had that theorem, a thousand lines away.**
  `ground_is_not_a_fixed_point` was written as a new result; the general form,
  `ground_is_not_an_image`, had been sitting in the transfinite section since it
  was needed there as a lemma for `axLimitNotFinite`, with a docstring noting
  that the prefix clauses constrain the carrier too. Lean caught it only because
  both proofs chose the same name. The theorem is moved to the section whose
  question it answers, the fixed-point case is a one-line corollary of it, and
  the prefix section no longer claims nobody had asked.
- **A guard for the case Lean cannot catch.**
  `test_no_proposition_is_proved_twice_for_the_same_price` groups every theorem
  of `Countermodels.lean` by namespace and by its statement with binder style and
  bound names normalized away, and requires the members of any group to differ in
  what their proofs spend. The vocabulary pair passes --- that is the one place a
  second proof is the point, and it costs `propext` less. A re-proof under a
  second name fails, which was checked by writing one. Grouping by namespace is
  required rather than tidy: three model namespaces each prove a `succ_moves`
  whose source text is identical and whose subject is their own carrier.
- **The eight say how small the carrier can be, and it is two.** An image is a
  Form that is not ground, so `no_model_on_one_point`; and
  `two_points_are_enough` builds the model with forming constant at the
  non-ground Form, `=~` and `≡` at equality and `~~` relating the image to
  everything, so `two_is_the_smallest_carrier` closes it exactly. Before this
  every result in the file left the carrier arbitrary.
- **Corrected: `axLimitNotFinite` is not the first clause to bound the carrier.**
  `the_limit_is_off_the_chain` claimed it was. The prefix eight already demand a
  second Form. What the limit clause demands is a point off the chain --- a
  different demand, not a larger one in the same direction. Two sections claimed
  a first because neither could see the other, which is the reproof again, one
  level up in the prose.
- **The transfinite layer costs one more Form, and not an infinite one.**
  `no_limit_on_two_points` refutes every two-Form model of the nineteen ---
  ground, its image and the limit are three distinct Forms, by
  `ground_is_not_an_image` and by `the_limit_is_off_the_chain` at the chain's
  zeroth and first positions --- and `ThreePointLimit` exhibits all nineteen
  conditions on `Fin 3`: forming constant at the image, the successor the
  three-cycle, `~~` and `=~` total, `≡` equality.
  `three_is_the_smallest_carrier_with_a_limit` closes it.
- **So "transfinite" is a name, not a demand on the carrier.** The layer's only
  model in this file is `Option Nat` and its name says infinite, which is what a
  reader assumes. `axLimitNotFinite` asks that no position of the chain simulate
  the limit, and a chain that stops moving has one position after its first
  step. `spanned_carriers_admit_no_limit` is the nearest thing to the assumption
  and it is weaker: a carrier the chain *exhausts* admits no limit, which a
  constant forming satisfies on three points without exhausting them. Eight
  conditions cost two Forms, nineteen cost three, and the eleven between them
  cost none --- the operations because their witnesses may all be ground, the
  composition because its carrier is one of paths.
- **The paths are a second carrier, and it holds two.** Two of the three
  composition conditions are equations one path satisfies; `unitalUpToCp`
  relates `comp p e` to `p`, which on one path is `cp` between the unit and
  itself, exactly where `someNonUnit` demands a path at which `cp` fails ---
  `no_compose_on_one_path`. `two_paths_are_enough` uses disjunction and `false`,
  the smallest monoid with a non-unit, so `two_is_the_smallest_path_carrier`.
  `compose_conditions_are_always_available` had said the layer excludes nothing;
  this says what it costs, which is one path more than nothing.
- **So the whole clause set fits in three Forms and two paths.**
  `ThreePointLimit.all_nineteen_conditions_hold` and
  `three_is_the_smallest_carrier_with_a_limit` now carry `Bool` paths rather
  than `Nat`, and neither number can be reduced. Every model in the file before
  these used an infinite carrier for one side or both, and none of them had to.
- **Only the prefix eight demand a Form at all.**
  `operation_conditions_hold_on_one_point`: every witness the operations ask for
  may be the ground and their one negative field is vacuous when `=~` is total.
  `transfinite_conditions_hold_on_one_point`: ground and limit the same Form,
  forming and the successor the identity on it, `~~` and `=~` total and `≡`
  empty, which satisfies `limitNotSimulatedFinitely` with an empty relation
  rather than a large carrier. The layer named for the transfinite asks least of
  the carrier of the three. `only_the_prefix_demands_a_second_form` pairs the
  three.
- **The third Form is demanded by neither layer and by both together.**
  `the_third_form_is_a_joint_demand`: the eight have a two-Form model, the
  transfinite conditions have a one-Form model, their conjunction has no
  two-Form model. That is a second failed join with a new reason ---
  `nineteen_is_not_fourteen_plus_five` fails because one side fixes relations
  the other must meet, and this one fails on the carrier, where each side is
  satisfiable at a size and the size at which both are is larger than either.
- **Both ends of the lattice of relations, for all three.**
  `similar_is_never_equality` had kept `~~` off the bottom and said nothing
  about the top. `simulation_is_never_total` is the other impossible corner and
  the cheapest one in the file: the sixth condition denies `≡` between an image
  and the ground, and a total relation denies nothing --- no carrier, no second
  condition. `total_congruent_forces_total_similar` fills the cell that could
  have been its own case, since a total `=~` drags `~~` up with it by the fifth
  condition. `the_extremes_of_the_three_relations` states all six settings
  together; four hold.
- **One cause at each end.** `~~` cannot be smallest because `imageSimilar`
  makes it relate an image to something it is not; `≡` cannot be largest because
  `imageNotSimulatingGround` makes it fail somewhere. The clause set requires
  the bottom relation to identify and the top relation to distinguish, and asks
  neither of the middle one. "The upper two relations are free above equality
  and `~~` is not free at all" reads more sharply as: `=~` is free at both ends,
  `≡` only downwards, `~~` only upwards.
- **And the guard for the grid had the defect it was written to catch.**
  `test_the_nine_cell_grid_is_nine_pairings` found its table by scanning the
  whole note for lines beginning with one of the three relations, which named
  the grid only for as long as the grid was the only table with those row
  labels. The new six-extreme table is a second one, and the guard reported six
  rows where the grid has three --- a true count of a table it had no way to
  tell from its own. It now finds the section by its heading and reads rows only
  inside it. A fail-open control confirms it still fails on a grid row dropped
  and on a grid row doubled.
- **At two Forms the eight decide the forming map outright.**
  `imageNotSimulatingGround` constrains forming only by a denial, and at two
  Forms a denial of one value names the other, so every model of the eight over
  `Bool` has the same forming map --- `forming_is_forced_at_two_points`. It
  follows that reachability is total, that both upper diagonals are total
  (`both_diagonals_are_forced_at_two_points`), and that three of the four cells
  of `~~` hold (`similar_is_forced_off_one_cell_at_two_points`).
  `eight_cells_are_forced_at_two_points` counts the consequence: eight of the
  twelve relation cells are the same in every model over two Forms.
- **The other four cells are free, and four models show it.**
  `two_points_are_enough_with_total_congruent` joins the three already there;
  the four differ pairwise at the ground-to-image cell of `~~`, at both
  off-diagonal cells of `=~`, and at the ground-to-image cell of `≡`.
  `the_eight_decide_forming_and_eight_of_twelve_cells` carries the forced half
  and the four models in one statement: at its smallest carrier the clause set
  is one model wide in its operation and four cells wide in its relations.
- **And the rigidity is the size's, not the clause set's.**
  `forming_is_not_forced_at_three_points` gives two models over three Forms
  alike in ground and in all three relations and different in forming.
  `two_points_determine_forming_and_three_do_not` pairs the sizes. A clause set
  that constrains an operation only negatively determines that operation
  exactly at the carrier where one value survives the denial, so minimality and
  rigidity coincide at the bottom and come apart one step above it.
  Satisfiability at a size and freedom at that size are different questions,
  and the carrier-size results before these asked only the first.
- **The reader the statement guards share was losing 89 of 1052
  declarations.** It was keyed by the bare name, and lost them two ways at
  once: the declaration regex stopped at the first dot, so the four theorems
  named `Alignment.<something>` shared one key, and 55 bare names are declared
  more than once across `lean4/` --- `reach` eight times --- so the dictionary
  kept whichever came last. Keys now carry the module and the enclosing
  namespaces and are unique by construction;
  `test_the_statement_reader_sees_every_declaration` compares the entry count
  with the sources, and a fail-open control confirms it catches either defect
  alone and both together.
- **What hid it was a floor.** The reader was checked with `> 500` entries,
  and 963 and 1052 give that the same answer, so the guard whose own subject is
  readers that fail open was reading five sixths of what it named. Lookups by
  bare name are still available through `_statement_named`, which asserts that
  the answer is one theorem instead of assuming it, and `_pairing_statements`
  now asserts that no two independence results share a bare name rather than
  relying on the fact that none do.
- **And a number in a docstring was wrong.** `_qualified_statements` said the
  bare-name reader dropped one of nine colliding pairs. It dropped 89
  declarations. The figure had been written rather than measured, which is the
  defect this whole document is about, in the file that documents it.
- **Eleven declarations across `lean4/` carry five propositions.** With the
  reader repaired, the duplicate-proposition question reaches past
  `Countermodels.lean` for the first time, and two other files have the same
  shape: `L2Operations.lean` states three source obligations twice, once under
  the operation each belongs to and once under its `nc<n>_L2` name, and
  `FullAxiomModel.lean` discharges five clause names with two proofs because
  three of those names are one clause and two more are another.
- **All eleven are wanted, and that is why they needed declaring.** A model
  discharging `axSeqIdentityL` should say so under that name whether or not
  `axSeqIdentityR` is the same statement. `ALIAS_FAMILIES` and
  `test_the_alias_families_are_the_declared_ones` pin the five sets by
  qualified name, so a twelfth has to be written down before it can exist and a
  family that stops being one fails too. A fail-open control confirms both
  directions. `sequencingClausesAreCooperationClauses` had said it in prose for
  three of the eleven; the other eight had nothing.
- **The 198 paths the documents cite were held by nothing.** Names the notes
  credit have been checked since `full_clauses_and_target_without_nonzero_D`;
  where those names live was not, so a file that moved would have left every
  sentence citing it silently wrong.
  `test_every_path_the_documents_cite_is_one_that_exists` resolves each cited
  path as the tail of a path some readable checkout carries --- 193 of 198 ---
  because a sentence names a file by as much of its path as it needs.
- **The five that do not resolve are pinned with the reason.** Three are build
  outputs, one is in the verifier-standard sources, and one is not written. The
  imported documents under `references/precursor/` are excluded because their own
  manifest pins them by sha256, and the exclusion is read out of that manifest,
  so unpinning a snapshot puts its five broken links back under the guard.
- **And a claim that expires when the work is done.** Three documents cite
  `lean4/Hypermath/ConstructiveQuine.lean` precisely because it does not exist.
  `test_the_construction_the_documents_call_unwritten_is_still_unwritten` holds
  the file's absence and the sentences that state it together, since either
  half alone fails open. Every other guard here catches prose that fell behind
  its sources; this one catches prose the sources caught up to. A fail-open
  control confirms all six directions.
- **A credited name that is a file now resolves as one.** The set
  `test_every_name_the_notes_credit_with_a_result_exists` resolves against was
  built from the Lean sources, so `Countermodels.lean` resolved and `README.md`
  did not, though "`README.md` records that" and "`Countermodels.lean` records
  that" are the same sentence shape. It now carries every file name in the
  readable checkouts, because a credited name that is a file is a claim the
  path guard holds.
- **The guard roster is no longer kept by hand.** The total at the head of it
  had been raised manually at the end of every increment and checked by
  nothing, and one pointer had gone stale --- the note named
  `test_each_condition_has_a_model_named_for_it`, which became
  `test_each_condition_is_either_refuted_or_derived` when a condition could
  first be answered by a derivation instead of a model. The claim was never
  unheld, only the name a reader would look for. Now every guard named in
  `docs/` or the README has to exist and the roster's total has to equal what
  it names. `CHANGELOG.md` is excluded on purpose: an entry should keep the
  name a guard had at that release. Every heading inside the roster is checked
  too, which found one: "One holds the admission" stood over a pair. The total
  was right while one of its parts was wrong, which is the durable form of this
  error, since the total is the only thing anyone rechecks.
- **The crediting vocabulary was a floor, and a floor cannot see a leak.** The
  name guard asks whether a name exists only when one of seventeen verbs
  follows it. Those verbs reach 171 of the 940 words that follow a name in
  `docs/research/`; `says`, `satisfies`, `requires`, `supplies`, `retains`,
  `preserves`, `exhibits` and `asks` are among the ones they miss, and roughly
  ninety sentences credit a name in words nobody wrote down. A name in any of
  them could have been deleted from the sources with nothing noticing.
  `test_every_name_the_notes_cite_resolves_or_is_classified` drops the
  vocabulary and holds all 847 cited identifiers instead.
- **The 51 that do not resolve are classified, and two kinds are checked.** Lean
  core, another project's, a value in a table, a binder, not written, or
  withdrawn from the sources and cited *because* it is gone. A name called
  withdrawn has to be called that by a Lean comment, and a name called
  superseded has to have its replacement still declared --- which caught four of
  this increment's own classifications: `driverInDAtSimulation`,
  `ordinalZeroIdentity`, `ordinalSuccApplies` and `pathLengthArithmetic` were
  replaced, not dropped.
- **The Lean name reader had never read a structure's fields.** It reads the
  line a declaration starts on, and a field or an inductive's constructor is not
  on it, so 219 names did not exist as far as the guards were concerned ---
  including the eight `Conditions` fields that `CLAUSE_INDEPENDENCE.md` cites
  more than any other names in the project. The Python name reader read one
  module of the package because that is where the first such citation happened
  to be, leaving 47 of the package's 89 constants outside. Neither could be seen
  through the vocabulary, since no sentence credits a field with proving
  anything: a narrower reader and a narrower question hid each other.
- **A name can be declared twice, and the control is what said so.** Renaming
  `ordinalZeroIdentityClaim` in `L3Ordinatics.lean` left it resolving, because
  `FiniteActionCountermodel.lean` declares the proposition too --- the layer
  advertising the claim and the countermodel refuting it each state it in their
  own namespace. A fail-open control confirms all six directions.
- **The list of withdrawn names was one name, written by hand, under a plural
  docstring.** `driverCycleIsClosed` was the name being cited as a discharge
  when `test_withdrawn_names_are_not_cited_as_proofs` was written, so it was the
  name the guard held. It is one of eight: `simulationPairExists`,
  `dSpansGround`, `driverCycle_FRAME`, `conditionalRetrace`, `Abstraction`,
  `abstractionTransitive` and `syntaxToAbstraction` are retired by these sources
  too, in sentences that say so, and any of the seven could have been cited as a
  proof with nothing objecting.
  `test_the_retired_names_are_read_out_of_the_sources` reads them instead of
  listing them, and pins the count at eight so a ninth has to be recorded.
- **The reader is a sentence and the sentence before it, and both neighbours are
  wrong.** A line reader finds five of the eight, because the sentence retiring
  `Abstraction`, `abstractionTransitive` and `syntaxToAbstraction` runs across
  three lines and names them on the first two. A sentence reader finds seven,
  because "Step 16: driverCycleIsClosed. There is no such theorem, here or
  anywhere." puts the name in the sentence before the retirement. A comment-block
  reader would find far too many: §IX of `L3Ordinatics` is one block of sixty
  lines carrying two retirements, and reading the block retires every name the
  census mentions.
- **A majority of this project's discharge claims were outside the subject of
  the guard that checks them.** The Lean comments claim a discharge on 52 lines;
  the documents claim one on 89, across 22 files, and nothing read them.
  `test_the_documents_claim_more_discharges_than_the_sources_do` states that as
  a measurement, and
  `test_every_discharge_the_documents_claim_names_something_that_exists` asks
  the prose the two questions the comments have been asked all along --- the
  name exists, and it is not one the sources retired. The prose passes both
  today, which it had been doing by luck. A fail-open control confirms all seven
  directions.
- **Backticks are positional and a regex cannot pair them.** In "the withdrawn
  `conditionalRetrace`, which was `fun _ _ _ hWit => hWit`" the first backticked
  span containing a space is `, which was `, so a regex that blanks quoted terms
  blanks the wrong one and leaves the term exposed, reading `hWit` as a retired
  name. Splitting on backticks by position gets it right: a span with a space is
  a term, and a name inside a term is part of the term.
- **One reader for "a name this project offers", instead of three.** Two guards
  were assembling that set themselves, in two orders, one carrying a comment the
  other needed, and this increment was about to add a third. `_known_names` is
  the reader; a set assembled in more than one place is the same error as a
  count kept by hand, which is the error this increment is about.
- **The one document that tells the suite what to do was read by nothing.**
  `AGENTS.md` §8 says every skipped test MUST disclose its rationale against a
  rubric of definitional categories, and `.github/PULL_REQUEST_TEMPLATE.md`
  states the same rubric. No test opened either file. Every guard in this suite
  holds prose to sources; `tests/test_stated_process_rules.py` holds the
  sources to the prose, which is the same claim from the other side and had no
  guard at all. All three of this repository's skips failed the rule the first
  time it was applied.
- **None of the eight categories fits a test that does not apply.** One skip was
  always `OPTIONAL_DEPENDENCY_ABSENT` and said so in other words. The other two
  skip a document that is a dated record of an earlier commit, whose numbers
  describe that commit --- the test cannot fail, because there is nothing about
  today for it to be wrong about. Read the eight in a row and every one is a
  reason the *measurement* is unavailable: an absent capability, dependency,
  service, architecture, device or privilege, a defect quarantined, a duration
  excluded. Not one is a reason the *subject* is. A checklist that does not
  cover the cases in front of it cannot be satisfied honestly, only quietly, so
  the rubric gained a ninth in both documents: `DATED_RECORD_BOUNDARY`.
- **A vocabulary written down twice is two claims.**
  `test_the_skip_rubric_is_stated_the_same_way_twice` holds them against each
  other. The names had not drifted; five of the eight glosses are worded
  differently, and that is prose. The template carries one entry that is not a
  category --- `NOT_APPLICABLE`, the box ticked when nothing was skipped ---
  and counting it as one would make "every skip names a category" satisfiable
  by a run with no skips in it.
  `test_the_rubric_categories_the_skips_use_are_ones_that_apply` requires a
  named category to be one the source can show, because a claimed
  `QUARANTINED_DEFECT` with nothing quarantined reads as disclosed and is worse
  than an undisclosed skip. A fail-open control confirms all six directions.
- **Skips are read from the syntax tree.** A skip is a call and a decorator,
  not a line, and a reason assembled at runtime is not one a reader of the
  source can check, so a non-literal reason counts as undisclosed. A rubric
  category is also a name, declared in `AGENTS.md` the way the Lean sources
  declare theirs, so `_known_names` now carries the vocabulary and a document
  citing `QUARANTINED_DEFECT` is citing something that exists.
- **The kernel axiom count was stated twice and wrong in both places.**
  `AGENTS.md` said "eighteen kernel axioms" in §1's table row and again in §5,
  where the sentence is "keep the source assumption inventory matching
  `_baseline.py` exactly". `AXIOM_DECLARATIONS` holds sixty-one, and
  `lean4/Hypermath/` declares exactly those sixty-one with the `axiom` keyword
  --- the symmetric difference is empty. Both sides of the sentence agree with
  each other and neither agrees with the number in front of them. No subset
  reconstructs eighteen: twenty-one are `ax`-prefixed, twenty-three with the
  filtration pair, thirty-five are definitions, eleven are L0's logical
  clauses. `test_the_axiom_count_the_policy_states_is_the_inventory_it_names`
  now holds the stated number to the inventory and the inventory to Lean.
- **A check that runs and is not described is the mirror of a rule stated and
  not enforced.** §6 said what `scripts/check_presentation.py` checks and named
  four of the five it runs; `check_lineage_claims` has been in CI as long as
  the others and was in no description of the gate. The first reader for this
  matched a description to a check by the words in the check's name and
  reported four of five unlisted, because `check_versions` against "version
  agreement" fails on a plural --- so §6 now cites each check by name and
  `test_the_presentation_gate_lists_every_check_it_runs` requires the citation.
- **"`.gitattributes` forces `eol=lf`" is a claim about the index.** On the
  disk it is false: twenty tracked files carry CRLF, among them `LICENSE`,
  `L0_ground.hm` and every `docs/terms/*.md`. Nothing sees it --- git
  normalizes on read and Python's text mode translates newlines --- and
  nothing that matters reads there: the source archive comes from `git
  archive`, which reads the index, and `_normalize_newlines` handles the rest.
  In the index the invariant holds, and its exceptions name themselves: the
  only index bytes with CRLF are the `references/precursor/` snapshots that
  `.gitattributes` marks `-text` so their sha256 pins hold.
  `test_the_line_ending_invariant_holds_where_the_release_reads_it` says which
  side of that distinction the sentence is about. Four files drifted this
  way while the entry recording it was written, and nothing reported them.
- **A total claimed in prose must be wholly in prose.** The totals reader asked
  whether the *number* was inside a quotation and not whether its noun was, so
  a section reference outside a quotation bound to a counted noun inside one
  and reported a stale figure that no one had written. It is the same mistake
  as pairing backticks by count rather than by position: a reader that does not
  know where a phrase ends. Both prose counters now require the whole phrase to
  be unquoted, and a control confirms a wrong total in plain prose is still
  caught while the same sentence inside quotation marks is still allowed.
- **The layer language had never been read.** `L0_ground.hm` through
  `L3_ordinatics.hm` are the specification the Lean development formalises, and
  every reader in the suite treated them as sha256 inputs and fixture
  filenames. Reading them found three axiom names the dictionary cites that no
  layer ever declared: `ax-sem-nec`, `ax-sub-nec` and `ax-syn-nec` are short
  forms someone wrote in prose for `ax-semantics-requires-syntax`,
  `ax-substance-requires-semantics` and `ax-syntax-requires-substance`. Every
  sentence around them was true --- each cited edge is the edge its declaration
  states --- and the only thing wrong was that the names did not exist. They
  are corrected in the dictionary and may now be written only where the drift
  is being recorded, never where citing one is the claim.
- **A grammar is wrong in two directions at once.** A reader that knows only
  `axiom` misses the eighty-five names `derive` introduces and calls them
  undeclared; a reader that matches names anywhere finds
  `ax-syntax-precedes-semantics`, which exists only in the comment recording
  its own retirement, and calls it declared. Neither is the smaller mistake, so
  every left-margin statement must now parse under a known form and yield the
  name it introduces, which is what keeps the citation check from answering
  "nothing is missing" for free.
- **A count standing next to its own evidence can just be counted.**
  `L0_ground.hm` said "The five axioms" and named seven of them in the same
  sentence, ninety lines above the block calling them "Seven Section VIII
  axioms". No audit is needed for that and no existing counter would have found
  it: they hold a number against a measurement. Where the phrase *begins* is
  the difficulty here, as where it ended was last time --- the count nearest a
  parenthesis is not always the count the parenthesis belongs to, so a clause
  carrying more than one count is declined rather than guessed at.
- **The guard passed on the real defect the first time it was written.**
  Wrapped lines are joined with a space, which carried a layer comment's marker
  into the middle of the list and made the whole claim look like prose.
  Blanking the marker without changing the length of the text is what made the
  list readable while keeping the reported line number true; a control now
  restores that defect and confirms the reader sees it.
- **Each layer keeps a census of itself and invited a parser to check it.**
  Every layer ends with a self-kernel: a numbered walk over everything the file
  declared. `L0_ground.hm` says outright that a future parser can evaluate the
  block mechanically against the file, and none ever had. Its length is written
  by hand in the layer header, the section banner, the closing block and the
  Lean file that formalises the layer, and three of those copies had drifted
  while the correct value stood elsewhere in the same file:
  `L2_operations.hm` indexed a census of 29 steps eleven lines under the line
  saying 39 and has 39 rows; `L3Ordinatics.lean` opened with 18 and closed its
  own self-kernel section with 20; and one census row named a derive one word
  short of the name its layer declares. All three are corrected, and the rows
  are now counted and every restatement held to them --- on the Lean side as
  well, which is the first check here to read a claim across that seam.
- **L2 states its census in comments and the language does not know it.** It
  indexes the section like the other three layers and calls it the closed
  structural census; there is no statement to close. Making those 39 rows a
  statement is specification content and is left alone. What is held is that no
  further layer goes the same way, with a control confirming the guard stays
  green if L2 is repaired and fires if the repair is half done.
- **Both new readers were wrong toward reporting a clean file.** The section
  banner was matched without its colon, so the reader began at a prose mention
  550 lines earlier and counted 58 census rows in a census of 41; and the
  census was read to the end of the file, so a declaration written after it
  counted as accounted for by it --- the guard passed the exact mutation it
  exists to catch. A census is what stands in its rows, and a row runs until
  the next row or the next statement.
- **Ten cross-layer discharge pointers named rows that had been renumbered
  out from under them.** A FRAME is a forward dependency stated out loud, and a
  later layer pays it off by citing the census row that opened it. That
  citation is a hand-written pointer into a numbered index that gets
  renumbered. `L3_ordinatics.hm` cited L1 step 26 and L1 step 30 four times
  each, and L1's census has 25 rows --- both were off by exactly five, landing
  on the `deriver` primitive at 21 and `D[deriver][deriver]` at `==` at 25. It
  cited L2 step 24 for `composition-length-additive`, which is step 25, and L2
  step 30 for the congruent-path internals, where step 30 states that it has no
  FRAME and step 37 is the close that carries the residual --- the same
  eight-row growth that left L2's section index claiming 29 steps. Every
  parenthetical named its target correctly and quoted the row almost verbatim,
  so all ten resolved without guessing. The obligations, the discharges and the
  rows were right; only the numbers pointed elsewhere.
- **A cited row must exist, and must be about what the citation says.** The
  first is asked of the layer files and the Lean sources both, since a row
  number needs no translation and the Lean side cites these rows eleven times
  in one hand-written run. The second is asked of the layers alone: a
  parenthetical naming something the cited layer declares says which row is
  meant, while a Lean source names its own declarations in its own spelling,
  and `definitionOfGround` cannot be matched against a census that spells it
  `definition-of-ground` without inventing a transliteration.
- **`P_n` was one of three parameters kept by hand, and the only one checked.**
  The count of atomic entities a layer introduces is now held to being one
  number across every restatement rather than several, and to the list beside
  it wherever one is given; the count of graduation conditions is held to the
  conditions the layer's own graduation block states by name. L3 graduates to
  terminal with no conditions and never states that count, so nothing is held
  about it.
- **One citation is recorded and left alone.** `definitionOfGround` is cited as
  L0 step 24 in four places; the census puts `definition-of-ground` at step 41,
  and step 24 is the graduation status, which carries no FRAME. It is certainly
  not step 24 as the census numbers it, and nothing written down says which row
  it is. A reference that visibly points at the wrong thing is better than one
  that invisibly does, so it stands, and a control confirms that removing it
  changes no verdict.
- **A census row runs until the next row, and letting it run further hid the
  defect.** With the boundary removed, a row's text bled into its neighbours,
  every name the reader was looking for turned up somewhere nearby, and the
  ledger read clean --- the control ran that mutation against the exact defect
  the guard exists to catch and watched it pass.
- **A layer's inventory of what it leaves undone claims to be all of them, and
  one is not in it.** L1's closing block ends "No entity unaccounted. No FRAME
  hidden." Its census opens four residuals, at steps 10, 21, 22 and 25, and the
  inventory names three. Step 22 is `opaque(D)`, FORM for the schema and a
  residual at L3 for the content --- the shape L2 uses at step 6 for `compose`
  and step 7 for `congruent-path`, both of which its inventory lists and one of
  which L3 discharges by name. Step 22 stands in no inventory and in no
  discharge register at either end. Exhaustiveness is the hardest claim to keep
  by hand, because nothing goes wrong when an item is left out: every sentence
  in the inventory stays true and the list is simply not all of them.
- **That one is recorded and not repaired, because the repair is not
  determined.** Four places say `D` belongs to L1 --- the declaration gives its
  reading in full and marks it orbital to L1, L1's inventory says so in the
  header and again in the closing block, and L3 says the matrix is defined at
  L1 while neither discharging the residual nor listing it as remaining ---
  against one census row that defers the content. Listing it asserts a residual
  four places deny; clearing the row asserts a closure nothing states. The gap
  is written into the guard rather than into prose, and a control confirms that
  repairing it from either end leaves the guard green while a second gap does
  not.
- **Inside its own file a layer cites its rows without the prefix, and nothing
  read those.** Thirty-six bare references stand in the layer files, invisible
  to a reader looking for `L1 step 10` where the file, already talking about
  itself, writes `step 10`. All are in range; being in range is what a
  renumbering breaks first. The inventory is also held to naming only rows that
  open a residual, which is the half that breaks visibly.
- **Completeness is asked only where it can be asked.** L1 is the one layer
  whose inventory cites rows by number. L0 documents eight residuals as two
  descriptions and L2 seven as five, and matching a description to a row is a
  reading rather than a measurement. Surveyed by hand and recorded rather than
  guarded: L2's inventory omits `path-trace` and the `compose` internals, and
  L3 accounts for the first among its non-blocking residuals and for the second
  only through the length law `composition-length-additive` asks for.
- **Three of the four readings were about where a phrase stops.** A reference
  belongs to another layer when a layer identifier stands close in front, and
  the window must allow words between, or L1 citing L0's self-kernel step 40
  reads as a claim about L1's own twenty-five rows. An inventory heading is the
  word with its colon immediately after, or L2's label over three census rows
  is read as an inventory of their own numbers. Payment is the verb and not the
  statement form: `discharge` is also a declared name, and matching it loses
  six of L0's eight residuals.
- **The fourth was a filter watching for a case that does not occur.** Three
  rows say they hold no residual and not one of them names a layer to close it,
  so requiring a named layer already excluded them and the denial filter never
  fired. It is now a check instead of a filter: a denial and a target must
  never meet on one line, because the day they do, requiring a target starts
  reading a denial as a promise.
- **A layer obeys a prohibition that its own list of prohibitions does not
  contain.** L2 forbids L3 three things and L3's copy of them runs (a), (b),
  and stops; the missing clause is separate classification machinery, and L3
  keeps it --- "the self-kernel pattern (L0-L3) IS the classification
  machinery" at two places and CLOSED in its own census at a third. The
  constraint is alive in the body of the layer and absent from the layer's list
  of constraints, so a reader asking what L3 may not do was told two of three
  and nothing they were told was false. Repaired, in the granting layer's own
  words.
- **A prohibition was addressed to the layer after the one it bound.** Inside
  L2's copy of the grant that binds L2, clause (a) read "L3 may NOT assert: a +
  b == b + a" where L1 wrote "L2 may NOT assert commutativity for '+'". The
  sentence is true and L2 states it properly two blocks down, in the block that
  binds L3; but addressed to the wrong layer it binds nothing at the layer it
  was written for, and the clause's own next words, "Commutativity is
  prohibited at L2", disagreed with its subject inside one line. Repaired.
- **The chain of grants has a link that begins in the middle, and this one is
  recorded rather than repaired.** L1 permits L2 four things and L2's copy
  keeps two: the quant family and free use of filtration are dropped, `compose`
  and finite structural operations put in their place. L2 uses both grants it
  dropped --- `quantification` and `quanta` run through its congruent-path
  close, and it cites the filtration chain by name --- while `compose`, which
  the copy reports as granted, appears in neither layer beneath it, and L2's
  own grant to L3 leans on it. Making the copy a copy deletes the only sentence
  saying `compose` is permitted; leaving it leaves the header's claim false.
  Whether L1's grant should reach `DerivationPath` is a question about the
  theory, so the gap is written into the guard and a control confirms the
  repair from the copy's end leaves every guard green.
- **A copy that says it is a copy is a claim, and it is the only thing that
  makes the block worth reading.** Six grants stand in the four layer files and
  four copies are kept of them, under headers reading "Copied from L<n>
  graduation block for traceability". Nothing inside such a block ever reads as
  wrong, because every sentence in it was true somewhere --- the question is
  only whether it is the sentence granted, addressed to the layer bound. L0's
  grant to L1 is the one nobody copied at all, and that is recorded too: the
  convention starts at L2, and L1's Section I holds axioms instead.
- **Letters agree while the text underneath is substituted, so the letters are
  not enough.** A clause and its copy must share one distinctive token, and the
  reader is held able to tell clauses apart before that means anything: of the
  fifty pairs made by setting a clause against the other letters of its own
  copy, thirty-three share nothing. Words are compared exactly and never
  stemmed, because `operation` and `operations` are the only two tokens
  standing between L1's clause (d) and L2's, and a control confirms that a
  reader which stemmed would close that divergence without noticing.
- **What binds is the deontic verb, not the mention.** A clause may name
  another layer perfectly correctly --- "those belong to L3", "prohibition
  carries forward from L2" --- and a reader taking any mention for a binding
  reports four defects that are not there, which a control shows by making it
  do so. Twelve prohibitions with a named subject stand in the four files;
  eleven always bound the layer whose block they stood in.
- **The two block terminators are redundant, and the control says so rather
  than implying otherwise.** A blank line ends one of these blocks and so does
  the next block's header, and every block here is followed by both. Dropping
  either alone changes nothing; dropping both lets the permits copy run on into
  the prohibits copy and reads every clause against the wrong one. That was the
  first reading of this increment, and it reported defects where there were
  none, which is the direction to fail in.
- **A pointer that resolves and lands on the wrong thing.** Three sentences in
  `L0_ground.hm` said the seven executive opaque predicates find their semantic
  close in Section IX. Section IX exists --- which is the whole reason nothing
  caught it: all fifty-five section references in the four layer files resolve,
  and a reader checking that they resolve reports a clean file. Section IX is
  the L0 self-kernel, it holds no `close` statement at all, and its own third
  line reads "VALIDATOR (L1): semantic content of those closures is consistent.
  [deferred]". The sentence saying the semantics were pending there sat four
  lines above that banner. The seven closes are in `L1_relations.hm` Section
  IV, titled SEMANTIC CLOSES FOR EXECUTIVE OPAQUES, which holds exactly seven
  and says it discharges L0 self-kernel steps 25-31. Eleven statements in the
  same file already said L1, seven of them the census rows the three wrong
  sentences were about. All three are repaired.
- **A section named as the place something closes must contain a close.**
  Resolution is not the check; the section was there. Four such pointers stand
  in these files and all four now land. The direction of the sentence is what
  had to be read: "Section VIII closes 7 previously informal terms as opaque
  predicates" is prose about what a section accomplishes and Section VIII holds
  no close, so a reader taking the subject form for a pointer reports a defect
  that is not there --- and the trap cannot be set on whole lines, because the
  two forms share one, a false pointer and a true pointer inside a single
  parenthesis.
- **Six counts a header states about its own sections had never been read.**
  Four axioms in L0 Section III, five derives in Section IV, four necessity
  constraints in Section VII, seven opaques and seven axioms and three derives
  in Section VIII. All correct, and all eight header counts are now measured
  against the sections they describe --- the other two being the census
  lengths, which the census guard already held from the other end and which the
  control confirms it still fires on. That asymmetry is the finding: L2's
  section index once said twenty-nine against a census of thirty-nine, and it
  is only because that number had gone wrong that anything was ever pointed at
  it. The six that had not gone wrong were the six nothing was watching.
- **A count has no fixed word order and one list uses both.** "III axioms (4)"
  puts the noun first; "VII graduation criterion (4 NCs discharged)" puts the
  number first, four words later in the same sentence. A reader that knows one
  order finds six of the eight and reports nothing missing, because the two it
  cannot see it also cannot miss, so the control removes the second order and
  confirms the guard goes red on its own floor rather than passing with a hole.
  In the other direction the lookbehind is what keeps the digits inside the
  layer names L1 and L2 from being read as quantities.
- **The header's list of sections is now held against the banners, both ways
  and in both shapes.** L0 writes its sections inline in a run of prose, L2 and
  L3 write a block one section to a line, twenty-seven entries in all, and one
  of them is VIII.a --- which a reader for roman numerals alone cannot see,
  the ninth
  time in this series that a near-miss turned out to be a narrow reader rather
  than a defect. L1 lists nothing at all. That is the same boundary the
  grant-copy convention has and it falls on the same side, so the absence is
  recorded as a set and the control adds a list to L1 to confirm the record
  fails rather than absorbing it.
- **L0's executive layer is FORM in the header and OPEN in its own status
  note, and this one is recorded rather than repaired.** The note's parenthesis
  says why it might be both --- closes stated, semantics pending --- so the
  question is whether the executive layer is FORM on structural grounds while
  OPEN on semantic ones, and that is a question about the theory rather than
  about its bookkeeping.
- **Every layer declares a boundary about the whole of its own text and
  nothing read it.** All four headers say it --- "Layer boundary: no term from
  L1 or above appears anywhere in this file", and the same for L2 and L3, and
  "terminal layer" for the last. It is the stratification the whole design
  rests on, asserted four times, and no guard, no census check and no audit
  step had ever looked. It is kept: one hundred and thirty-four names are
  declared above some layer and not by it, and not one of them stands in a
  statement of a layer below.
- **The claim is refuted entirely by the machinery that enforces it.** Sixteen
  of those names appear in comments, and every one of the sixteen is in a
  comment that bounds the term rather than using it: L1 telling L2 it "may NOT
  introduce ordinal_limit", L2's graduation block granting L3 `ordinal_succ`
  by name, L0 warning that a derive in L1 requiring `ordinal_limit` is
  over-reaching, four FRAME deferrals and three locators. A prohibition has to
  name what it prohibits. So the claim drawn over the whole file is false, and
  the only things making it false are the sentences that keep it true where it
  matters. The three non-terminal claims are repaired to say what the files do
  --- no term from above in any statement --- and the part worth asserting,
  that those comments bound rather than use, is moved out of prose and into a
  guard that classifies all sixteen as forbidding, granting, deferring or
  locating.
- **A spelling shared between a declared primitive and two censuses' own
  vocabulary.** L2 declares `step` as a primitive; L0 and L1 write "step 25:"
  at the head of every row of their self-kernels, one hundred and seventy-one
  lines of it against sixteen real mentions. A reader taking the spelling for
  the primitive reports the two layers keeping this boundary best as the two
  breaking it most, so the collision is classified by name with its reason and
  a control shows the reader without it.
- **A comment run is usually the body of the statement above it.** The five
  clauses of L2's grant to L3 are comments; the word that makes them a grant is
  on the line above and is not a comment. A reader that stops at the run sees
  five clauses naming L3's terms for no reason it can find, and reports them.
  The run is read with the statement on each side of it for that reason.
- **The terminal layer's boundary is recorded, not counted as kept.**
  "Terminal layer. No layer above" cannot be violated, so holding it would be
  counting an empty set as a success. What is asked of L3 instead is that it
  name no floor, so that a layer above it could not appear without the record
  changing first.
- **This repository keeps two accounts of the repositories around it, and
  nothing had read either one.** Section 1.1 of `AGENTS.md` is hand-written and
  counts itself in words --- three tightly coupled adjacent formal systems and
  one reference standard --- over a numbered list. `docs/family/family-graph.json`
  is generated: five public nodes, sixteen citation edges, sealed by a sha256
  over its own body, consumed by `scripts/build_pages.py` and by no test. The
  register is now added up, the seal is now recomputed before anything is
  compared against it, and the two are held to each other.
- **They disagreed in both directions and nothing in either was false.** The
  register named the verifier standard, which the graph has no node for ---
  correctly, since its nodes are fields and that is a standard, which the entry
  now says. The graph had a node for `hyperlogic` with an edge running *into*
  this repository, and the register did not mention it at all; it is registered
  now, as a sibling cited without being depended on, which is what it is.
- **A generated census went stale the day after it was sealed.** The graph was
  built on 2026-09-20 with three outbound citation edges. On 2026-09-21
  `P0_STATUS.md` cited a fourth sibling by name, and no step anywhere --- not
  the audit, not the pages build, not a test --- would ever have noticed. The
  seal is over the body, so it cannot be repaired by hand; the missing edge is
  pinned with its reason instead, which makes a *second* omission a failure
  rather than another silence.
- **Three unrelated readers went red on one document, and only one was right.**
  The layer-name reader, the cited-path reader and the clause-count reader all
  reported `P0_STATUS.md` as defective. It was the first document this
  repository ever wrote about somewhere else, and every reader in the suite
  rested on an assumption none of them states: that a name or path a document
  cites belongs to this tree. True of every document that existed when they
  were written. The clause count was a plain error --- the note put the total
  at 38 where the sources have 39 --- and is repaired. The other two were
  correct sentences about elsewhere: `ax-no-return` is a gate the precursor's
  draft declares, and `P0_shadow_ground.hm` is a file `hyperlogic` carries.
- **A citation is excused by the sentence that says where it lives, not by a
  list.** The exemption is read out of the document, the way retired layer
  names already are, and the tree named has to be one of the repository's own
  two accounts --- or the precursor, which is anchored by the commit it forked
  from. That anchor is the one part of *elsewhere* this repository can check,
  and it checks out: `819f685`, dated as the note dates it.
- **Mention is not attribution, and the word boundary has to stop at the
  underscore.** Every sibling in the register is also a word this repository
  uses about itself, and one of them is a clause name, an axiom and a layer
  file besides. Attributing every paragraph that merely contains a sibling's
  name excused seven hundred and four names; requiring the tree to be named as
  carrying, shipping or declaring the thing cuts it to ten. And a boundary that
  stops at letters and digits reads `L3_ordinatics.hm`, this repository's own
  file, as a citation of the sibling whose name it contains --- four words from
  "declares", which alone excused nine local names from having to resolve.
- **A bullet list has no blank lines in it, so a paragraph is not a block.**
  The first version of the reader took blank-line separated runs as its unit,
  which makes an entire changelog list one paragraph. One bullet saying a
  sibling carries a file then attributed four hundred and thirty-six names out
  of hundreds of unrelated bullets, and among them quietly excused a path that
  is pinned elsewhere as deliberately absent: one guard disabling another with
  neither of them saying anything. A list item is its own paragraph.
- **A name is attributed to every tree its paragraph names, and that limit is
  recorded rather than hidden.** A sentence saying that one tree declares this
  and another carries that attributes both names to both trees, because the
  reader does not parse which clause a name belongs to. What is held is that
  the right tree is among them, never that it is the only one.
- **A check that reports a cause it never measured.** The control harness for an
  earlier increment ends by rerunning its module after putting every byte back,
  under the message "the tree did not restore". It said that, and the tree had
  restored perfectly: the module was red because of a document written hours
  earlier that the control never touches. The message named a filesystem
  failure the check cannot see, and sent a session after corrupted bytes that
  were never corrupt. It is the same shape as the rest of this series, in the
  machinery rather than the artifact: a reader narrower than the claim it makes.
- **Two readers wrong in opposite directions, so neither looked wrong.** The
  Lean sources are read one declaration at a time: a comment block, then a
  body. The walk upwards that finds where the block begins stopped at the first
  blank line, and a Lean docstring is paragraphed, so it stopped inside the
  docstring. The walk downwards that finds where the declaration ends ran to
  the line before the next declaration, so it took in that declaration's
  docstring and every section banner between them. Too narrow above, too wide
  below. Every declaration still came back with prose, and 795 of this tree's
  1985 regions overlapped the region after them. One half of the lower repair
  is disclosed rather than held: a section banner is only truly swallowed by
  the last declaration of a file, which has no neighbour below it to collide
  with, so the guard that holds the partition cannot see that case. The
  admission it happens to affect passes on its pointer either way.
- **An admission passed on a word written about a different theorem.**
  `definitionOfGround` says nothing about independence. It says it is admitted
  at its own layer only, because the proof needs two closes declared one layer
  later, and that it is proved at `definitionOfGround_L1`. That is the second
  thing an admission is allowed to say, not the first. It satisfied the word
  test on "independent" read out of the section census below it, which is a
  paragraph about `derivesIsDirectional`. The census is right, the admission is
  right, and the reader joined them across a boundary it drew in the wrong
  place.
- **A disjunction whose second arm had never run.** An admitted declaration
  must state its status in words or name a declaration that closes it and is
  not itself admitted. Every admission in the tree carried one of the words, so
  the pointer half never executed once, and the clause inside it refusing a
  witness that is itself admitted never executed either. Six statements of the
  guard were unreachable for as long as it existed. Asked directly now, all
  eight admissions name a witness --- which is stronger than the disjunction
  and is what is true --- and the pointer arm carries a real admission for the
  first time.
- **The pointers were there the whole time and outside the readable region.**
  `derivesIsDirectional` closes with a sentence of verdict and names the two
  models that settle it in the paragraph above; read as it was, it cited
  nothing at all. Repairing the regions gives it back its two models and takes
  `congruentPathInternals` from six resolving names to twelve.
- **The module that reads the sources counts its own invariants, and nothing
  read that count.** Its docstring opened on "Four" and this increment took it
  to seven. The word and the list beneath it are now read against each other
  wherever a guard module opens that way, and because the reader finds one such
  list today it asserts that it found one at all --- a count guard passing
  because it read nothing is the failure it exists to prevent.
- **A sentence that has twice been a correct count of a smaller audit, with the
  record of its repair the only thing checking it.** `lean4/README.md` said the
  audit had "seven required processes" when it ran seven, and went on saying it
  when it ran twelve. The repair rewrote it to "fourteen checks" over the twelve
  processes it then ran and the two checks it derives, and left nothing reading
  the file --- so the same body of work that took the audit to fourteen
  processes and sixteen checks put the sentence wrong again before it was ever
  committed. Fourteen names, the word "fourteen", every name a real check: the
  count was right about its list and wrong about its subject, and every count
  guard here passed over it, because they hold a number against the list beside
  it and the list was the error. The sentence now names the fourteen it runs,
  the two it derives, and why a report can say its execution completed while a
  check in it fails.
- **Every document's list of the audit's checks is now read against the audit,
  not one sentence in one file.** The guard written for the first drift compares
  `docs/verification.md` to the command table; that was the other file carrying
  the sentence, not the one the entry was about.
- **The audit runs twelve processes that bind a dependency group and the note
  said ten, in the present tense.** It also said the evidence table carries ten
  sizes where it has twelve rows. Both counts are measured now, and a number
  standing in front of the word is held to one of the two things this repository
  calls a process.
- **Two checks are in every report the audit produces and in no sentence of the
  document that says what a completed execution requires.** `assumption_policy`
  and `proof_admissibility` decide the gate between them and were named only in
  the Lean README. The note now names them and says why a completed execution is
  consistent with a failing check in the same report. Every check the report
  carries has to be written down somewhere, which is the group-size rule asked of
  the checks themselves; `CHANGELOG.md` is not read for it, because an entry
  keeps the names its release had and cannot stop being true.
- **The audit keeps two orderings of its checks in one file and compares
  neither.** It runs the command table in order and seeds the report from a
  separate tuple; when a probe returns evidence the audit rejects, the handler
  charges the error to the last attempted check in the report, which is the
  seed's order. They agree today, and a name moved in one and not the other
  would mark a check that ran and passed as the failure, with its exit code,
  output and reasons all still saying it succeeded. Ten of the thirteen
  adjacent exchanges are already caught, by nine tests that raise from inside a
  probe and name the check they expect to fail; the last two entries are among
  the three that are not.
- **A citation in the Lean sources was read only where a keyword invited it.**
  Every name and count check in this repository reads `docs/**/*.md` and
  `README.md`, and `lean4/` carries 3,586 lines of comment prose, 857 of them
  in doc comments that are rendered as the API documentation and are the first
  thing a reader of the sources meets. Five guards do reach into that prose,
  each through a narrow trigger --- a line carrying the word "discharge", 52 of
  the 3,586; a name qualified by a namespace root; the prose inside an
  admission's docstring --- and between them they reach 55 of the 309 names
  those comments cite. The other 254 were read by nothing, and a count of what
  is covered cannot see what is not. Two citations had gone stale in that
  remainder: `conditions_iff_conditions`
  appeared once in the repository and named nothing --- the theorem is
  `prefixAxioms_iff_conditions` --- and a docstring reporting that two layers
  admit the same statement cited `L0Ground.derivesIsDirectional`, which names
  the `L1Relations` theorem and so named one of the two twice. Both are
  repaired and the source digests refreshed under the review the policy
  requires. The classification the documents needed turns out to be the one
  this prose needs, with no entry added: of the 309 names cited in the sources,
  eight do not resolve and all eight were already written down.
- **A citation qualified by a file was never checked against that file.** A
  dotted name resolves by its last component, which is right --- Lean writes a
  name at whatever depth the namespace makes unambiguous --- but it leaves the
  qualifier unread, so a citation can land on the wrong file with every part of
  it resolving. That is how the directionality pointer survived. Where the
  qualifier is a file of this project it is now read, over both surfaces; 28
  names are written that way. A qualifier that is a namespace is not read,
  because a namespace spans files: `Hypermath` is both the top namespace and
  the stem of the file that imports the layers, so thirty-nine of the forty
  files are read as qualifiers and that one is not.
- **`BACKTICKED` was defined twice in one file, and the collision was what kept
  a guard strict.** A narrow reader at the top of `tests/test_declared_counts.py`
  and a wide one 1,847 lines below; Python keeps the last, so both ran on the
  wide one --- including the guard written directly beneath the narrow
  definition, whose docstring described a reader its own module contradicted.
  Nothing failed and nothing could have, because the surviving reader was the
  stricter of the two. The ordinary repair for that guard, widening its reader,
  is the move that would have opened the hole. No name in `tests/` or
  `src/hypermath_foundations/` is now bound at module level twice.
- **"The cheapest checkable claim in the repository" was being checked four
  times.** `test_a_count_that_introduces_a_list_is_the_length_of_the_list`
  matches 64 spans across 105 files; 52 hold fewer than two items, four hold
  something that is not a bare name, three carry a second number in the clause
  and one is inside a quotation. Four claims are compared, and the guard
  asserts only that nothing disagrees --- so a reader that matched nothing at
  all would have satisfied it in silence. The reach is now pinned per file
  type, one each for `.hm` and `.lean` and two for `.md`, so emptying one
  surface fails while the others still compare.
- **A count introducing a list set out down the page was read by nothing.**
  `docs/research/CONSTRUCTIVE_QUINE_SELF_CLOSURE.md` announced two rigorous
  boundary results over a numbered list of four, and referred to the fourth by
  number further down the same section --- the list had grown twice, the prose
  around it had followed, and the number introducing it had not. Corrected, and
  `test_a_count_that_introduces_a_set_out_list_is_its_length` now reads that
  shape; three such lists exist, all in the notes. What makes it safe is that
  the list is set out beneath: inline, a colon does not bind its noun to what
  follows, and `README.md` correctly says "across two models" before naming
  five declarations. Measured before the guard was written, an inline reader
  found exactly one disagreement in the repository and it was that correct
  sentence. The colon is also required to end the line, which was first written
  down as the safeguard and is not one --- dropping that anchor leaves the
  guard green, so it is a narrowing nothing here can distinguish.
- **A rule the notes enforce about themselves was never carried to the sources
  that make the same claim.** Clause counts in prose are checked in markdown
  only. `lean4/Hypermath/L1Relations.lean` and `lean4/Hypermath/L3Ordinatics.lean`
  each put `FullAxiomModel` at a total of thirty-eight where the sources have
  thirty-nine, which is the exact drift this module was opened against. Both
  corrected, and `test_a_total_clause_claim_is_the_measured_total_wherever_it_is_written`
  now reads the total wherever it is written --- fifty-seven claims, twenty-one
  in the Lean comments, thirty-five in the notes, one in the layer language.
  The count may be spelled: the notes write all thirty-nine clauses in words,
  and a digits-only reader would have left that one unread. Words are safe to
  admit because the table of number words stops at twenty while both permitted
  totals are larger, so a numeral the table can express is a subset by
  construction --- asserted rather than assumed.
- **And the obvious fix was measured and rejected.** Widening the existing
  markdown reader to the sources reports four spans and not one is a defect:
  two are legitimate subset counts written in digits, which the markdown
  happens never to do, and two are numbers its forty-five character window
  reaches across to a noun they were never attached to --- a line number, and
  the size of a reduction. The permitted set reads as a fact about the project
  and is a fact about one file type. A rule can be enforceable on the files it
  was written for and unenforceable on the files carrying the same claim, and
  nothing about the green guard says which it is.
- **The layer language computes with a symbol nothing declares, and only a
  comment knew.** Every introducing form in the layer language introduces a
  word, so an operator written infix has no line that could declare it --- and
  the two that exist have none. `L3_ordinatics.hm` says so in its closing
  notes, in prose no test read. One of them is applied on five lines that are
  not comments, among them step 3 of the file's only close of a lower layer's
  residual, which asserts there that the operator is now available from
  Section IV; Section IV declares two opaques and three derives and neither
  operator. The other is announced twice and applied nowhere.
  `test_every_operator_the_layers_use_is_declared_or_disclosed` now holds the
  disclosure from both sides: declaring one makes the table stale, and so does
  the last use of one going away. Declaring the first is a decision about the
  language rather than a repair, so it stays open and is now open in a form
  that cannot rot.
- **The roster could not state a total of one hundred.** Its own line was read
  by a pattern allowing one hyphenated word and a reader that split on hyphens,
  so it could say ninety-nine and nothing above it. It stood at ninety-eight,
  and the document whose whole subject is hand-kept numbers going wrong was two
  increments from a `KeyError` on the word "hundred".
- **The zero row was proved over the prefix and read over every clause there
  is.** `the_unmentioned_are_unconstrained` is a theorem about `PrefixAxioms`:
  24 clauses. The sentence taken off it, in the guard that scans for the three
  names, is that every model may read them however it likes and all 39 clauses
  still hold. Nothing was false; the theorem was about a smaller set than the
  sentence, and the two sets have the same name. What stood at the larger one
  was a word scan --- the evidence this file rejects three theorems earlier,
  where it records that a model may interpret an unused symbol's clause
  vacuously and transfer it anyway, and the re-check it asks for two theorems
  later, where it records that a freedom proved against 24 clauses has to be
  proved again against the rest. `FullAxiomsCarrying` is that re-check: all 39
  copied verbatim around the three, `carried_symbols_are_free_at_thirty_nine`
  transferring an instance between any two readings of them, and
  `the_unmentioned_are_unconstrained_at_thirty_nine` the pair. Axiom-free, and
  each proof is the same two tactics it is at 24.
- **Writing clauses into one scope is a step that can lose one.**
  `closeDischargeOpaque` binds `e` as a `Form`; `ComposeAxioms` calls its
  identity path `e`; in the assembly the second shadows the first inside that
  one field. Legal, meaning-preserving, and completely silent --- so the
  declaration cannot be what says it was harmless.
  `carrying_iff_the_whole_clause_set` says it, by taking the structure back
  apart into the four it was built from, where the two `e`s are in different
  scopes and every field has to be discharged by `assumption` in both
  directions. Measured against the substitution it exists to refuse: bundle the
  four as fields and this proof fails on two prefix fields, while the freedom
  theorem closes by the same two tactics as before and is then a theorem about
  nothing. Two lines of rewrite here make the bundled file compile with no
  errors and all three theorems axiom-free, which is why the guard reads the
  fields rather than trusting the build.
- **`axComposeNonempty`'s inert binders are inert in the statement only.** Its
  two `Form` arguments, which the file already recorded as unused, are the sole
  mention of `Form` anywhere in `ComposeAxioms` --- and `Form` is a section
  variable, so mentioning it once makes it an implicit parameter that no
  explicit argument determines. Every use of the structure has to pin it by
  name. `ComposeConditions`, which drops the binders, has no such parameter.
  The binders were recorded as costing nothing; this is what they cost.
- Reviewed-source pin moved with the Lean file. `COUNTERMODEL_SOURCE_SHA256`
  now names the source carrying the above, which is the whole point of pinning
  it: the audit's `assumption_policy` fails until a change to that file has
  been read rather than regenerated.
- **A digest that fires on every edit reports nothing about any edit.** Adding
  a theorem to one of the thirteen swept Lean files takes four edits that have
  to agree: the `#print axioms` line, the name in the probe's pinned tuple, the
  count it adds to in the cost table, and the total in the verification table.
  Python held the second against the third and the fourth. The audit held the
  first against the second. Nothing held the first from here --- and what looked
  like it did was `COUNTERMODEL_SOURCE_SHA256`, which goes red for any change to
  the file whatever, so refreshing it is what reading the file means and a
  refreshed digest is evidence about the reader, not the edit. Measured the hard
  way: three theorems went into `Countermodels.lean` with three sweep lines and
  nothing on the Python side at all --- no records, no bump to the cost count,
  no change to the verification row. Those last three are checked against each
  other, so leaving all three out keeps them in agreement, at a number the Lean
  file no longer had; leaving out only one of them goes red in a second, caught
  by the other two. The digest was refreshed because the file had been read, the
  suite was green at 567 passed, and the audit stopped at `countermodel` with
  twelve probes left UNKNOWN.
- **Three facts holding each other up are not held to what they describe.** The
  tuple, the cost count and the verification total are pinned against one
  another, and that mutual check is real: it catches any edit that moves one of
  them. What it cannot catch is all three staying still. Agreement among
  readers of one number is evidence that they read the same number, and not
  that the number is the file's.
- **`tests/test_axiom_sweep.py` added.** It pairs the probes, the pinned tuples
  and the swept files, and then pairs every sweep line with a pinned name and
  back --- 1690 lines across thirteen files, exactly. It is a necessary
  condition for the audit's comparison rather than the comparison itself: the
  audit pairs names Lean resolved, and this pairs the names the file asks for,
  by fewest leading segments. Agreement here cannot promise the audit agrees.
  Disagreement here promises it will not.
- Sweep lines resolve outwards, and Lean resolves inwards. Three namespaces in
  `Countermodels.lean` declare a `prefixAxioms_hold`, so the bare sweep line
  matches four pinned names and the three written with their namespace match one
  each. Taking the fewest leading segments settles it and is a perfect matching
  in all thirteen files; where it would not be, the guard says so rather than
  choosing, because a sweep line whose record cannot be read off the file is a
  fact about the file and not about the reader.
- **The roster's own checker had every number and kept a floor under each.** The
  document that holds every other count in this repository to a computation says
  one hundred and eleven guards hold the measurement, which is true of its own
  list and says nothing about the suite. The check behind it walks `tests/` to
  build the set it validates names against and then asserts that set has more
  than a hundred members --- it had two hundred and forty-one. It collects the
  entry headings and asserts there are at least ten; there were thirty-nine. It
  sums what the headings claim and asserts the sum does not exceed the total,
  permitting any difference at all; the difference is twenty-four, and those
  twenty-four are guards named in the prose between entries, under no entry.
- **`test_the_roster_states_its_own_shape` added**, and a paragraph under the
  total for it to hold: how many guards the suite defines, how many this roster
  names, how many entries carry them, how many names stand under no entry, and
  how the unnamed hundred and thirty divide between the twelve files the roster
  draws from and the seven it has never cited. Ninety-six of those hundred and
  thirty are in files of audit and meta-layer unit tests; thirty-four are in the
  two files the roster draws most of its entries from. Which of them belong here
  is not settled by this and is now countable, which it was not before.
- A floor is not a measurement. `> 100`, `>= 10` and `counted <= claimed` are
  each true of the quantity under them and each survives that quantity moving to
  almost anything, which is the shape this repository has been finding in prose
  all along, found this time in the assertions of the guard that keeps the list.
- **A measurement written seven times in one file, with a floor under every
  copy.** `tests/test_layer_boundary.py` stated the count of terms-from-above
  named in comments three times in its module docstring, twice in `#:` comments
  beside its tables, and once in each of two guards. Every one of the seven
  said sixteen; the value had been seventeen since the mention nothing had read
  was found, and `assert len(comments) >= 16` stood in two of those guards. One
  copy was worse than stale: "one hundred and thirty-six names are declared by
  some layer above some other layer, and not one of them stands in a statement
  of a layer below" is false of one hundred and thirty-six --- that is the
  population without the ambiguity table, where the reader finds a hundred and
  fifty-two statements --- and true of the hundred and thirty-four the guard
  beside it measures. A number and a claim in one sentence, each right about a
  different corpus.
- **The instrument for holding a docstring's numbers could reach only the file
  that defined it.** `_states` was built last increment and lived in
  `tests/test_declared_counts.py` with all five of its callers. A pass that
  rewrites every `assert <expression> <comparison> <integer>` under `tests/`
  into a recording call, and a second pass asking which of those bounds the
  guard's own docstring also spells, found eight such floors; two disagreed
  with the value outright and reading the rest found two more stale numbers in
  the same docstrings. `test_the_skip_rubric_is_stated_the_same_way_twice` said
  "five of the eight glosses" where there are nine categories and six differing
  glosses, with the guard directly below it recording the ninth in its own
  docstring; `test_a_header_count_of_a_section_is_the_count_that_section_has`
  opened "Nine numbers" and listed eight, in the one docstring whose subject is
  a header disagreeing with its file. `_states` moved to
  `tests/_docstring_counts.py`, which is not a test module and so can be
  imported by any of them --- it could not have been imported where it stood,
  because `tests/test_declared_counts.py` imports from
  `tests/test_stated_process_rules.py` and the cycle would have closed.
  Twenty-one numbers across four files are now held, five floors went away
  because an exact count leaves a floor nothing to say, and the ambiguity table
  became a parameter of the reader so its control is run rather than described.
- **Two bounds stood between moving quantities, and one of them was dead.**
  `max(kinds.values()) < len(comments)` said no bounding category covers every
  mention, where "the categories distinguish" is the claim; it passed with nine
  mentions to spare and would have gone on passing if two categories had come
  to take exactly the same mentions. It is replaced by the statement that no
  two take the same mentions and none takes a subset of another, which implies
  it. `len(opened[index]) > len(cited) - 1` could not fail at all: the guard
  above it already holds every cited row to be one that opens a residual, so
  the inventory is a subset and the cardinality follows. In its place is the
  one failure an exemption list has of its own --- `UNLISTED` is subtracted
  from what the guard finds, so an entry whose gap has been closed would
  subtract from nothing and leave the record stale and the guard green.
- **Splitting a conjunction claims a count, and two of the splits never paid
  it.** `compose_is_four_split_conditions` and
  `sharp_transfinite_is_four_split_conditions` each say four in normal form
  rather than three, which is a claim that the two halves are two conditions
  and not one --- and `WitnessConjunctionDoesNotSplit` is the same file's proof
  that a conjunction can fail to be two. Two of the four splits in
  `Countermodels.lean` already carried separating models; these two carried the
  biconditional and nothing else, because the model that drops the whole
  conjunction says nothing about which half did the work. Both now have a pair:
  `keepLeft` against `keepRight` for composition, total congruence with
  simulation at one pair against both relations empty for the transfinite
  layer, each holding fixed the conditions its split does not touch. All four
  new declarations report no axiom dependency at all; three of them reached for
  `propext` through `simp` in draft and were rewritten as terms.
- **Eleven lists of conditions, and the rule for counting them was applied to
  two.** `test_each_corner_condition_has_a_model_that_drops_it` states this
  project's rule --- a field count is a measurement only once every field has a
  model that drops it --- and reads the two structures named in
  `CORNER_STRUCTURES`. `Countermodels.lean` names eleven, carrying fifty-five
  fields. Across all eleven, forty-five fields have a drop model and ten do
  not, and the ten sort into two kinds with nothing left over: eight are halves
  of a split, where a drop model cannot exist at all because both halves hold
  in every model of their layer, and two are theorems of other layers and not
  conditions at all. The nine structures outside the rule were not failing it;
  they were outside it, which is the same shape as the unread counts above.
- **`_known_names` narrowed twice.** The line widened last increment said
  "every name a module here defines at the top level" and read `def`, which is
  every function and no table. A note citing `CORNER_STRUCTURES` found it, the
  same way a note citing `_states` found the first one. Top-level assignments
  and classes now count, and the forty-seven names already classified as
  unresolvable are unchanged --- the widening added reach, not exceptions.
- **Nine counts inside the checking apparatus, and every one was wrong.** Four
  guards in `tests/test_declared_counts.py` open by stating the size of the
  corpus they hold. Nothing read those numbers. Measured on 2026-09-21: 204
  cited paths were 208, 198 resolving were 203, six unresolved were five, 847
  cited identifiers were 928, 51 unresolved were 47, 309 names in the Lean
  comments were 314, 3,586 lines of comment prose were 3,624, 52 of them
  carrying the word were 54, and 89 discharge claims across 22 files were 105
  across 20. Two of the nine contradicted a table twenty lines below them in
  the same function that *is* compared exactly, element by element, on every
  run. `_states` reads the sentence back out of the docstring and holds its
  numbers to what the body just measured, so the repair for the next drift is
  to retype a sentence rather than to notice one.
- **One of those drifts ran backwards under its floor.** The documents claiming
  a discharge fell from twenty-two files to twenty while the claims inside them
  rose from eighty-nine to a hundred and five. A floor can report neither
  direction, and the guard floored all three numbers --- at forty, at each
  other, and at fifteen. A count that only grows is at least legible from
  outside; a count that moves both ways under a floor is not legible at all.
- **A reader was named for the claim and measured the letters.**
  `_documents_that_claim_a_discharge` said it returned every line claiming
  something is discharged and returned every line carrying the word, and a
  good fraction of those are prose about the counting. Wide is right for it ---
  its only consumer asks whether the names on each line exist, where a line
  naming none costs nothing and a line missed is a hole --- so the word was
  corrected and the reader left alone, and the sentence it feeds now says what
  is counted.
- **`_known_names` said "the guard names" and read only the guards.** It
  matched `^def (test_...)` in `tests/`, so the 114 helpers those modules
  define were names this project could not confirm existed. It went unnoticed
  until a note cited `_states` and the citation would not resolve; every
  top-level definition now counts, which is what the sentence above it always
  claimed.
- **A floor is not a measurement, and three of them said they were.** Every
  comparison in `tests/` against a whole number was instrumented at once and the
  suite run with the instruments in place: fifty-four exist, the run reached all
  fifty-four, and the gap between bound and value runs from nothing up to three
  times the bound. Thirteen sit exactly on their value, which notices a fall and
  says nothing about a rise. Three carry a comment saying they catch a reader
  losing reach, which is the one thing a floor cannot do, and the notes now
  carry the table of what each of the three actually allows.
- **The credited-name reader would not let anything stand between a name and
  its verb.** English does. Seven names in `docs/research/` are credited across
  an adverb, across the noun the name is used as an adjective for, or across a
  parenthesized citation, and all seven stood outside
  `test_every_name_the_notes_credit_with_a_result_exists` --- whose entire
  subject is that a credited name exists. None of the seven is missing, so
  nothing in the notes was wrong; what was wrong was the comment naming
  `checked >= 140` as the thing that would have reported it, with `checked` at
  214. The reader now admits the three shapes, admits only the words these
  notes write, and asserts each shape is reached, so a branch that carries
  nothing is visible rather than kept.
- **"Both arms have to run" is one assertion, and one of the two arms was
  holding fifty-four comparisons hostage to it.** `subsets` was held by its own
  truth, which is what the claim means; `compared` was held to forty-five with
  fifty-five in hand. It now matches its sibling, and the two reach floors above
  it are what hold that reader to the corpus.
- **Nothing in the theory is used only across the seam.** All eighteen names
  the bridge files reach are also consumed inside the theory's own five files,
  so the declared names partition into five idle, thirty-eight consumed only
  within the theory, eighteen consumed on both sides, and an empty fourth
  class, pinned as `LAYER_SEAM_ONLY` and compared by the audit. Deleting the
  bridge would therefore change nothing the sweep reports: the idle set stays
  at five and all seven sole consumers are inside the theory.
- **Which axioms count as the foundation was written down twice.**
  `LAYER_FOUNDATION` restated `LEAN_BUILTINS` plus the admission marker, with
  neither referring to the other; it is now derived from it.
- **An unreviewed axiom in the layer sweep ended the audit instead of failing
  it.** That group is the only one that reads its records through a table
  rather than comparing against one, so a name absent from `LAYER_AXIOM_HOME`
  raised a `KeyError` past the audit's handlers and the run produced no report
  at all --- which adding a clause without adding its home does. The reduction
  now raises the same failure every other group produces, and a guard requires
  every group to reject rather than crash, reading the handled kinds out of the
  audit's own source.
- **Every count in the evidence table now computes.** The observation row and
  the finite-action row were already joined to their tables; the ground-syntax
  row's twenty-three reports and the composed-calculus row's twenty-six were
  joined to nothing. All rows now compute from the pinned tables the audit
  replays, and each group's split by foundation axiom is pinned too --- so a
  report gaining an axiom is visible even in the rows whose prose cites no
  split.
- **Two rows of the evidence table in `docs/verification.md` were joined to
  nothing.** The seven parameter-relative finite-trace proofs and the thirteen
  parameter-only plus four source-relative arithmetic results are all
  equivalence classes of `PROVED_DEPENDENCIES`, and both counts are correct ---
  but the phrases occurred once each, in that file, derived by no table, guard
  or note. The arithmetic row is one group under two conditions rather than two
  kinds of result: all seventeen rest on the signature parameters, and the four
  additionally name a Lean foundation axiom. Both rows now compute.
- **The theory's language is closed in its five files; its proofs are not.**
  Three of the five import only each other; `L1Relations` imports and uses
  `Hypermath.Trace`, and `L3Ordinatics` imports `Ordinatics` from another
  repository. But no field of the clause structure mentions `Trace`, and neither
  does the type of any of the sixty-one declared names --- so the clause list can
  be read and a countermodel for it built without `Hypermath.Trace` existing,
  which is the licence every countermodel in the note has been using unchecked.
- **The home of an idle declared name was checked by nothing.**
  `LAYER_AXIOM_HOME` is the table every number in the sweep is read through. Its
  names were anchored to the Lean source three ways over --- as source
  parameters, as fields of the model's clause structure, and for `ordinatics` by
  its own guard --- but its homes were anchored only by use, and an idle name is
  used nowhere. Moving `pathStep` from `L2Operations` to `L1Relations` in the
  table alone left the suite and the audit green; the same held for all five
  idle names. Now read back out of the source, for all sixty-one at once.
- **The seam between the theory and the rest of the development is a
  signature, not a theory.** `LAYER_BRIDGE_VOCABULARY` pins, name by name, what
  each of the five bridge files takes from the theory --- a question the
  layer-level support table cannot answer, since a row saying `GroundSyntax`
  reaches `L0Ground` is true of a file using only `Form`. Thirty-three of the
  thirty-eight bridging declarations consume symbols only; the five that reach a
  clause are `nativeModel` and `native_check_sound` in each ground file, plus
  `cycle_witness_length_preserved`. Every bridge file reaches `Form` and `f2f`.
- **No `L2Operations` clause is consumed outside the theory's own files.** Eight
  of the thirty-four clauses are reached from outside, all homed in `L0Ground`
  or `L1Relations`; twenty-six never are. So the whole of `L2Operations` can be
  restated without disturbing a proof anywhere else in the development. The
  reviewed shape the audit compares is now a six-tuple.
- **The theory is confined to five files, and that is now pinned.** Of the
  twenty-four files swept, fourteen never touch the declared vocabulary, five
  contain nothing else, and five are the seam between them. The silence of the
  fourteen was already held --- a file consuming nothing cannot appear in
  `LAYER_CONSUMPTION_SUPPORT` --- but the line between the other two groups was
  not, because a support row says a file consumes `L0Ground`, not that
  everything in it does. `LAYER_WHOLLY_CONSUMING` is the fifth element of the
  reviewed shape, and the guard requires every layer file to be in it.
- **Read by file, the silent five hundred and sixty-seven stop looking odd.**
  Some of that silence is required by the method: `TransportCountermodel.lean`
  builds carriers satisfying the clauses and declares its own `FullAxioms` to
  do it, so a countermodel consuming a clause would not be a countermodel. The
  rest is parametric machinery. The proportion suggested most of the
  development was unrelated to the theory; the partition says it is a theory of
  one hundred and seventy-seven declarations with thirty-eight more reaching it.

- **Irredundance does not pin a count; minimality does, and the hub is the
  unique minimum.** The closing claim above settles that both lists are
  irredundant and leaves open why one is shorter, because irredundance is a
  property of one list and two irredundant lists can differ in length. The
  arrows make it answerable: between the three diagonal predicates there are
  six, `filtrationSimCong` at `y := x` is one of them and free at every setting,
  and the remaining five are the vocabulary. `no_other_pair_of_arrows_is_the_hub`
  refutes every ordered pair of the five but the hub's own, and since a pair may
  repeat an arrow the diagonal cases also say no single arrow does it, so two is
  the minimum and the hub is the only two; `no_two_of_the_triangle_suffice` says
  the clause list is not. The fourteen refutations needed no new model: three
  `Drops*` settings cover thirteen of the pairs and
  `NeedsCongruentDiagonalIsReach` covers the last, which is the pair nearest the
  hub --- reach into equality with its own mirror --- because it is the one model
  holding the simulation diagonal at `Reach` while congruence descends nowhere.
  The claim is minimality in the arrow vocabulary, not a claim that no single
  cleverly worded statement is equivalent to the hub.

- **The `countermodel` audit group grows from one hundred and four to one hundred
  and forty dependency reports, and every one of them is now pinned to its
  exact axiom cost.** Ninety cost nothing, thirty-two cost `propext`,
  thirteen add `Quot.sound` and five add `Classical.choice`. This was the last
  probe group compared against a rule rather than a table --- it asked only that
  no axiom outside `propext`, `Quot.sound` and `Classical.choice` appear, which
  catches an admitted proof and nothing short of one --- so a report's cost could
  move and the audit would still pass
  once the source digest was refreshed alongside the edit, which is what
  refreshing a digest is for. A digest records that something changed; the table
  records what. Sixteen new structural tests hold the measurement, including one
  that checks a
  claim `operationAxioms_iff_conditions` has asserted in prose since it was
  written and which nothing had compared until now, one that checks each arrow of
  the cycle has a model filed under the right prefix, and one that checks the two
  halves of the vocabulary pair still state the same fact --- without which the
  pair demonstrates nothing and nothing else would notice.

- **Three tests check what Lean cannot.** A model asserting its own condition
  twice and one of the others not at all would typecheck and read as though it
  had done the work. `test_each_condition_has_a_model_named_for_it`,
  `test_every_model_names_its_whole_group_and_denies_one` and
  `test_the_sharp_list_keeps_six_conditions_word_for_word` measure the names,
  and the `countermodel` audit group grows from sixty-five to seventy-nine
  dependency reports.
- **The chain from declaration to characterisation was joined at every link by a
  count, and is now joined by names.** The layers declare 35 logical axioms of
  which `ordinatics` stands for five; four model structures each assert 39
  fields; four condition structures hold 24, 7, 3 and 5. Thirty-nine four times
  over is agreement by arithmetic.
  `test_the_models_list_the_clauses_the_layers_declare`,
  `test_every_clause_structure_names_the_same_clauses` and
  `test_the_five_clause_structures_partition_the_clause_set` check the names.
  All three pass as the tree stands.
- **Two defects in the clause reader, both of which returned a well-formed
  answer to a question it could not resolve.** Its structure pattern required
  `where` on the opening line, so a structure with wrapped binders was invisible
  and the reader returned an empty dict instead of failing --- `ComposeAxioms`
  and `TransfiniteAxioms` both wrap. It also resolved a repeated structure name
  by taking the last one across namespaces, and `Countermodels.lean` declares
  six called `PrefixAxioms`. The reader is now namespace-qualified, tolerates
  wrapped headers, and raises on both not-found and ambiguous.
- **The declared clause set is now characterised end to end: 39 of the 39
  clauses, nineteen conditions, no axioms.** `FreeFiltration.TransfiniteAxioms`
  states the transfinite projections with the carrier, the three relations, the
  path type and its projections and the three transfinite constants all open;
  `transfinite_clauses_are_five_conditions` reads them off, and
  `all_thirty_nine_iff_nineteen_conditions` joins all four lists. `deriver`
  occurs once, in an equation, so it is determined and disappears with its
  clause. `pathStart` and `pathEnd` occur once, existentially, so they are
  pinned at one point --- and pinning them *separates* `axLimitDerives`, whose
  shared path index was the only thing tying its two halves together. One clause
  leaves two conditions behind, and the two eliminations cancel.
- **The third join is obstructed although its symbols are disjoint, which the
  incidence table cannot predict.** `nineteen_is_not_fourteen_plus_five` gives
  all three parts: `LimitAdjoined` satisfies all nineteen conditions on the
  chain with one point adjoined; `BareChain` satisfies all fourteen on a carrier
  the chain exhausts; and `spanned_carriers_admit_no_limit` shows no transfinite
  layer sits on the latter for any choice of limit, successor, deriver or path
  projections. `the_limit_is_off_the_chain` is the one step that does it ---
  `axLimitNotFinite` denies simulation from every finite position,
  `simulationDiagonalIsReach` grants it at every reached point, and
  `chain_points_are_reached` reaches them all. The demand is on the carrier, and
  a table of which clauses name which symbols cannot see one.
- **`ground_is_not_an_image` added**, so the contrast is exact rather than
  asserted: the prefix conditions already constrain the carrier --- forming
  never returns to the ground --- but only by forbidding a coincidence inside
  the chain. `axLimitNotFinite` is the first clause that demands a Form the
  chain never reaches.
- **A measured total drifted in the note about measured totals, because its
  noun was a pronoun.** `docs/research/CLAUSE_INDEPENDENCE.md` read "the working
  tree has 66, and every site that reports it now says so" while the baseline
  held 68. The counts scan binds a number to the noun it counts; the referent
  here sat two paragraphs away behind "it", so the sentence named a total and
  matched no total pattern. Corrected, and the sentence now carries its noun.
- **`test_every_audit_group_size_is_reported` added: the scan now runs in both
  directions.** The existing checks fail when a sentence disagrees with a
  measurement, and never fired on a measurement no sentence names. Four of the
  ten report groups were in that state --- `layered_derivation` (186),
  `full_model` (92), `record_machine` (87) and `countermodel` (53) --- and the
  six that were reported are exactly the six that had not grown since the note
  that introduced them. `docs/verification.md` now carries all ten sizes as a
  table generated from `_reports.py`, and a new process fails the test until it
  is written down.
- **The last three clauses this repository declares on its own are now
  characterised, and the join is free.** `FreeFiltration.ComposeAxioms` states
  `axComposeAssoc`, `axComposeIdentity` and `axComposeNonempty` over an
  arbitrary path type with `compose`, `pathGround` and `congruentPath` all
  parameters; `composeAxioms_iff_conditions` reduces them to three conditions
  and `prefixOperationsCompose_iff_conditions` joins all three lists at **34 of
  the 39 clauses, fourteen conditions, no axioms**. Only the five transfinite
  projections of the one `ordinatics` instance remain outside, and those are
  declared in another repository.
- **`axComposeNonempty` has two binders that do nothing.** It is declared
  `Form → Form → ∃ p, ¬ congruentPath p pathGround`, and its statement cannot
  mention either Form it takes. `compose_nonempty_binders_are_inert` proves the
  arrows are removable given any one Form, so the clause says only that
  something is not the unit --- the row-of-zero reading applied inside a single
  clause instead of across the clause set.
- **Two joins, two answers, and the incidence table predicts both.**
  `lists_join_freely_exactly_on_disjoint_symbols` states them together:
  `operations_exclude_the_unreached_point` on one side, where a model of the
  eight prefix conditions admits no operation conditions at all, and on the
  other side the composition layer extending *any* model of the eleven, because
  no condition among the eleven mentions `compose`, `pathGround` or
  `congruentPath`. `compose_conditions_are_always_available` is the witness. The
  second proof is trivial and that triviality is the measurement: clause lists
  compose as freedoms exactly when the symbols they name are disjoint.
- **The zero row is now mechanized here too, and it took an arbitrary carrier to
  do it.** `FreeFiltration.PrefixAxiomsCarrying` is the 24 clauses with the
  three symbols no clause mentions carried alongside;
  `carried_symbols_are_free` transfers an instance between any two assignments
  of them, `carrying_iff_prefix` says carrying them changes nothing, and
  `the_unmentioned_are_unconstrained` pairs the two. All axiom-free, each proved
  by `cases` then `constructor <;> assumption`, and that pair of tactics is the
  measurement: injecting a parameter into one field makes all three fail with
  `tactic 'assumption' failed`.
- **A freedom theorem proved inside a model cannot witness a silence.** The
  first version of the above was written against `HypermathFullAxiomModel` and
  passed while checking nothing: that model reads `structContinues _ _ := True`,
  so a field mutated to `structContinues (pl pathGround) ground` unfolds to
  `True` and `assumption` closes it from the unmutated hypothesis --- a clause
  that does mention the parameter, transferred anyway. Over an arbitrary carrier
  nothing unfolds and the same proof becomes a real check. This is the guard
  hygiene rule one level up: a proof wide enough to succeed is wide enough to
  succeed for the wrong reason.
- **`ordinalApply` is unconstrained at both levels, so the three proposed action
  laws in §IV were never reachable.** `Hypermath.ordinalApplyUnconstrained`
  gives, for any function whatever, an instance of the transfinite interface
  over this substrate with this limit, this successor and that function for its
  application; its only assumptions are the substrate parameters and
  `Hypermath.ordinatics` itself. No law of the interface mentions `apply` and no
  clause of this repository mentions `ordinalApply`, which
  `tests/test_declared_counts.py` now pins with `ordinalLimit` and `ordinalSucc`
  as the control.
- `pathLengthArithmeticClaim` was refuted by a full-clause model, and the model
  was never needed: it names `pathLength`, which no clause mentions, and
  `ordinalApply`, which neither clause nor law mentions. The docstrings of all
  three §IV claims said something weaker than the truth --- "no declared
  computation clause", "not strongly enough to derive it" --- and now say that
  nothing relates the symbols at all, and that a bridge here means a declared
  clause rather than a sharper proof. The `ordinalApply` definition docstring
  labels its three intended readings as intentions rather than consequences.
- **The zero row is now checked by the kernel one repository down.**
  `Ordinatics.Transfinite` declares three data fields with five laws and no law
  mentions `apply`; `Ordinatics.Transfinite.withApply` rebuilds an instance
  around a new application and elaborates only because every proof field
  transports, while the same expression at `succ` fails and the error names
  `succExtends`. `apply_is_free` and `apply_is_a_free_factor` turn that into a
  splitting --- an instance is a constrained part with a free function carried
  alongside --- and depend on no axioms;
  `Ordinatics.TwoChainModel.only_apply_is_unconstrained` sorts the three fields
  at one substrate. Read together with `deriverAtLimit`, whose independence cost
  a model and a second naming, the pattern is that what a symbol costs to settle
  tracks how many clauses name it.
- `tests/test_declared_counts.py` recomputes the incidence table from the clause
  structure and pins the unconstrained and singly-mentioned rows, so a clause
  that starts constraining one of those symbols flags the independence arguments
  that rested on the silence. Read from a model rather than the layers, because
  the layers write `~~`, `=~` and `≡` and a scan by name would not see them.
- `tests/test_declared_counts.py` pins the duplication and pins `axSeqAsymm` as
  the only clause in the layer mentioning incongruence. It also surfaced a third
  duplicate group on the first run --- `pathStart`, `pathEnd`, `pathTrace` and
  `pathLength` share a type --- which is four accessors of one path type rather
  than redundancy, and is now pinned separately so that dropping or retyping one
  is visible.
- **The prose scan was excusing live claims.** Its exemption for sentences
  reporting what an earlier commit withdrew was applied to the whole paragraph,
  so every other number sharing that paragraph was skipped with it. Two
  milestone totals had been wrong since the §VI.a increment and were reported by
  nothing. The exemption is now per sentence, which found both. Same shape as
  the wrapped-field counter: a guard wide enough to be safe is wide enough to
  hide what it guards.
- The scan also gained a narrower binding rule. A number is bound to the first
  counted noun that follows it, so a number already spoken for by `clauses` is
  no longer read as an assumption count when the sentence goes on to mention
  assumptions. `NOT_A_CLAUSE_COUNT` had the mirror of this rule from the start;
  this is its missing half.
- That is the `=~` freedom theorem one clause set up. Taking the arbitrary `E`
  of `AsymmetricCongruent` everywhere true already makes `=~` total across the
  24 clauses; the transport model extends it to all 39. The clause set contains
  no distinctness assumption at `=~`, and operations and ordinals do not add
  one, so every "these two Forms differ" in the development has to be carried by
  `≡` or by a clause that does not exist.
- `tests/test_declared_counts.py` now pins the transport model's clause
  structure at 39 alongside the other three. It was the one full-clause
  structure nothing measured, and the new independence result reads its size as
  a claim about all 39.
- **The two upper reflexivities are one condition, and it is reachability.**
  `L1Relations` §IV.c proves from existing clauses that `x =~ x` and `x ≡ x`
  hold of exactly the same Forms, and that both hold exactly when x is `~~` to
  some iterate of ground; `globalCongruentReflexivityIsCofinality` states the
  global form. §IV.b had proved reflexivity at ground twice, once per level,
  remarking each time that it does not generalise without saying what it was
  equivalent to. It could not generalise: the two proofs were the same proof.
  Five theorems, no new assumption, every dependency a declared clause.
- **`=~` is free above equality.** `AsymmetricCongruent` is now parameterised by
  an arbitrary relation `E` and satisfies all 24 L0/L1 clauses for every choice
  of it, so no property of `=~` beyond containing equality follows from the
  clauses. The previous single asymmetric pair is one instance; transitivity is
  another. A freedom theorem settles the cells nobody has asked about yet, which
  refuting one property at a time does not.
- **`≡` is free above equality apart from `ax-diff`, and that is a
  characterisation.** `FreeSimulation` satisfies all 24 clauses for every `E`
  relating no image to ground. The side condition is forced in every model by
  `axDiffInRelationLanguage`, so sufficiency and necessity meet: the clauses
  constrain `≡` in exactly one way and no other.
- The relation grid is complete. Three filtration relations against reflexive,
  symmetric and transitive is nine cells, all nine independent of the clauses,
  and they reduce to one reachability fact and two freedom theorems. `~~` admits
  no freedom theorem *of that shape*, which is the finding: `traceLevels` forces
  `f2f x ~~ x`, `filtrationCongSim` forces `~~ ⊇ =~`, and reachability ties
  `=~`'s diagonal. Read as assumptions the filtration is upside down --- the
  content sits at the bottom level and the two above it are nearly
  undetermined.
- **All three relations free at once, and then it is an iff.** Each freedom
  theorem fixes two relations to answer about the third, so none of them says
  what the clauses assert about the filtration as a whole; `~~` gets none
  because it is what the others are held fixed against.
  `HypermathCountermodel.FreeFiltration.prefixAxioms_iff_conditions` leaves all
  three open and proves `PrefixAxioms S C E ↔ Conditions S C E` for arbitrary
  `S`, `C`, `E` over an arbitrary carrier --- eight conditions: two inclusions,
  three facts about forming at the bottom level, one denial at the top, and both
  upper diagonals pinned to ground-reachability. Necessity is
  `Hypermath.filtrationConditionsHold`, proved in `L1Relations` §VI.a from the
  declared clauses. Neither direction uses an axiom.
- **The carrier had to be free as well, and the first version of the
  characterisation was true but blind.** Over the ground chain every Form is an
  iterate of ground, so condition 3 alone makes `Reach` total
  (`reach_is_total_on_the_chain`) and the two diagonal conditions say nothing
  beyond reflexivity. The reachability content they lose is the whole
  reflexivity column --- `reflexivityIsGroundReachability`, `IrreflexiveSimilar`
  --- so a chain-only statement cannot express the result it is supposed to
  subsume. Opening the carrier costs nothing: the proof goes through unchanged
  and still uses no axiom.
- `FreeFiltration.ext_conditions` added, instantiating the eight at the chain
  with one adjoined Form whose image is itself, so the chain never produces it.
  `congruent_reflexivity_needs_an_unreached_point` reads off all 24 clauses with
  `~~` reflexive and `=~` not. `IrreflexiveSimilar` refuted `=~`-reflexivity
  with `~~` irreflexive too, which left the reading that a badly behaved bottom
  level was doing the work; one unreached Form is the entire requirement.
- The iff is available because seven of the 24 clauses are closes that read
  `HMSyntax`, `Substance`, `Semantics`, `FormClosure`, `Derives`, `Discharge`
  and `Definition` off the three relations. Defining those seven predicates as
  what the closes say makes all seven fields `Iff.rfl`, so every clause either
  survives as a condition or is a definition restated, and nothing is lost.
- The two upper freedom theorems are now corollaries.
  `total_similar_leaves_exactly_three_conditions` sets `~~` to the total
  relation and the eight collapse to three --- `≡ ⊆ =~`, both reflexive, `≡`
  denies every image at ground --- which is `AsymmetricCongruent` and
  `FreeSimulation` read off one statement. So are the nine grid cells.
- **`~~` may be a partial order.** `similar_can_be_a_partial_order` reads
  `x ~~ y` as `y ≤ x` with `=~` and `≡` both equality, satisfying every clause
  while `~~` is reflexive, transitive, antisymmetric and not total. Every
  previous `~~` witness was the total relation or the ad-hoc irreflexive one,
  which left open whether the freedom results were artefacts of a badly behaved
  bottom level. They are not: assuming the filtration well behaved buys nothing
  back.
- `IrreflexiveSimilar` also refutes transitivity of `~~` and reflexivity of both
  upper relations, with no change to the model. Those were readable off it from
  the start and had not been read.
- **`lake build` never compiled the countermodels.** The library target is
  `Hypermath`; the twelve top-level files in `lean4/` are compiled only by name.
  Four theorems added this cycle were `sorryAx` while the build stayed green,
  and the Python suite could not see it either because it stubs `lake`. CI was
  never affected --- it runs the real audit through `scripts/check_foundation.py`
  --- but the pull-request template told contributors the wrong pair of commands.
  Template and `lean4/README.md` now say which command establishes what.
- Production-milestone totals measured and corrected. The phrase names
  `PROVED_DECLARATIONS`: the three commits that introduced the three different
  totals each set that dictionary to the number they wrote (`6b050fc`/34,
  `b35b795`/38, `c5de9dc`/45). The test measures the baseline rather than
  pinning a literal, so adding the §IV.c theorems moved the total from 58 to 63
  and named all nine stale sentences by itself. This was the one count family
  the first pass left alone as unverified.
- `lean4/README.md` said the audit had "seven required processes". Those are the
  first seven of the fourteen it runs; it now lists all fourteen and names the
  one expected to fail.
- The prose scan reads paragraphs rather than lines, and matches a number to the
  noun it counts rather than to a fixed phrase. The notes are hard-wrapped, so a
  number and its noun routinely land on different lines. That found four further
  drift sites no line-at-a-time, phrase-led search could see: "67 assumptions",
  "67 reviewed parameter/axiom declarations", "11 remaining admission sites" and
  a wrapped "38 declared logical clauses".
- `docs/research/CLAUSE_INDEPENDENCE.md` added: the status of each admission,
  the witness for each, and the evidence behind every corrected count.
- `tests/test_discharge_pointers.py` added. It parses the Lean sources and
  fails if a comment claiming a discharge names an identifier that is not a
  declaration, if a repository-qualified name in prose does not resolve, or if
  an admission does not state whether it is independent, open, underivable, or
  closed elsewhere by a named theorem that is not itself admitted.

## 0.1.0 - 2026-09-17

Initial experimental release:

- Hypermath foundational audit and formal verification framework.
- Finite layer graph operations and serialized support replay.
- Axiom model, proof obligations, and self-derivation gating.
- Pure stdlib smoke testing and bounded release boundaries.
