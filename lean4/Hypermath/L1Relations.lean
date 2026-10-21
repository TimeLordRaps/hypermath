-- Hypermath.L1Relations
-- Layer 1: Relations
-- Lean4 mechanization scaffold for L1_relations.hm
--
-- Imports: L0Ground (Form, ground, f2f, structContinues/Distinct/Orbits,
--                    Similar/Congruent/Simulation, executive opaques)
-- P_1 = 25.  N_1_atomic = 2 (deriver, D).  G_1 = 4.
-- Source: L1_relations.hm

import Hypermath.L0Ground
import Hypermath.Trace

namespace Hypermath

open Hypermath  -- bring ~~/=~/≡ notation into scope

-- ============================================================================
-- §I  Filtration Axiom
-- Simulation → Congruent → Similar. Strict hierarchy. FORM.
-- ============================================================================

/-- **filtration-sim-cong**: ≡ implies =~. -/
axiom filtrationSimCong : ∀ x y : Form, (x ≡ y) → (x =~ y)

/-- **filtration-cong-sim**: =~ implies ~~. -/
axiom filtrationCongSim : ∀ x y : Form, (x =~ y) → (x ~~ y)

-- ============================================================================
-- §II  Derives (all FORM unless marked FRAME)
-- Seven derives: the relation properties of ~~, =~, ≡ in full language.
-- ============================================================================

/-- x ~~ x for all Forms x. FORM, by `axSimilarRefl` (L0 §VIII.b). -/
theorem similarReflexive : ∀ x : Form, x ~~ x := axSimilarRefl

/-- x ~~ y → y ~~ x. FORM, by `axSimilarSymm` (L0 §VIII.b). -/
theorem similarSymmetric : ∀ x y : Form, (x ~~ y) → (y ~~ x) := axSimilarSymm

/-- ax-sim in relation language: f2f(x) ~~ ground for all x. FORM. -/
theorem axSimInRelationLanguage : ∀ x : Form, f2f x ~~ ground :=
  fun x => (closeStructContinues (f2f x)).mp (axSim x)

/-- ax-box in relation language: f2f(f2f(x)) ~~ x for all x. FORM. -/
theorem axBoxInRelationLanguage : ∀ x : Form, f2f (f2f x) ~~ x :=
  fun x => (closeStructOrbits x).mp (axBox x)

/-- ax-diff in relation language: f2f(x) ~~ ground AND ¬(f2f(x) ≡ ground). FORM. -/
theorem axDiffInRelationLanguage :
    ∀ x : Form, (f2f x ~~ ground) ∧ ¬ (f2f x ≡ ground) :=
  fun x => ⟨axSimInRelationLanguage x,
             (closeStructDistinct (f2f x) ground).mp (axDiff x)⟩

/-- f2f(ground) ~~ ground (the ~~ fixed point). FORM. -/
theorem groundFixedPoint : f2f ground ~~ ground :=
  (axDiffInRelationLanguage ground).1

-- A ≡ pair exists. Stated in the source at this point; proved below in §IV.b,
-- because the proof needs `closeSemanticsOpaque` (§IV) to move the one asserted
-- `Semantics ground` into `≡`. It is FORM, not FRAME.
--
-- The forward reference this comment replaced pointed at
-- `L3Ordinatics.simulationPairExists`, which does not exist: it was withdrawn
-- when a full-clause model refuted the *nontrivial* pair, and survives only as
-- the unproved `simulationPairExistsClaim` (L3Ordinatics §V). The weak pair is
-- not that statement and needs no ordinal machinery at all.

-- ============================================================================
-- §III  Graduation — L1 → L2
-- Four NCs. NC-2 closes here; NC-3 is the two filtration axioms of §I; NC-4
-- closes in §IV.b. NC-1 is `similarReflexive`, which is independent of the
-- clauses (see §II), so the graduation rests on an assumption the development
-- has not made. That is stated plainly rather than counted as discharged.
-- ============================================================================

-- NC-1: ~~ is well-defined and reflexive. Independent of the clauses; it
--       inherits the admission of `similarReflexive` and is not a discharge.
theorem nc1_L1 : ∀ x : Form, x ~~ x := similarReflexive

-- NC-2: The ~~/≡ gap is inhabited (f2f(ground) ~~ ground but ¬ (f2f(ground) ≡ ground)).
theorem nc2_L1 : ∃ x y : Form, (x ~~ y) ∧ ¬ (x ≡ y) :=
  ⟨f2f ground, ground, groundFixedPoint, (axDiffInRelationLanguage ground).2⟩

-- NC-3: filtration is in scope (axioms filtrationSimCong, filtrationCongSim above).

-- NC-4: The orbit structure is a defined ~~ class of size ≥ 2.
--       Proved below in §IV.b. Like the ≡ pair above it needs
--       `closeSemanticsOpaque`, so it is stated in source order here and
--       discharged after the closes rather than admitted at this line.

-- Graduation status: FORM once §IV.b closes NC-4. L2 licensed there, not here.

-- ============================================================================
-- §IV  Semantic Closes for Executive Opaques
-- The seven closes are declared in L0Ground §VIII.a, beside the opaques they
-- close: every symbol they mention is an L0 symbol.
-- ============================================================================

/-- **derives-in-n**: the quanta-bearing derivation relation. `DerivesIn n x y`
    says y is reached from x in exactly n applications, landing at `=~`. Four
    coordinates: (start, end, landing level, quanta). Congruence tier. -/
def DerivesIn (n : Nat) (x y : Form) : Prop := Nat.repeat f2f n x =~ y

-- ----------------------------------------------------------------------------
-- §IV.a  The abstraction tier of derives, discharge and definition
-- Three of the seven executive closes forget quanta. Made explicit here.
-- ----------------------------------------------------------------------------

/-- The abstraction map: a quanta-bearing witness yields the abstract relation.
    It runs one way only — there is no inverse, which is the whole content of
    calling `Derives` an abstraction. -/
theorem derivesInToDerives {n : Nat} {x y : Form} (h : DerivesIn n x y) :
    Derives x y :=
  (closeDerivesOpaque x y).mpr ⟨n, h⟩

/-- And `Derives` is exactly the image of that map: nothing else inhabits it. -/
theorem derivesIsAbstractionOfDerivesIn (x y : Form) :
    Derives x y ↔ ∃ n : Nat, DerivesIn n x y :=
  closeDerivesOpaque x y

/-- **The forgetting is real.** Two witnesses at different quanta give the same
    abstract fact, definitionally. A `=~` relation would have to separate them;
    this one cannot, so its tier is `~=`. -/
theorem derivesForgetsQuanta {x y : Form} {m n : Nat}
    (hm : DerivesIn m x y) (hn : DerivesIn n x y) :
    derivesInToDerives hm = derivesInToDerives hn :=
  rfl

/-- `discharge` is defined as `Derives`, so it inherits the abstraction tier:
    a discharge records that evidence exists, never how much. -/
theorem dischargeIsAbstractionTier (c e : Form) :
    Discharge c e ↔ ∃ n : Nat, DerivesIn n e c :=
  (closeDischargeOpaque c e).trans (closeDerivesOpaque e c)

/-- `definition` is defined as `Derives`, so it inherits the abstraction tier:
    a definition records that the definiens is reachable, never at what cost. -/
theorem definitionIsAbstractionTier (n x : Form) :
    Definition n x ↔ ∃ k : Nat, DerivesIn k n x :=
  (closeDefinitionOpaque n x).trans (closeDerivesOpaque n x)

-- ----------------------------------------------------------------------------
-- §IV.b  The two graduation items that need the semantic closes
-- Both are FORM. Both were admitted before 2026-09-21 with comments claiming a
-- later layer would supply them; neither needs a later layer. What they need is
-- `closeSemanticsOpaque`, which is three declarations above, so they are proved
-- here instead of forwarded.
-- ----------------------------------------------------------------------------

/-- ground is ≡-reflexive. `axGroundSemanticsAx` is the only `Semantics`
    assertion in the development, so ground is the only Form for which
    ≡-reflexivity is available: it does not generalise. FORM.

    §IV.c says exactly how far it fails to generalise:
    `reflexivityIsGroundReachability` shows `x ≡ x` holds precisely when x is
    similar to some iterate of ground, so this is not a gap peculiar to `≡`. -/
theorem groundSimulatesItself : ground ≡ ground :=
  (closeSemanticsOpaque ground).mp axGroundSemanticsAx

/-- A ≡ pair exists, hence the top of the filtration chain is inhabited. FORM.
    Discharges L1 step 10.

    Both filtration axioms run forwards from `≡`, so the ground reflexive pair
    descends to `=~` and then to `~~` with no further assumption. This is the
    weak pair. The nontrivial pair `∃ x y, x ~~ y ∧ x ≡ y ∧ ¬ (x = y)` is a
    different statement, is refuted by the full-clause model, and remains
    unproved as `L3Ordinatics.simulationPairExistsClaim`. -/
theorem simulationPairExists_L1 : ∃ x y : Form, (x ~~ y) ∧ (x ≡ y) :=
  ⟨ground, ground,
   filtrationCongSim ground ground (filtrationSimCong ground ground groundSimulatesItself),
   groundSimulatesItself⟩

/-- f2f(ground) ≠ ground. FORM.

    ax-diff denies `f2f ground ≡ ground`. If forming collapsed at ground, that
    denial would be a denial of ground's own ≡-reflexivity, which
    `axGroundSemanticsAx` asserts. So the orbit is not a single point. Note the
    direction: this argument runs from ≡ downwards and never needs the reverse
    filtration implication, which `HypermathCountermodel.reverse_filtration_fails`
    shows is unavailable. -/
theorem f2fGroundNeGround : f2f ground ≠ ground := by
  intro collapse
  have reflexive : f2f ground ≡ ground := by
    rw [collapse]
    exact groundSimulatesItself
  exact (axDiffInRelationLanguage ground).2 reflexive

/-- NC-4: the orbit structure is a defined ~~ class of size ≥ 2. FORM.
    This closes the fourth graduation obligation stated in §III. -/
theorem nc4_L1 : ∃ x y : Form, (x ~~ y) ∧ x ≠ y :=
  ⟨f2f ground, ground, groundFixedPoint, f2fGroundNeGround⟩

/-- ground is =~-reflexive. `axGroundSubstanceAx` is the only `Substance`
    assertion, so as with `≡` this holds at ground and nowhere else. FORM.

    "As with `≡`" is literally true, not an analogy: `reflexivityLevelsCoincide`
    proves the two reflexivities are the same condition point by point. -/
theorem groundIsCongruentToItself : ground =~ ground :=
  (closeSubstanceOpaque ground).mp axGroundSubstanceAx

/-- `Definition ground ground`, restated at L1 for existing citations.
    The proof now lives at `L0Ground.definitionOfGround`. -/
theorem definitionOfGround_L1 : Definition ground ground := definitionOfGround

-- ----------------------------------------------------------------------------
-- §IV.c  The two upper reflexivities are one condition, and it is reachability
--
-- §IV.b proves reflexivity at ground twice, once at `≡` and once at `=~`, and
-- each proof remarks that it does not generalise. Neither says what it is
-- equivalent to, and the answer is already available: the triangle axioms
-- (`axSyntaxRequiresSubstance`, `axSubstanceRequiresSemantics`,
-- `axSemanticsRequiresSyntax`) make the three predicates interderivable, and
-- the three opaque closes read them as `=~`-reflexivity, `≡`-reflexivity and
-- similar-reachability from ground. So the three are one condition. Nothing new
-- is assumed here; this is a consequence of clauses stated above.
-- ----------------------------------------------------------------------------

/-- The triangle, traversed. `Substance` implies `Semantics` implies `HMSyntax`
    implies `Substance`, so asserting any one of the three at a point asserts
    all three. FORM. -/
theorem triangleVerticesCoincide (x : Form) :
    HMSyntax x ↔ Substance x :=
  ⟨axSyntaxRequiresSubstance x,
   fun s => axSemanticsRequiresSyntax x (axSubstanceRequiresSemantics x s)⟩

/-- **The two upper reflexivities are the same condition.** `x =~ x` and
    `x ≡ x` hold of exactly the same Forms. FORM.

    This is why §IV.b needed two separate ground assumptions and got no further
    with either: they were never two facts. `axGroundSubstanceAx` and
    `axGroundSemanticsAx` assert the same thing about ground through different
    predicates. -/
theorem reflexivityLevelsCoincide (x : Form) : (x =~ x) ↔ (x ≡ x) :=
  ⟨fun c => (closeSemanticsOpaque x).mp
      (axSubstanceRequiresSemantics x ((closeSubstanceOpaque x).mpr c)),
   fun s => (closeSubstanceOpaque x).mp
      (axSyntaxRequiresSubstance x
        (axSemanticsRequiresSyntax x ((closeSemanticsOpaque x).mpr s)))⟩

/-- **And the condition is reachability.** A Form is `=~`-reflexive exactly
    when it is `~~` to some iterate of ground. FORM.

    The filtration runs downwards --- `≡` to `=~` to `~~` --- but reflexivity
    does not respect that direction: the top two levels agree with each other
    and with a `~~` statement about the ground chain. Reflexivity is therefore
    not a property of a relation here so much as a property of a point's
    position relative to ground. -/
theorem reflexivityIsGroundReachability (x : Form) :
    (x =~ x) ↔ ∃ n : Nat, Nat.repeat f2f n ground ~~ x :=
  ⟨fun c => (closeSyntaxOpaque x).mp
      ((triangleVerticesCoincide x).mpr ((closeSubstanceOpaque x).mpr c)),
   fun r => (closeSubstanceOpaque x).mp
      ((triangleVerticesCoincide x).mp ((closeSyntaxOpaque x).mpr r))⟩

/-- The three readings in one statement: `≡`-reflexive, `=~`-reflexive and
    reachable-from-ground are mutually equivalent, pointwise. FORM. -/
theorem upperReflexivitiesAndReachabilityAgree (x : Form) :
    ((x ≡ x) ↔ (x =~ x)) ∧
      ((x =~ x) ↔ ∃ n : Nat, Nat.repeat f2f n ground ~~ x) :=
  ⟨(reflexivityLevelsCoincide x).symm, reflexivityIsGroundReachability x⟩

/-- **The global form.** `=~` is reflexive on all of `Form` exactly when the
    ground chain is `~~`-cofinal in `Form`. FORM.

    So the question "is `=~` reflexive?" is not a question about `=~`. It asks
    whether forming from ground reaches everything up to similarity, and the
    clauses do not settle that:
    `HypermathCountermodel.IrreflexiveSimilar.congruent_reflexivity_fails_with_unreached_form`
    is a model of all 24 prefix clauses with a Form the chain never reaches. -/
theorem globalCongruentReflexivityIsCofinality :
    (∀ x : Form, x =~ x) ↔ ∀ x : Form, ∃ n : Nat, Nat.repeat f2f n ground ~~ x :=
  ⟨fun refl x => (reflexivityIsGroundReachability x).mp (refl x),
   fun cofinal x => (reflexivityIsGroundReachability x).mpr (cofinal x)⟩

-- Graduation status: FORM. All four NCs discharged. L2 licensed.

-- ============================================================================
-- §V  Derives is Directional
-- Discharges L0 §VIII self-kernel step 40 (FRAME/L1).
-- ============================================================================

/-- Derives is not symmetric. Witness: x := ground, y := f2f(ground). FORM.
    Discharges L0 step 40; the proof is `L0Ground.derivesIsDirectional_FRAME`. -/
theorem derivesIsDirectional :
    ¬ ∀ x y : Form, Derives x y → Derives y x :=
  derivesIsDirectional_FRAME

-- ============================================================================
-- §VI  Trace Axiom
-- ============================================================================

/-- Every application of □ carries one of three trace levels:
    (a) trace at ≡: f2f(x) ≡ x;  (b) trace at =~: f2f(x) =~ x;
    (c) trace at ~~ (floor): f2f(x) ~~ x.
    (c) is always guaranteed by ax-sim. Levels are exhaustive per application step. -/
axiom traceLevels :
    ∀ x : Form,
      (f2f x ~~ x) ∧                           -- (c) floor: always
      ((f2f x =~ x) → (f2f x ~~ x)) ∧          -- (b) =~ implies ~~
      ((f2f x ≡ x) → (f2f x =~ x))             -- (a) ≡ implies =~

/-- The displayed pairwise orbit relations follow from the declared trace axiom.
    Placed after traceLevels because ax-sim plus symmetry alone does not give
    the third pair. This proves these pairs, not transitivity of Similar. -/
theorem orbitStructure :
    (f2f ground ~~ ground) ∧
    (f2f (f2f ground) ~~ ground) ∧
    (f2f (f2f ground) ~~ f2f ground) :=
  ⟨groundFixedPoint,
   axSimInRelationLanguage (f2f ground),
   (traceLevels (f2f ground)).1⟩

-- ============================================================================
-- §VI.a  Everything the clauses say about the filtration, in one statement
-- ============================================================================

/-- **The eight conditions, proved in the layer.** Each conjunct is a direct
    consequence of the declared clauses, so any model of them satisfies all
    eight. FORM.

    `HypermathCountermodel.FreeFiltration.prefixAxioms_iff_conditions` proves
    the converse: a triple of relations satisfying exactly these eight satisfies
    all 24 clauses. The two together are a characterization rather than a list
    of independence results --- the clauses assert two inclusions, three facts
    about forming at the bottom level, one denial at the top, and the pinning of
    both upper diagonals to reachability, and they assert nothing else about
    `~~`, `=~` or `≡`.

    Read down the list, the asymmetry is the point. Five of the eight are about
    `~~`; one is about `≡`; the remaining two are the couplings. Neither upper
    relation is constrained anywhere off its own diagonal except by the
    inclusions. -/
theorem filtrationConditionsHold :
    (∀ x y : Form, (x ≡ y) → (x =~ y)) ∧
    (∀ x y : Form, (x =~ y) → (x ~~ y)) ∧
    (∀ x : Form, f2f x ~~ x) ∧
    (∀ x : Form, f2f x ~~ ground) ∧
    (∀ x : Form, f2f (f2f x) ~~ x) ∧
    (∀ x : Form, ¬ (f2f x ≡ ground)) ∧
    (∀ x : Form, (x =~ x) ↔ ∃ n : Nat, Nat.repeat f2f n ground ~~ x) ∧
    (∀ x : Form, (x ≡ x) ↔ ∃ n : Nat, Nat.repeat f2f n ground ~~ x) :=
  ⟨filtrationSimCong,
   filtrationCongSim,
   fun x => (traceLevels x).1,
   axSimInRelationLanguage,
   axBoxInRelationLanguage,
   fun x => (axDiffInRelationLanguage x).2,
   reflexivityIsGroundReachability,
   fun x => ((reflexivityLevelsCoincide x).symm).trans
     (reflexivityIsGroundReachability x)⟩

/-- The one clause that constrains `≡` away from its own diagonal, isolated.
    `FreeSimulation` shows it is the only one, and the sixth conjunct above is
    where it enters the characterization. FORM. -/
theorem simulationDeniesEveryImageAtGround : ∀ x : Form, ¬ (f2f x ≡ ground) :=
  fun x => (axDiffInRelationLanguage x).2

-- ============================================================================
-- §VII  Deriver and Derivation Matrix
-- N_1_atomic = 2: deriver, D.
-- ============================================================================

/-- The deriver: a Form whose purpose is to traverse D and produce closure
    certificates.

    Its ≡-cycle is **not** discharged in L3Ordinatics, which is what this
    docstring used to say. L3 carries only the conditional
    `driverInDAtSimulationOfCycle`, which takes the cycle as a hypothesis, and
    `selfDerivation_iff_driverCycleClaim`, which shows the layer's target is
    equivalent to it rather than a proof of it.
    `HypermathCountermodel.driver_cycle_claim_fails` and
    `HypermathFullAxiomModel.driver_cycle_claim_fails` both refute it. The cycle
    is an open claim, `driverCycleClaim` below. -/
axiom deriver : Form

/-- One apply-step admitted to D, with evidence that it preserves at least =~.
    A ~~ step alone is insufficient. Simulation steps enter by filtrationSimCong. -/
def DStep (x y : Form) : Prop := y = f2f x ∧ Congruent y x

/-- The finite trace witness for a D-entry, with its start and end in the type.
    This implements the =~ floor in L1_relations.hm:401–415. It does not yet
    encode the strongest per-step relation, nondecreasing trace metadata, or
    the separate opaque DerivationPath and its L3 limit-path interpretation. -/
abbrev DEntry (x y : Form) := Trace DStep x y

/-- D[x][y] holds precisely when a finite apply-trace preserving =~ exists.
    The witness remains available in DEntry; D is its proposition of existence. -/
def D (x y : Form) : Prop := Nonempty (DEntry x y)

/-- The concrete zero-step self-read at x, requiring no congruence premise. -/
def selfRead (x : Form) : DEntry x x := Trace.nil x

/-- A nonempty D-entry requires actual evidence of the edge's congruence.
    f2f remains an uninterpreted source parameter, so this is not executable. -/
noncomputable def dEntryStep (x : Form) (h : Congruent (f2f x) x) : DEntry x (f2f x) :=
  Trace.cons ⟨rfl, h⟩ (Trace.nil (f2f x))

/-- Composition preserves every edge witness and requires matching endpoints. -/
def dEntryCompose {x y z : Form} (p : DEntry x y) (q : DEntry y z) : DEntry x z :=
  Trace.compose p q

theorem selfReadLength (x : Form) : Trace.length (selfRead x) = 0 := rfl

/-- The guarded step constructor records exactly one edge. -/
theorem dEntryStepLength (x : Form) (h : Congruent (f2f x) x) :
    Trace.length (dEntryStep x h) = 1 := rfl

/-- A D-entry's recorded length gives its exact finite apply-iteration. -/
theorem dEntryEndpointIteration {x y : Form} (p : DEntry x y) :
    Nat.repeat f2f (Trace.length p) x = y := by
  have iterate_step : ∀ (n : Nat) (a : Form),
      Nat.repeat f2f (n + 1) a = Nat.repeat f2f n (f2f a) := by
    intro n a
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg f2f ih
  induction p with
  | nil => rfl
  | cons edge tail ih =>
    rw [Trace.length, iterate_step, ← edge.1]
    exact ih

/-- Without an admissible D-step, every existing witness is a zero-step read. -/
theorem dEntryNoSteps (noSteps : ∀ x y : Form, ¬ DStep x y)
    {x y : Form} (p : DEntry x y) : Trace.length p = 0 ∧ x = y := by
  cases p with
  | nil => exact ⟨rfl, rfl⟩
  | cons edge tail => exact False.elim (noSteps _ _ edge)

/-- D[x][x] for every x: every Form has a zero-step self-read in D. FORM. -/
theorem dIsReflexive : ∀ x : Form, D x x :=
  fun x => ⟨selfRead x⟩

/-- D is transitive by composition of its finite trace witnesses. -/
theorem dIsTransitive {x y z : Form} : D x y → D y z → D x z := by
  rintro ⟨p⟩ ⟨q⟩
  exact ⟨dEntryCompose p q⟩

/-- `D` is at the abstraction tier for the same reason as `Derives`: `Nonempty`
    forgets the witness, hence its length. Distinct traces of distinct quanta
    over the same endpoints are one and the same element of `D`. -/
theorem dForgetsQuanta {x y : Form} (p q : DEntry x y) :
    (⟨p⟩ : D x y) = ⟨q⟩ :=
  rfl

/-- The universal ground-spanning claim proposed in L1_relations.hm:418–425.
    This is a proposition, not an assumed theorem. With finite D witnesses,
    L3's limit separation refutes it in notGroundSpanningClaim. The original
    admitted dSpansGround theorem has therefore been withdrawn. -/
def groundSpanningClaim : Prop := ∀ y : Form, D ground y

/-- The reflexive, zero-step D entry exists. It does not supply a two-step
    simulation cycle; that separate claim remains unproved. -/
theorem driverIsInD : D deriver deriver :=
  dIsReflexive deriver

/-- The proposed two-step simulation cycle, retained as an unproved claim.
    FullAxiomModel satisfies all 44 clauses and refutes this statement.
    The former admitted driverCycle_FRAME theorem has been withdrawn. -/
def driverCycleClaim : Prop := f2f (f2f deriver) ≡ deriver

-- ============================================================================
-- §VIII  L1 Self-Kernel
-- P_1 = 25 steps. N_1_atomic = 2 (deriver, D). G_1 = 4.
-- FRAME residuals:
--   step 10: simulation pairs — the weak L1 theorem remains admitted;
--            the stronger nontrivial L3 claim is refuted in a full-clause model.
--   step 21: deriver ==-cycle content — unproved driverCycleClaim.
--   step 25: D[deriver][deriver] at ≡ level — conditional on driverCycleClaim.
-- All 25 steps represented by the declarations above.
-- ============================================================================

end Hypermath
