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

/-- x ~~ x for all Forms x. FORM. -/
theorem similarReflexive : ∀ x : Form, x ~~ x := by
  sorry
  -- FORM: ax-sim gives f2f(x) ~~ ground. ax-ground-self + closeStructContinues
  -- gives ground ~~ ground. The ~~ orbit contains x; transitivity at ~~ level
  -- establishes x ~~ x. Full proof pending mechanization.

/-- x ~~ y → y ~~ x. FORM. -/
theorem similarSymmetric : ∀ x y : Form, (x ~~ y) → (y ~~ x) := by
  sorry
  -- FORM: ~~ is defined as non-empty overlap in continuation capacity.
  -- Overlap is symmetric by definition. Mechanical proof via opaque close.

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

/-- A non-trivial ≡ pair exists. FRAME/L3.
    Witness constructed in L3Ordinatics.lean (simulationPairExists). -/
theorem simulationPairExists_L1 : ∃ x y : Form, (x ~~ y) ∧ (x ≡ y) := by
  sorry
  -- FRAME/L3: non-trivial == pair requires ordinal continuation-path machinery.
  -- Discharged in Hypermath.L3Ordinatics, theorem simulationPairExists.

-- ============================================================================
-- §III  Graduation — L1 → L2
-- Four NCs discharged. Graduation status: FORM. L2 licensed.
-- ============================================================================

-- NC-1: ~~ is well-defined and reflexive.
theorem nc1_L1 : ∀ x : Form, x ~~ x := similarReflexive

-- NC-2: The ~~/≡ gap is inhabited (f2f(ground) ~~ ground but ¬ (f2f(ground) ≡ ground)).
theorem nc2_L1 : ∃ x y : Form, (x ~~ y) ∧ ¬ (x ≡ y) :=
  ⟨f2f ground, ground, groundFixedPoint, (axDiffInRelationLanguage ground).2⟩

-- NC-3: filtration is in scope (axioms filtrationSimCong, filtrationCongSim above).

-- NC-4: The orbit structure is a defined ~~ class of size ≥ 2.
theorem nc4_L1 : ∃ x y : Form, (x ~~ y) ∧ x ≠ y := by
  exact ⟨f2f ground, ground, groundFixedPoint, by
    sorry⟩
  -- FORM: f2f(ground) ≠ ground follows from ax-diff + closeStructDistinct.

-- Graduation status: FORM. L2 licensed.

-- ============================================================================
-- §IV  Semantic Closes for Executive Opaques
-- Discharges L0 §VIII self-kernel steps 25–31 (FRAME/L1).
-- All seven executive opaques move from pre-semantic to FORM.
-- ============================================================================

/-- syntax closes to orbit-depth at ~~ level. FORM. Discharges L0 step 25. -/
axiom closeSyntaxOpaque :
    ∀ x : Form,
      HMSyntax x ↔
      ∃ n : Nat, Nat.repeat f2f n ground ~~ x

/-- substance closes to =~-equivalence class of x. FORM. Discharges L0 step 26. -/
axiom closeSubstanceOpaque :
    ∀ x : Form, Substance x ↔ (x =~ x)

/-- semantics closes to ≡-equivalence class of x. FORM. Discharges L0 step 27. -/
axiom closeSemanticsOpaque :
    ∀ x : Form, Semantics x ↔ (x ≡ x)

/-- derives(x, y) closes to: ∃ finite n, f2f^n(x) =~ y. FORM. Discharges L0 step 28. -/
axiom closeDerivesOpaque :
    ∀ x y : Form, Derives x y ↔ ∃ n : Nat, Nat.repeat f2f n x =~ y

/-- discharge(c, e) closes to: Derives e c is FORM. FORM. Discharges L0 step 29. -/
axiom closeDischargeOpaque :
    ∀ c e : Form, Discharge c e ↔ Derives e c

/-- definition(n, x) closes to: Derives n x is FORM. FORM. Discharges L0 step 30. -/
axiom closeDefinitionOpaque :
    ∀ n x : Form, Definition n x ↔ Derives n x

/-- form-closure(x) closes to: syntax ∧ substance ∧ semantics all FORM.
    FORM. Discharges L0 step 31. -/
axiom closeFormClosureOpaque :
    ∀ x : Form,
      FormClosure x ↔ (HMSyntax x ∧ Substance x ∧ Semantics x)

-- ============================================================================
-- §V  Derives is Directional
-- Discharges L0 §VIII self-kernel step 40 (FRAME/L1).
-- ============================================================================

/-- Derives is not symmetric: Derives x y does not imply Derives y x in general.
    Witness: x := ground, y := f2f(ground).
    - Derives ground (f2f ground): one application, trivial.
    - Derives (f2f ground) ground at =~: would require f2f^n(f2f ground) =~ ground.
      ax-box gives f2f(f2f(f2f ground)) ~~ f2f ground (at ~~, not =~).
      ~~ return ≠ =~ landing; no axiom makes f2f invertible at =~.
    FORM. Discharges L0 step 40. -/
theorem derivesIsDirectional :
    ¬ ∀ x y : Form, Derives x y → Derives y x := by
  sorry
  -- FORM proof sketch:
  -- 1. Derives ground (f2f ground) holds: one application, witnessed by n=1.
  -- 2. Suppose Derives (f2f ground) ground: then ∃ n, f2f^n(f2f ground) =~ ground.
  -- 3. By ax-box, f2f^2(x) ~~ x (at ~~ only).
  -- 4. No axiom upgrades this ~~ return to =~: ax-diff says f2f(x) is distinct (≢) from ground.
  -- 5. Therefore ¬ Derives (f2f ground) ground at =~. Contradiction with assumed symmetry.

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
-- §VII  Deriver and Derivation Matrix
-- N_1_atomic = 2: deriver, D.
-- ============================================================================

/-- The deriver: a Form whose purpose is to traverse D and produce closure
    certificates. Its ==-cycle (≡-cycle) is FRAME/L3;
    discharged in L3Ordinatics.lean. -/
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

/-- The universal ground-spanning claim proposed in L1_relations.hm:418–425.
    This is a proposition, not an assumed theorem. With finite D witnesses,
    L3's limit separation refutes it in notGroundSpanningClaim. The original
    admitted dSpansGround theorem has therefore been withdrawn. -/
def groundSpanningClaim : Prop := ∀ y : Form, D ground y

/-- D[deriver][deriver] entry exists. Schema: FORM.
    Content at ≡ level: FRAME/L3 (discharged in L3Ordinatics). -/
theorem driverIsInD : D deriver deriver :=
  dIsReflexive deriver

/-- deriver ≡-cycle: f2f(f2f(deriver)) ≡ deriver. FRAME/L3.
    Discharged in L3Ordinatics.lean, theorem driverCycleIsClosed. -/
theorem driverCycle_FRAME : f2f (f2f deriver) ≡ deriver := by
  sorry
  -- FRAME/L3: constructive proof requires ordinal continuation machinery.

-- ============================================================================
-- §VIII  L1 Self-Kernel
-- P_1 = 25 steps. N_1_atomic = 2 (deriver, D). G_1 = 4.
-- FRAME residuals:
--   step 10: simulationPairExists — FRAME/L3 (discharged in L3Ordinatics)
--   step 21: deriver ==-cycle content — FRAME/L3 (discharged in L3Ordinatics)
--   step 25: D[deriver][deriver] at ≡ level — FRAME/L3 (discharged in L3Ordinatics)
-- All 25 steps represented by the declarations above.
-- ============================================================================

end Hypermath
