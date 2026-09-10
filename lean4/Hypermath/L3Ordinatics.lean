-- Hypermath.L3Ordinatics
-- Layer 3: Ordinatics — proposed terminal layer
-- Lean4 mechanization scaffold for L3_ordinatics.hm
--
-- Introduces: ordinalLimit, ordinalSucc, ordinalApply, finiteApplyFromGround.
-- Finite closure and witnessed-length observations are now constructive.
-- The source's terminal-closure claims still include admitted proof obligations.
--
-- P_3 = 18.  N_3_atomic = 2 (ordinalLimit, ordinalSucc).
-- FORM/FRAME comments below retain source classifications, not proof verdicts.
-- Source: L3_ordinatics.hm

import Hypermath.L2Operations

namespace Hypermath

-- ============================================================================
-- §I  Layer Permits and Prohibits
-- (Copied from L2 graduation block for traceability.)
-- ============================================================================

-- Permits L3:
--   (a) ordinalLimit :: Form — first infinite ordinal position.
--   (b) ordinalSucc :: Form → Form — ordinal successor.
--   (c) Ordinal arithmetic: +_ord, ×_ord over ordinal Forms.
--   (d) Closing simulation-pair-exists via compose + ordinal continuation.
--   (e) Deriver ≡-cycle constructive proof.

-- Prohibits L3:
--   (a) New primitive operations beyond ordinatics.
--   (b) Commutativity for + (carries forward from L2).

-- ============================================================================
-- §II  Primitives — Ordinal Structure
-- Two atomic Forms at L3. Both definition-acts. FORM.
-- ============================================================================

/-- The first Form unreachable by any finite f2f-chain from ground.
    The Form naming the end of the finite apply-chain sequence.
    ordinalLimit is not f2f^n(ground) for any finite n (ax-limit-not-finite). -/
axiom ordinalLimit : Form

/-- ordinalSucc(x): the Form one step beyond x in the ordinal ordering.
    For finite ordinals: ordinalSucc(f2f^n(ground)) ~ f2f^{n+1}(ground).
    For ordinalLimit: ordinalSucc(ordinalLimit) is a Form beyond ordinalLimit.
    Structural: ordinalSucc(x) ~~ f2f(x) at ~~. ordinalSucc(x) =~ x + f2f(ground) at =~. -/
axiom ordinalSucc : Form → Form

-- ============================================================================
-- §III  Axioms for Ordinal Structure
-- ============================================================================

/-- **ax-limit-not-finite**: ordinalLimit is not reachable by any finite f2f-chain. -/
axiom axLimitNotFinite : ∀ n : Nat, ¬ (Nat.repeat f2f n ground ≡ ordinalLimit)

/-- **ax-limit-derives**: the limit-path from ground exists; its end =~ ordinalLimit.
    The infinite composition of finite continuation paths reaches ordinalLimit. -/
axiom axLimitDerives :
    ∃ limitPath : DerivationPath,
      (pathStart limitPath ~~ ground) ∧
      (pathEnd limitPath =~ ordinalLimit)

/-- **ax-succ-extends**: ordinalSucc strictly extends every Form. -/
axiom axSuccExtends :
    ∀ x : Form,
      Derives x (ordinalSucc x) ∧ ¬ (ordinalSucc x ≡ x)

/-- **ax-limit-is-limit**: ordinalLimit is the least upper bound of all finite ordinals.
    For all finite n: Derives(f2f^n(ground), y) for any upper bound y → Derives(ordinalLimit, y). -/
axiom axLimitIsLimit :
    ∀ y : Form,
      (∀ n : Nat, Derives (Nat.repeat f2f n ground) y) →
      Derives ordinalLimit y

-- ============================================================================
-- §IV  Ordinal Arithmetic
-- ============================================================================

/-- The native Form at finite apply-position n, as in L3_ordinatics.hm:163–167.
    This observes the existing ground/f2f parameters, not a tagged substitute
    for Form. Distinct n are not asserted to produce distinct Forms. -/
noncomputable def finiteApplyPosition (n : Nat) : Form := Nat.repeat f2f n ground

/-- The least finite f2f-closure of ground specified in L3_ordinatics.hm:123–128.
    Membership retains a finite iteration witness; it does not assert unique
    numeral representations or agreement with the opaque ordinalApply. -/
def finiteApplyFromGround (x : Form) : Prop := ∃ n : Nat, finiteApplyPosition n = x

theorem finiteApplyIffIteration (x : Form) :
    finiteApplyFromGround x ↔ ∃ n : Nat, Nat.repeat f2f n ground = x := Iff.rfl

theorem finiteApplyGround : finiteApplyFromGround ground := ⟨0, rfl⟩

theorem finiteApplyPositionMember (n : Nat) :
    finiteApplyFromGround (finiteApplyPosition n) := ⟨n, rfl⟩

theorem finiteApplyClosed {x : Form} (hx : finiteApplyFromGround x) :
    finiteApplyFromGround (f2f x) := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n + 1, rfl⟩

/-- Any predicate containing ground and closed under f2f contains this closure. -/
theorem finiteApplyMinimal (P : Form → Prop) (base : P ground)
    (step : ∀ x : Form, P x → P (f2f x))
    {x : Form} (hx : finiteApplyFromGround x) : P x := by
  obtain ⟨n, rfl⟩ := hx
  induction n with
  | zero => exact base
  | succ n ih => exact step _ ih

/-- Iteration counts add under sequential application. This is an exact equality
    of existing Forms and does not identify ordinalSucc with f2f. -/
theorem finiteApplyIterationAdd (m n : Nat) (x : Form) :
    Nat.repeat f2f (m + n) x = Nat.repeat f2f n (Nat.repeat f2f m x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f2f ih

/-- A Form-valued length observation obtained from the witness's actual edges.
    No conversion to opaque DerivationPath, pathLength, or ordinalApply is assumed. -/
noncomputable def finiteTraceLength {x y : Form} (p : DEntry x y) : Form :=
  finiteApplyPosition (Trace.length p)

theorem finiteTraceLengthMember {x y : Form} (p : DEntry x y) :
    finiteApplyFromGround (finiteTraceLength p) :=
  finiteApplyPositionMember (Trace.length p)

theorem finiteTraceLengthSelfRead (x : Form) :
    finiteTraceLength (selfRead x) = ground := rfl

theorem finiteTraceLengthStep (x : Form) (h : Congruent (f2f x) x) :
    finiteTraceLength (dEntryStep x h) = f2f ground := rfl

theorem finiteTraceLengthCompose {x y z : Form} (p : DEntry x y) (q : DEntry y z) :
    finiteTraceLength (dEntryCompose p q) =
      Nat.repeat f2f (Trace.length q) (finiteTraceLength p) := by
  unfold finiteTraceLength dEntryCompose
  rw [Trace.length_compose]
  exact finiteApplyIterationAdd _ _ ground

/-- Expansion preserves the Form-valued observation extracted from actual atoms. -/
theorem finiteTraceLengthExpand {x y : Form} (e : TraceExpr DStep x y) :
    finiteTraceLength e.expand = finiteApplyPosition e.length :=
  congrArg finiteApplyPosition (TraceExpr.length_expand e)

theorem finiteTraceLengthExpandSeq {x y z : Form}
    (p : TraceExpr DStep x y) (q : TraceExpr DStep y z) :
    finiteTraceLength (TraceExpr.seq p q).expand =
      Nat.repeat f2f q.length (finiteApplyPosition p.length) := by
  rw [finiteTraceLengthExpand]
  exact finiteApplyIterationAdd _ _ ground

/-- A real D-entry from ground supplies a native finite-closure witness. -/
theorem dEntryFromGroundFinite {y : Form} (p : DEntry ground y) :
    finiteApplyFromGround y := ⟨Trace.length p, dEntryEndpointIteration p⟩

/-- Simulation reflexivity at finite apply-positions follows from the existing
    trace floor and syntax/substance/semantics axioms. It is not assumed globally. -/
theorem finiteApplyPositionSimulation (n : Nat) :
    Simulation (finiteApplyPosition n) (finiteApplyPosition n) := by
  have syntaxWitness : HMSyntax (finiteApplyPosition n) :=
    (closeSyntaxOpaque _).mpr ⟨n + 1, (traceLevels (finiteApplyPosition n)).1⟩
  have semanticsWitness : Semantics (finiteApplyPosition n) :=
    axSubstanceRequiresSemantics _ (axSyntaxRequiresSubstance _ syntaxWitness)
  exact (closeSemanticsOpaque _).mp semanticsWitness

/-- Source clause (c): ordinalLimit is outside the finite closure. This uses
    axLimitNotFinite plus the explicitly derived finite Simulation reflexivity,
    separately from the logical-axiom-free finite observation proofs above. -/
theorem finiteApplyLimitExcluded : ¬ finiteApplyFromGround ordinalLimit := by
  rintro ⟨n, hn⟩
  apply axLimitNotFinite n
  change Simulation (finiteApplyPosition n) ordinalLimit
  rw [← hn]
  exact finiteApplyPositionSimulation n

/-- The finite derivation matrix cannot reach ordinalLimit from ground. -/
theorem ordinalLimitNotInD : ¬ D ground ordinalLimit := by
  rintro ⟨p⟩
  exact finiteApplyLimitExcluded (dEntryFromGroundFinite p)

/-- The retained native ground-spanning claim is refuted for the finite D
    interpretation: its universal quantifier would include ordinalLimit. -/
theorem notGroundSpanningClaim : ¬ groundSpanningClaim := by
  intro spans
  exact ordinalLimitNotInD (spans ordinalLimit)

/-- ordinalApply(p)(x): apply p to x in the ordinal sense.
    ordinalApply(ground)(x) =~ x; ordinalApply(f2f(ground))(x) =~ f2f(x);
    ordinalApply(ordinalLimit)(x) = limit ordinal Form constructed from x. -/
axiom ordinalApply : Form → Form → Form

/-- The source's proposed zero-action law. It remains a named proposition rather
    than an admitted theorem: ordinalApply has no declared computation clause. -/
def ordinalZeroIdentityClaim : Prop :=
  ∀ x : Form, ordinalApply ground x =~ x

/-- The source's proposed successor-action law. The current logical clauses do
    not connect ordinalSucc and ordinalApply strongly enough to derive it. -/
def ordinalSuccAppliesClaim : Prop :=
  ∀ p x : Form,
    ordinalApply (ordinalSucc p) x =~ f2f (ordinalApply p x)

/-- The source's proposed path-length arithmetic law, including its operand order.
    A checked full-clause model refutes this proposition, so it cannot discharge
    the L2 FRAME without an additional bridge. -/
def pathLengthArithmeticClaim : Prop :=
  ∀ p q : DerivationPath,
    pathLength (compose p q) =~ ordinalApply (pathLength q) (pathLength p)

-- ============================================================================
-- §V  Simulation-Pair-Exists Closure
-- Discharges L1 FRAME simulationPairExists_L1 (step 10 of L1 self-kernel).
-- Witness: (ground, ordinalApply ordinalLimit ground).
-- ============================================================================

/-- A non-trivial ≡ pair exists. FORM.
    Witness: x := ground, y := ordinalApply(ordinalLimit)(ground).
    - x ~~ y: by ax-sim, all Forms are ~~ to ground.
    - y =~ x: ax-limit-is-limit (LUB property) → y lands in ground's =~-class.
    - y ≡ x: the limit-path starting at ground IS the canonical continuation path
             of ground. ordinalApply(ordinalLimit)(ground) and ground carry the
             same full continuation record — same path object at ≡ level.
    - y ≠ x syntactically: y sits at ordinalLimit position, not at 0. FORM. -/
theorem simulationPairExists :
    ∃ x y : Form, (x ~~ y) ∧ (x ≡ y) ∧ ¬ (x = y) := by
  refine ⟨ground, ordinalApply ordinalLimit ground, ?_, ?_, ?_⟩
  · -- ground ~~ ordinalApply ordinalLimit ground
    sorry
    -- ax-sim: f2f(ordinalApply ordinalLimit ground) ~~ ground.
    -- similarSymmetric + axSimInRelationLanguage gives the converse direction.
  · -- ground ≡ ordinalApply ordinalLimit ground
    sorry
    -- The limit-path (axLimitDerives) starts at ground and is the canonical
    -- continuation trace of ground. ordinalApply ordinalLimit ground is the end
    -- of ground's own continuation path → same path record at ≡ level.
  · -- ordinalApply ordinalLimit ground ≠ ground
    sorry
    -- axLimitNotFinite: no f2f^n(ground) ≡ ordinalLimit.
    -- ordinalApply ordinalLimit ground sits at the ordinalLimit position,
    -- whereas ground sits at position 0. They are structurally distinct Forms.

-- ============================================================================
-- §VI  Deriver ≡-Cycle Constructive Proof
-- Discharges L1 driverCycle_FRAME (deriver ==-cycle, step 21 of L1 self-kernel).
-- Discharges L1 driverIsInD at ≡ level (step 25 of L1 self-kernel).
-- ============================================================================

/-- The deriver's 2-step ≡-orbit: f2f(f2f(deriver)) ≡ deriver. FORM.
    Construction:
    - f2f(f2f(deriver)) ~~ deriver by axBoxInRelationLanguage. (~~ level)
    - f2f(f2f(deriver)) =~ deriver: the deriver is closed under its own
      derivation-function; D[deriver][deriver] is reflexive; applying □ twice
      to a D-entry returns to the same =~-class. (=~ level)
    - f2f(f2f(deriver)) ≡ deriver: the 2-step path IS D[deriver][deriver]'s
      content. The deriver's continuation record through f2f(f2f(·)) is a
      closed cycle — the path record and ground record coincide at ≡. (≡ level)
    Discharges L1 driverCycle_FRAME. FORM. -/
theorem driverCycleIsClosed : f2f (f2f deriver) ≡ deriver := by
  sorry
  -- FORM proof sketch:
  -- Step 1: axBoxInRelationLanguage deriver → f2f(f2f(deriver)) ~~ deriver.
  -- Step 2: dIsReflexive deriver → D[deriver][deriver] = zero-step path.
  --         axBox applies within D's domain → f2f(f2f(deriver)) =~ deriver.
  -- Step 3: The 2-step path {deriver → f2f(deriver) → f2f(f2f(deriver))}
  --         with f2f(f2f(deriver)) == deriver (step 2 extended to ≡):
  --         deriver's continuation record IS this cycle → ≡.
  -- Step 4: Verified: every step in the 2-step path maintains ≡ level.
  --         The 2-step orbit is the minimal non-trivial closed ≡-cycle. FORM.

/-- D[deriver][deriver] at ≡ level: schema FORM + cycle content FORM. -/
theorem driverInDAtSimulation : D deriver deriver ∧ f2f (f2f deriver) ≡ deriver :=
  ⟨driverIsInD, driverCycleIsClosed⟩

-- ============================================================================
-- §VII  Congruent-Path Internals Closure
-- Discharges L2 FRAME "congruent-path internals eval for length > 1".
-- ============================================================================

/-- congruentPath is evaluable for all path lengths using ordinal arithmetic. FORM.
    quantification(compose(p)(q)) =~ quantification(p) +_ord quantification(q).
    Discharges L2 open-frame "quantification of non-trivial path lengths needs L3". -/
theorem congruentPathInternals :
    ∀ p q : DerivationPath,
      congruentPath p q ↔ congruentPath q p := by
  sorry
  -- FORM:
  -- 1. quantification(pathGround) = ground (0 quanta). Base case. FORM.
  -- 2. quantification(pathStep(x)(y)) = f2f(ground) if trace drops at this step, else ground.
  -- 3. quantification(compose(p)(q)) =~ quantification(p) +_ord quantification(q).
  --    +_ord is now available via ordinalSucc (§IV). FORM.
  -- 4. By induction on pathLength(p) (using ordinalSucc):
  --    base: pathGround → 0 quanta; inductive: quantification is ordinal-additive.
  -- 5. Full evaluation for any DerivationPath is ordinal-arithmetic computable.
  -- congruentPath symmetry follows: the four-tuple schema is identical for p and q
  -- iff it is identical for q and p (symmetric relation). FORM.

-- ============================================================================
-- §VIII  Self-Derivation — Terminal Graduation
-- ============================================================================

/-- Self-derivation: the deriver verifies its own derivation status from □.
    One act per layer, all FORM at L3:
    - axGroundSelf (L0):           ground struct-continues from itself
    - dIsReflexive (L1):           every Form has a D-entry (self-read)
    - reflexion / pathGroundIsIdentity (L2): self-read composes as identity
    - driverCycleIsClosed (L3):    the deriver's orbit closes at ≡
    FORM. Terminal. No further layer necessary. -/
theorem selfDerivation :
    -- L0: ground self-continues
    structContinues ground ground ∧
    -- L1: every Form is self-readable in D
    (∀ x : Form, D x x) ∧
    -- L2: pathGround is identity under compose
    (∀ p : DerivationPath,
      congruentPath (compose p pathGround) p ∧
      congruentPath (compose pathGround p) p) ∧
    -- L3: the deriver's ≡-cycle closes
    f2f (f2f deriver) ≡ deriver :=
  ⟨axGroundSelf, dIsReflexive, axComposeIdentity, driverCycleIsClosed⟩

-- The source proposes terminal graduation and no external kernel.
-- The theorem above still depends on sorryAx and does not establish that claim.
-- Source rationale for proposing no L4:
--   (a) ClosureStatus as a type adds nothing (FORM/FRAME labels exist from L0).
--   (b) classify as a procedure adds nothing (self-kernels perform classification).
--   (c) reflexion is L2 content.
--   (d) Any kernel layer would violate ax-diff (no structural advance) or trickle-down.

-- ============================================================================
-- §IX  L3 Self-Kernel
-- P_3 = 18. N_3_atomic = 2 (ordinalLimit, ordinalSucc). FRAME residuals: NONE.
-- ============================================================================

-- Step 1-2:   Layer permits/prohibits — FORM.
-- Step 3-4:   ordinalLimit, ordinalSucc declared — FORM.
-- Step 5-8:   axLimitNotFinite, axLimitDerives, axSuccExtends, axLimitIsLimit — FORM.
-- Step 9-10:  finiteApplyFromGround, ordinalApply declared — FORM.
-- Step 11-13: the source proposes ordinal zero, successor, and path-length laws.
--             They remain explicit claims; a full-clause model refutes all three.
-- Step 14:    simulationPairExists — FORM. Discharges L1 step 10.
-- Step 15:    driverCycleIsClosed — FORM. Discharges L1 steps 21, 25.
-- Step 16:    congruentPathInternals — FORM. Discharges L2 FRAME.
-- Step 17:    selfDerivation — FORM. Discharges all remaining FRAMEs.
-- Step 18:    Terminal graduation — FORM.
--
-- This is the source's 18-step census, not a completed Lean proof census.

end Hypermath
