-- Hypermath.L3Ordinatics
-- Layer 3: Ordinatics — proposed terminal layer
-- Lean4 mechanization scaffold for L3_ordinatics.hm
--
-- Introduces: finiteApplyFromGround, and the L3 consequences of the deriver's
-- declared ordinal position.
--
-- The transfinite declarations themselves — ordinalLimit, ordinalSucc,
-- ordinalApply, and the four laws constraining them — are no longer stated
-- here. They live in the ordinatics repository as `Ordinatics.Transfinite`,
-- and this layer assumes one instance of that interface (§II). Every name and
-- type this file previously exported is recovered unchanged.
--
-- Finite closure and witnessed-length observations are constructive.
-- The source's terminal-closure claims still include admitted proof obligations.
--
-- P_3 = 21.  N_3_atomic = 2 (ordinalLimit, ordinalSucc).
-- FORM/FRAME comments below retain source classifications, not proof verdicts.
-- Source: L3_ordinatics.hm

import Hypermath.L2Operations
import Ordinatics

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
-- §II  Transfinite Declarations — Instantiated from Ordinatics
-- Two atomic Forms at L3, plus ordinal application. Definition-acts. FORM.
-- ============================================================================

/-- **Hypermath's entire transfinite commitment, as one named interface.**

    `Ordinatics.Transfinite` collects the ordinal limit, the ordinal successor,
    ordinal application, the four laws constraining them, and the position the
    deriver occupies. Hypermath supplies its own substrate — `ground`, `f2f`,
    the four relations, `DerivationPath` and its endpoints — and assumes one
    instance over it.

    This replaces the seven axioms this section used to carry (`ordinalLimit`,
    `ordinalSucc`, `ordinalApply`, `axLimitNotFinite`, `axLimitDerives`,
    `axSuccExtends`, `axLimitIsLimit`). Their content is unchanged: each is
    recovered below with its previous name and type, as a projection. What
    changed is ownership. The transfinite declarations belong to the repository
    that owns ordinal structure for this family; hypermath states where it
    stands relative to them instead of restating them.

    **What this assumption is and is not known to be.** Ordinatics exhibits two
    models: `TwoChainModel.transfinite_is_satisfiable`, and
    `ReachableLimitModel.transfinite_is_satisfiable_nonvacuously`, where the
    least-upper-bound clause has a satisfiable antecedent and so has to be proved
    rather than discharged vacuously. Both are built over `Nat × Bool`. They
    establish that the interface is satisfiable, so assuming it is not assuming
    something empty.

    They do **not** establish that *this* substrate admits an instance. That
    would need a model of hypermath's own `Form`, `f2f`, relations and
    `DerivationPath` satisfying these clauses alongside everything else hypermath
    assumes, and no such model exists in either repository. This axiom is a
    genuine assumption about this substrate, and the audit reports it as one.

    `Ordinatics.TwoChainModel.deriver_position_not_derivable` establishes the
    other half of the design's claim: the four laws are satisfiable with a
    different Form named as deriver, so `deriverAtLimit` is independent of them.
    The position is declared, not derived. See §VIII.a and L3_ordinatics.hm:143. -/
axiom ordinatics :
    Ordinatics.Transfinite (Form := Form) (Path := DerivationPath)
      ground f2f Similar Congruent Simulation Derives pathStart pathEnd deriver

/-- The first Form unreachable by any finite f2f-chain from ground.
    The Form naming the end of the finite apply-chain sequence.
    ordinalLimit is not f2f^n(ground) for any finite n (axLimitNotFinite). -/
noncomputable def ordinalLimit : Form := ordinatics.limit

/-- ordinalSucc(x): the Form one step beyond x in the ordinal ordering.
    For finite ordinals: ordinalSucc(f2f^n(ground)) ~ f2f^{n+1}(ground).
    For ordinalLimit: ordinalSucc(ordinalLimit) is a Form beyond ordinalLimit.
    Structural: ordinalSucc(x) ~~ f2f(x) at ~~. ordinalSucc(x) =~ x + f2f(ground) at =~. -/
noncomputable def ordinalSucc : Form → Form := ordinatics.succ

/-- ordinalApply(p)(x): apply p to x in the ordinal sense.

    The three readings the source intends --- ordinalApply(ground)(x) =~ x,
    ordinalApply(f2f(ground))(x) =~ f2f(x), and ordinalApply(ordinalLimit)(x) as
    a limit ordinal Form built from x --- are **intentions and not consequences**.
    The interface declares no clause of any kind for `apply`, not merely no
    computation clause: `Ordinatics.Transfinite.apply_is_free` proves that every
    function whatever is the application of some instance with this limit and
    this successor. None of hypermath's own 39 clauses mentions it either. That
    is why the three proposed action laws in §IV are named propositions, and
    `ordinalApplyUnconstrained` below is the reason rather than the symptom. -/
noncomputable def ordinalApply : Form → Form → Form := ordinatics.apply

-- ============================================================================
-- §III  Axioms for Ordinal Structure
-- Each is now a projection from the ordinatics interface, stated with exactly
-- the type it previously carried as a hypermath axiom. Downstream proofs are
-- unaffected; `#print axioms` on them now names `Hypermath.ordinatics`.
-- ============================================================================

/-- **ax-limit-not-finite**: ordinalLimit is not reachable by any finite f2f-chain. -/
theorem axLimitNotFinite : ∀ n : Nat, ¬ (Nat.repeat f2f n ground ≡ ordinalLimit) :=
  ordinatics.limitNotFinite

/-- **ax-limit-derives**: the limit-path from ground exists; its end =~ ordinalLimit.
    The infinite composition of finite continuation paths reaches ordinalLimit. -/
theorem axLimitDerives :
    ∃ limitPath : DerivationPath,
      (pathStart limitPath ~~ ground) ∧
      (pathEnd limitPath =~ ordinalLimit) :=
  ordinatics.limitDerives

/-- **ax-succ-extends**: ordinalSucc strictly extends every Form. -/
theorem axSuccExtends :
    ∀ x : Form,
      Derives x (ordinalSucc x) ∧ ¬ (ordinalSucc x ≡ x) :=
  ordinatics.succExtends

/-- **ax-limit-is-limit**: ordinalLimit is the least upper bound of all finite ordinals.
    For all finite n: Derives(f2f^n(ground), y) for any upper bound y → Derives(ordinalLimit, y). -/
theorem axLimitIsLimit :
    ∀ y : Form,
      (∀ n : Nat, Derives (Nat.repeat f2f n ground) y) →
      Derives ordinalLimit y :=
  ordinatics.limitIsLimit

/-- **The declared position of the deriver.**

    L1 declares `deriver` as a Form and says nothing about where it sits. That
    silence is what left every deriver question open: the finite-position
    obstructions of §VIII applied or not depending on an undeclared fact. The
    ordinatics interface carries the declaration, and this is it.

    It is a declaration, not a derivation. Nothing in L0–L2 determines the
    deriver's position, and the choice is consequential in both directions —
    §VIII.a below records exactly what it buys and what it costs.

    That is proved, not merely asserted. The four laws beside this clause never
    mention the deriver, and
    `Ordinatics.TwoChainModel.deriver_position_not_derivable` exhibits one
    substrate where they hold, the structure is inhabited with the deriver at the
    limit, and it is not inhabited with the deriver at ground. Laws indifferent
    between two namings admit no derivation of either. -/
theorem axDeriverAtLimit : deriver = ordinalLimit := ordinatics.deriverAtLimit

-- ============================================================================
-- §IV  Ordinal Arithmetic
-- ============================================================================

/-- The native Form at finite apply-position n, as in L3_ordinatics.hm:208–212.
    This observes the existing ground/f2f parameters, not a tagged substitute
    for Form. Distinct n are not asserted to produce distinct Forms. -/
noncomputable def finiteApplyPosition (n : Nat) : Form := Nat.repeat f2f n ground

/-- The least finite f2f-closure of ground specified in L3_ordinatics.hm:168–173.
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

/-- **Nothing constrains `ordinalApply`, at either level.**

    `ordinalApply` is `ordinatics.apply`, and no law of `Ordinatics.Transfinite`
    mentions that field, so the assumption this layer makes is compatible with
    every reading of it: for any `g` whatever there is an instance of the same
    interface, over this same substrate, with this limit and this successor and
    `g` for its application. Nothing that follows from `ordinatics` can therefore
    say anything about `ordinalApply` alone.

    Nor does anything else. `ordinalApply` is a definition rather than a source
    parameter, and none of the 39 logical clauses mentions it;
    `tests/test_declared_counts.py` pins that.

    So the three propositions below were not reachable from the start. That is a
    stronger statement than the refutations they carry, and a cheaper one: a
    refutation says one construction defeats the claim, this says no construction
    was needed to know it would. `pathLengthArithmeticClaim` is the sharpest
    case, since `pathLength` is also mentioned by no clause. Deriving any of the
    three requires **declaring** a clause for the application, which is what the
    ordinatics field docstring means by a theory supplying one itself. -/
theorem ordinalApplyUnconstrained (g : Form → Form → Form) :
    ∃ T : Ordinatics.Transfinite (Form := Form) (Path := DerivationPath)
        ground f2f Similar Congruent Simulation Derives pathStart pathEnd deriver,
      T.apply = g ∧ T.limit = ordinalLimit ∧ T.succ = ordinalSucc :=
  ordinatics.apply_is_free g

/-- The source's proposed zero-action law. It remains a named proposition, and
    `ordinalApplyUnconstrained` is why: `ordinalApply` has no declared clause of
    any kind, so no reading of it is ruled out and none is forced. -/
def ordinalZeroIdentityClaim : Prop :=
  ∀ x : Form, ordinalApply ground x =~ x

/-- The source's proposed successor-action law. The current clauses do not
    connect ordinalSucc and ordinalApply weakly either: by
    `ordinalApplyUnconstrained` the successor can be held fixed while the
    application is replaced by anything at all, so no clause relates them. -/
def ordinalSuccAppliesClaim : Prop :=
  ∀ p x : Form,
    ordinalApply (ordinalSucc p) x =~ f2f (ordinalApply p x)

/-- The source's proposed path-length arithmetic law, including its operand order.
    A checked full-clause model refutes this proposition, so it cannot discharge
    the L2 FRAME without an additional bridge --- and the model was not needed.
    Both symbols it names are unconstrained: no clause mentions `pathLength`
    (`tests/test_declared_counts.py`) and neither clause nor law mentions
    `ordinalApply` (`ordinalApplyUnconstrained`). A bridge here means a declared
    clause, not a sharper proof. -/
def pathLengthArithmeticClaim : Prop :=
  ∀ p q : DerivationPath,
    pathLength (compose p q) =~ ordinalApply (pathLength q) (pathLength p)

-- ============================================================================
-- §V  Nontrivial Simulation-Pair Obligation
-- The stronger pair claim does not follow from the current clauses.
-- The separate weak L1 existence claim remains admitted.
-- ============================================================================

/-- The proposed nontrivial simulation pair, with its original statement.
    FullAxiomModel interprets Simulation as equality and refutes this claim
    while satisfying all 44 clauses. The admitted theorem is withdrawn;
    neither the limit clauses nor similarity imply this stronger relation. -/
def simulationPairExistsClaim : Prop :=
  ∃ x y : Form, (x ~~ y) ∧ (x ≡ y) ∧ ¬ (x = y)

-- ============================================================================
-- §VI  Deriver ≡-Cycle Obligation
-- ============================================================================

/-- Adding the cycle as an explicit hypothesis supplies the second conjunct.
    This conditional theorem does not prove driverCycleClaim. -/
theorem driverInDAtSimulationOfCycle (cycle : driverCycleClaim) :
    D deriver deriver ∧ f2f (f2f deriver) ≡ deriver :=
  ⟨driverIsInD, cycle⟩

-- ============================================================================
-- §VII  Congruent-Path Internals Closure
-- Discharges L2 FRAME "congruent-path internals eval for length > 1".
-- ============================================================================

/-- `congruentPath` is symmetric. FORM, by `axCongruentPathSymm` (L2 §II). -/
theorem congruentPathInternals :
    ∀ p q : DerivationPath,
      congruentPath p q ↔ congruentPath q p :=
  fun p q => ⟨axCongruentPathSymm p q, axCongruentPathSymm q p⟩

-- ============================================================================
-- §VIII  Self-Derivation Target and Its Remaining Cycle Obligation
-- ============================================================================

/-- The original closed self-derivation target, retained without weakening.
    This declaration names a proposition; it is not a proof of that proposition.
    The first three conjuncts follow from the reviewed clauses. The fourth
    fails in FullAxiomModel, so those clauses do not entail the whole target. -/
def selfDerivation : Prop :=
    -- L0: ground self-continues
    structContinues ground ground ∧
    -- L1: every Form is self-readable in D
    (∀ x : Form, D x x) ∧
    -- L2: pathGround is identity under compose
    (∀ p : DerivationPath,
      congruentPath (compose p pathGround) p ∧
      congruentPath (compose pathGround p) p) ∧
    -- L3: the deriver's ≡-cycle closes
    f2f (f2f deriver) ≡ deriver

/-- Conditional assembly of the original target. The cycle is a premise,
    not a newly introduced native axiom or an established conclusion. -/
theorem selfDerivationOfCycle (cycle : driverCycleClaim) : selfDerivation :=
  ⟨axGroundSelf, dIsReflexive, axComposeIdentity, cycle⟩

/-- Exactly the cycle remains after the other three conjuncts are discharged.
    This equivalence is not a closed proof of either side. -/
theorem selfDerivation_iff_driverCycleClaim : selfDerivation ↔ driverCycleClaim :=
  ⟨fun target => target.2.2.2, selfDerivationOfCycle⟩

-- Explicit source-cycle certificates and the finite-successor boundary.

/-- A native apply edge retaining simulation at that edge, not only its endpoints
after two applications. Its source requirement is L1 section VII. -/
def SimulationStep (x y : Form) : Prop := y = f2f x ∧ Simulation y x

abbrev SimulationEntry (x y : Form) := Trace SimulationStep x y

def simulationEntryToDEntry {x y : Form} (path : SimulationEntry x y) : DEntry x y :=
  Trace.map id (fun {a b} edge => ⟨edge.1, filtrationSimCong b a edge.2⟩) path

theorem simulationEntryToDEntry_length {x y : Form} (path : SimulationEntry x y) :
    Trace.length (simulationEntryToDEntry path) = Trace.length path :=
  Trace.length_map id (fun {a b} edge => ⟨edge.1, filtrationSimCong b a edge.2⟩) path

/-- This typed certificate retains the two actual edges and endpoint closure.
It is stronger than the original selfDerivation proposition; no inhabitant is
postulated. The equality below counts edges, not ordinal or semantic value.

`selfDerivationOfWitness` sends this to the target. The converse fails:
`HypermathTargetAtLimitModel.target_does_not_yield_a_cycle_certificate` is a
model of all 44 clauses in which the target and `driverCycleClaim` both hold and
this structure has no inhabitant, so "stronger" is a separation there rather
than a reading of the definitions. -/
structure DriverCycleWitness where
  path : SimulationEntry deriver (f2f (f2f deriver))
  length_two : Trace.length path = 2
  closes : driverCycleClaim

noncomputable def driverCycleWitnessOfSteps
    (first : Simulation (f2f deriver) deriver)
    (second : Simulation (f2f (f2f deriver)) (f2f deriver))
    (closes : driverCycleClaim) : DriverCycleWitness :=
  ⟨Trace.cons ⟨rfl, first⟩ (Trace.cons ⟨rfl, second⟩ (Trace.nil _)), rfl, closes⟩

theorem driverCycleWitness_exists_of_steps
    (first : Simulation (f2f deriver) deriver)
    (second : Simulation (f2f (f2f deriver)) (f2f deriver))
    (closes : driverCycleClaim) : Nonempty DriverCycleWitness :=
  ⟨driverCycleWitnessOfSteps first second closes⟩

theorem selfDerivationOfWitness (witness : DriverCycleWitness) : selfDerivation :=
  selfDerivationOfCycle witness.closes

theorem witness_has_two_D_steps (witness : DriverCycleWitness) :
    ∃ path : DEntry deriver (f2f (f2f deriver)), Trace.length path = 2 :=
  ⟨simulationEntryToDEntry witness.path,
   (simulationEntryToDEntry_length witness.path).trans witness.length_two⟩

/-- The exact finite successor equation stated in L3 section II. This is an
explicit proposed correspondence law, not an extra native axiom. -/
def FiniteSuccessorAgreement : Prop :=
  ∀ n : Nat, ordinalSucc (finiteApplyPosition n) = finiteApplyPosition (n + 1)

theorem no_simulation_step_at_finite_of_successor_agreement
    (agreement : FiniteSuccessorAgreement) {x : Form} (finite : finiteApplyFromGround x) :
    ¬ Simulation (f2f x) x := by
  obtain ⟨n, rfl⟩ := finite
  have agreement_at : ordinalSucc (finiteApplyPosition n) = f2f (finiteApplyPosition n) :=
    agreement n
  rw [← agreement_at]
  exact (axSuccExtends (finiteApplyPosition n)).2

theorem simulation_trace_from_finite_is_empty
    (agreement : FiniteSuccessorAgreement) {x y : Form}
    (finite : finiteApplyFromGround x) (path : SimulationEntry x y) :
    Trace.length path = 0 := by
  cases path with
  | nil => rfl
  | cons edge tail =>
      have step : Simulation (f2f x) x := edge.1 ▸ edge.2
      exact False.elim (no_simulation_step_at_finite_of_successor_agreement agreement finite step)

theorem no_driver_cycle_witness_at_finite_successor
    (agreement : FiniteSuccessorAgreement) (finite : finiteApplyFromGround deriver) :
    ¬ Nonempty DriverCycleWitness := by
  rintro ⟨witness⟩
  have zero := simulation_trace_from_finite_is_empty agreement finite witness.path
  have impossible : (2 : Nat) = 0 := witness.length_two.symm.trans zero
  exact Nat.noConfusion impossible

/-- The same proposed correspondence, without its finiteness restriction: apply
*is* the ordinal successor at every Form, not only at positions reached from
ground. Like `FiniteSuccessorAgreement` this is a proposed law and not a clause.

The restriction is what the declared deriver position evades. `deriverNotFinite`
denies the hypothesis of `no_driver_cycle_witness_at_finite_successor`, so that
obstruction has no instance; this one asks nothing about where the deriver sits
and applies at the limit exactly as it does at ground. -/
def SuccessorAgreement : Prop := ∀ x : Form, ordinalSucc x = f2f x

theorem no_simulation_step_of_successor_agreement
    (agreement : SuccessorAgreement) (x : Form) : ¬ Simulation (f2f x) x := by
  rw [← agreement x]
  exact (axSuccExtends x).2

theorem simulation_entry_is_empty_of_successor_agreement
    (agreement : SuccessorAgreement) {x y : Form} (path : SimulationEntry x y) :
    Trace.length path = 0 := by
  cases path with
  | nil => rfl
  | cons edge tail =>
      have step : Simulation (f2f x) x := edge.1 ▸ edge.2
      exact False.elim (no_simulation_step_of_successor_agreement agreement x step)

/-- **Declaring the deriver at the limit does not evade this one.** If apply is
the successor everywhere then `axSuccExtends` forbids every simulation edge, so
no path retains one and the certificate cannot be built at any position. The
cycle and this law are therefore incompatible, and both are consistent with the
39 clauses --- `HypermathTargetAtLimitModel` satisfies them with
`ordinalSucc = f2f` and no certificate,
`HypermathTransportCountermodel` satisfies them with a successor that is not
apply and an inhabited certificate. So the open question about the cycle is the
question of what apply means, which is a source question rather than one the
clauses can settle. -/
theorem no_driver_cycle_witness_of_successor_agreement
    (agreement : SuccessorAgreement) : ¬ Nonempty DriverCycleWitness := by
  rintro ⟨witness⟩
  have zero := simulation_entry_is_empty_of_successor_agreement agreement witness.path
  exact Nat.noConfusion (witness.length_two.symm.trans zero)

/-- A two-edge simulation path reads back completely: the far endpoint is forced
and both retained edges are recovered. `Trace` carries nothing else, which is
what lets the certificate below reduce to propositions about `Simulation`. -/
theorem simulationEntry_two {x y : Form} (path : SimulationEntry x y)
    (two : Trace.length path = 2) :
    y = f2f (f2f x) ∧ Simulation (f2f x) x ∧ Simulation (f2f (f2f x)) (f2f x) := by
  obtain ⟨_, edge, tail, one⟩ := Trace.uncons_of_length_succ path two
  obtain ⟨rfl, first⟩ := edge
  obtain ⟨_, secondEdge, rest, zero⟩ := Trace.uncons_of_length_succ tail one
  obtain ⟨rfl, second⟩ := secondEdge
  exact ⟨(Trace.eq_of_length_zero rest zero).symm, first, second⟩

/-- **The certificate is exactly three simulation facts at the deriver.** The
structure bundles a trace, a length and a closure, and the trace and the length
together say no more than that both apply edges at the deriver retain
simulation. `driverCycleWitnessOfSteps` was already the right-to-left half; the
other half is what was missing, and without it "the certificate is stronger than
the target" could only be argued by pointing at the fields.

The third conjunct is `driverCycleClaim`, which is the whole of the target by
`selfDerivation_iff_driverCycleClaim`. So the gap between the target and the
certificate is precisely the first two conjuncts: the retained edges. -/
theorem driverCycleWitness_iff :
    Nonempty DriverCycleWitness ↔
      (Simulation (f2f deriver) deriver ∧
        Simulation (f2f (f2f deriver)) (f2f deriver) ∧ driverCycleClaim) := by
  constructor
  · rintro ⟨witness⟩
    obtain ⟨_, first, second⟩ := simulationEntry_two witness.path witness.length_two
    exact ⟨first, second, witness.closes⟩
  · rintro ⟨first, second, closes⟩
    exact driverCycleWitness_exists_of_steps first second closes

/-- Transitivity of `Simulation`, as an explicit hypothesis. No clause asserts
it: `Simulation` is a declared parameter and the clauses naming it relate it to
other relations -- distinctness, the two filtration steps, semantics opacity and
the `ordinatics` interface -- never to itself. -/
def SimulationTransitive : Prop :=
  ∀ x y z : Form, Simulation x y → Simulation y z → Simulation x z

theorem driverCycleClaim_of_steps (transitive : SimulationTransitive)
    (first : Simulation (f2f deriver) deriver)
    (second : Simulation (f2f (f2f deriver)) (f2f deriver)) : driverCycleClaim :=
  transitive _ _ _ second first

/-- **Given transitivity the closure is free, so the certificate is exactly the
two retained edges.** The endpoint claim the target asks for is then a
consequence of the edges rather than an additional demand, which locates the
separation precisely: what a proof of the target leaves to be supplied is the
edges, and never the closure. Both models of the independence result satisfy
transitivity -- `HypermathTargetAtLimitModel.simulation_is_transitive` and the
transport countermodel's `simulation_is_equivalence` -- so adding it to the 39
clauses would not decide the certificate either. -/
theorem driverCycleWitness_iff_of_transitive (transitive : SimulationTransitive) :
    Nonempty DriverCycleWitness ↔
      (Simulation (f2f deriver) deriver ∧
        Simulation (f2f (f2f deriver)) (f2f deriver)) :=
  driverCycleWitness_iff.trans
    ⟨fun steps => ⟨steps.1, steps.2.1⟩,
     fun steps => ⟨steps.1, steps.2, driverCycleClaim_of_steps transitive steps.1 steps.2⟩⟩

/-- **A fixed point makes the certificate free.** If apply leaves the deriver
where it is then both retained edges and the closure are instances of
reflexivity of `Simulation` at the deriver, so nothing about a cycle is being
witnessed. Reflexivity there is itself not a clause --- no clause asserts
`Simulation deriver deriver` --- which is why it appears as a hypothesis.

This is not idle: `HypermathTransportCountermodel`, the development's only
inhabited certificate for most of its life, has `f2f deriver = deriver`.
`HypermathNondegenerateCycleModel` is the model whose cycle actually moves. -/
theorem driverCycleWitness_of_fixed_deriver (fixed : f2f deriver = deriver)
    (reflexive : Simulation deriver deriver) : Nonempty DriverCycleWitness := by
  refine driverCycleWitness_iff.mpr ⟨?_, ?_, ?_⟩
  · simpa [fixed] using reflexive
  · simpa [fixed] using reflexive
  · show Simulation (f2f (f2f deriver)) deriver
    simpa [fixed] using reflexive

-- ----------------------------------------------------------------------------
-- §VIII.a  Consequences of the declared deriver position
--
-- `axDeriverAtLimit` (§III) places the deriver at ordinalLimit. Everything
-- below follows from that one declaration together with clauses already
-- present. Read together they say what the choice buys and what it costs.
-- ----------------------------------------------------------------------------

/-- No finite apply-position simulates the deriver. The deriver is outside the
    finite tower, not merely far along it. -/
theorem noFinitePositionSimulatesDeriver (n : Nat) :
    ¬ (finiteApplyPosition n ≡ deriver) := by
  rw [axDeriverAtLimit]
  exact axLimitNotFinite n

/-- In particular the deriver is not simulated by ground. Under a finite
    reading this was not available: ground is at position 0 of the tower. -/
theorem groundDoesNotSimulateDeriver : ¬ (ground ≡ deriver) :=
  noFinitePositionSimulatesDeriver 0

/-- **What the declaration buys.** The deriver is not finitely reachable from
    ground, so the hypothesis of `no_driver_cycle_witness_at_finite_successor`
    is refuted and that obstruction cannot be applied to it. -/
theorem deriverNotFinite : ¬ finiteApplyFromGround deriver := by
  rw [axDeriverAtLimit]
  exact finiteApplyLimitExcluded

/-- The obstruction has no instance at the deriver, whatever the successor
    agreement. This removes a blocker; it does not supply a witness. The cycle
    is still neither proved nor refuted, and by
    `selfDerivation_iff_driverCycleClaim` neither is self-derivation. -/
theorem noFiniteObstructionAtDeriver :
    ¬ ∃ _agreement : FiniteSuccessorAgreement, finiteApplyFromGround deriver :=
  fun ⟨_, finite⟩ => deriverNotFinite finite

/-- **What the declaration costs.** The finite derivation matrix does not reach
    the deriver from ground. Ground-closure at the deriver position cannot be
    read as D-reachability. -/
theorem deriverNotInD : ¬ D ground deriver := by
  rw [axDeriverAtLimit]
  exact ordinalLimitNotInD

/-- **What replaces it.** A DerivationPath still runs from ground to the
    deriver. Closure at the deriver position holds through L2's path language,
    where the limit clause states it, not through L1's finite matrix. -/
theorem deriverReachedByLimitPath :
    ∃ limitPath : DerivationPath,
      (pathStart limitPath ~~ ground) ∧ (pathEnd limitPath =~ deriver) := by
  rw [axDeriverAtLimit]
  exact axLimitDerives

/-- The deriver derives everything every finite stage derives. It is the least
    upper bound of the finite tower, which is the sense in which a deriver that
    runs the whole tower sits above it. -/
theorem deriverIsLeastUpperBound (y : Form)
    (bound : ∀ n : Nat, Derives (finiteApplyPosition n) y) : Derives deriver y := by
  rw [axDeriverAtLimit]
  exact axLimitIsLimit y bound

/-- The deriver is not the top either: its successor continues from it and
    differs from it. The declaration fixes a position, not a terminus. -/
theorem deriverExtends :
    Derives deriver (ordinalSucc deriver) ∧ ¬ (ordinalSucc deriver ≡ deriver) :=
  axSuccExtends deriver


-- The source proposes terminal graduation and no external kernel.
-- The target above is unproved and does not establish that claim.
-- Source rationale for proposing no L4:
--   (a) ClosureStatus as a type adds nothing (FORM/FRAME labels exist from L0).
--   (b) classify as a procedure adds nothing (self-kernels perform classification).
--   (c) reflexion is L2 content.
--   (d) Any kernel layer would violate ax-diff (no structural advance) or trickle-down.

-- ============================================================================
-- §IX  L3 Self-Kernel
-- P_3 = 21. N_3_atomic = 2 (ordinalLimit, ordinalSucc). FRAME residuals: see CORRECTIONS in L3_ordinatics.hm.
-- ============================================================================

-- Step 1-2:   Layer permits/prohibits — FORM.
-- Step 3-4:   ordinalLimit, ordinalSucc declared — FORM.
-- Step 5-8:   axLimitNotFinite, axLimitDerives, axSuccExtends, axLimitIsLimit — FORM.
-- Step 9:     axDeriverAtLimit — the declared deriver position. FORM.
--             Steps 3-9 are projections of the one assumed `ordinatics`
--             interface, not seven independent assumptions.
-- Step 10-11: finiteApplyFromGround, ordinalApply declared — FORM.
-- Step 12-14: the source proposes ordinal zero, successor, and path-length laws.
--             They remain explicit claims; a full-clause model refutes all three.
-- Step 15:    simulationPairExists. There is no such theorem in this layer. It
--             was withdrawn when a full-clause model refuted the nontrivial
--             pair, and survives as the unproved `simulationPairExistsClaim`
--             (§V). L1 step 10 does not need it: the weak pair is proved
--             outright at `Hypermath.simulationPairExists_L1`, from the ground
--             semantics clause alone.
-- Step 16:    driverCycleIsClosed. There is no such theorem, here or anywhere.
--             The layer carries `driverCycleClaim` and the conditional
--             `driverInDAtSimulationOfCycle`, which assumes it. Both
--             `HypermathCountermodel.driver_cycle_claim_fails` and
--             `HypermathFullAxiomModel.driver_cycle_claim_fails` refute it, so
--             L1 steps 21 and 25 stay open.
-- Step 17:    congruentPathInternals — admitted, and independent of every
--             declared clause. `HypermathFullAxiomModel.`
--             `congruentPath_symmetry_independent` gives one structure with two
--             readings of `congruentPath`, both satisfying all 44 clauses, one
--             symmetric and one not. The L2 frame it was supposed to close
--             cannot be closed by any layer.
-- Step 18:    selfDerivation — a named proposition, not a proof. Its fourth
--             conjunct is step 16, and `selfDerivation_iff_driverCycleClaim`
--             shows the target reduces to exactly that. It discharges nothing.
-- Step 19:    deriverPositionConsequences (§VIII.a) — what step 9 buys, costs
--             and replaces. Opens no FRAME and discharges none.
-- Step 20:    Terminal graduation — FORM.
--
-- This is the source's 20-step census, not a completed Lean proof census.

end Hypermath
