-- Hypermath.L0Ground
-- Layer 0: Ground
-- Lean4 mechanization scaffold for L0_ground.hm
--
-- Translation notes:
--   `apply`  → `f2f`  (form-to-form): avoids conflict with Lean4's `apply` tactic
--   `Prop`   is Lean4's built-in sort; no separate declaration needed
--   `==` (simulation) → notation `≡` to avoid conflict with Lean4's BEq
--   FORM derives:  `theorem … := by sorry`  — mechanical proofs pending
--   FRAME items:   `theorem … := by sorry`  + `-- FRAME/LN` comment
--   Axioms of the system: `axiom`
--   Uninterpreted source primitives: `axiom` (parameters, not proved laws).
-- Lean `opaque` without a body requests an Inhabited default; it does not
-- declare an abstract parameter. Source FORM labels are not proof completion:
-- declarations containing `sorry` remain admitted proof obligations.
--
-- P_0 = 45.  N_0_atomic = 4.  G_0 (NCs for graduation) = 4.
-- Source: L0_ground.hm

namespace Hypermath

-- ============================================================================
-- §I  Primitives
-- Four atomic declarations. All definition-acts. FORM.
-- ============================================================================

/-- The base type. Every entity in hypermath is a Form. -/
axiom Form : Type

-- Note: Prop is Lean4's built-in `Prop : Sort 0`.
-- The .hm `primitive Prop :: Type` is represented by Lean's built-in Prop.
-- This is an unproved translation choice: adequacy with the source-native
-- discharge semantics remains open.

/-- The irreducible generative base. Written □ in .hm notation. -/
axiom ground : Form

/-- The sole operation. `f2f` (form-to-form) is `apply` in .hm.
    Renamed to avoid conflict with Lean4's `apply` tactic. -/
axiom f2f : Form → Form

-- ============================================================================
-- §II  Opaque Structural Predicates (pre-relational)
-- Three opaques. All closed in §VI. FORM after close.
-- ============================================================================

/-- `structContinues x y`: x was generated from the same base as y.
    Semantic close (§VI): `structContinues x ground ↔ x ~~ ground` -/
axiom structContinues : Form → Form → Prop

/-- `structDistinct x y`: x and y are not mutually simulating.
    Semantic close (§VI): `structDistinct x y ↔ ¬ (x ≡ y)` -/
axiom structDistinct : Form → Form → Prop

/-- `structOrbits x y`: f2f(f2f(y)) is in the structural orbit of x.
    Semantic close (§VI): `structOrbits (f2f (f2f x)) x ↔ f2f (f2f x) ~~ x` -/
axiom structOrbits : Form → Form → Prop

-- ============================================================================
-- §III  Axioms
-- Four axioms. Each cited in at least one §IV derive. FORM.
-- ============================================================================

/-- **ax-diff**: f2f(x) is struct-distinct from ground for every x. -/
axiom axDiff : ∀ x : Form, structDistinct (f2f x) ground

/-- **ax-sim**: f2f(x) struct-continues from ground for every x. -/
axiom axSim : ∀ x : Form, structContinues (f2f x) ground

/-- **ax-box**: f2f(f2f(x)) struct-orbits x for every x. -/
axiom axBox : ∀ x : Form, structOrbits (f2f (f2f x)) x

/-- **ax-ground-self**: ground struct-continues from itself. -/
axiom axGroundSelf : structContinues ground ground

-- ============================================================================
-- §IV  Derives (all FORM)
-- Five derives. All have explicit witnesses or follow directly from axioms.
-- ============================================================================

/-- f2f(ground) is struct-distinct from ground. FORM. -/
theorem applyGroundIsDistinct : structDistinct (f2f ground) ground :=
  axDiff ground

/-- f2f(ground) struct-continues from ground. FORM. -/
theorem applyGroundContinues : structContinues (f2f ground) ground :=
  axSim ground

/-- f2f(f2f(ground)) struct-orbits ground. FORM. -/
theorem doubleApplyGroundOrbits : structOrbits (f2f (f2f ground)) ground :=
  axBox ground

/-- Two struct-distinct Forms both struct-continuing from ground exist.
    Witnesses: f2f(ground) and ground. FORM. -/
theorem twoMembersInClass :
    ∃ x y : Form,
      structDistinct x y ∧ structContinues x ground ∧ structContinues y ground :=
  ⟨f2f ground, ground, applyGroundIsDistinct, applyGroundContinues, axGroundSelf⟩

/-- f2f(f2f(ground)) struct-orbits ground AND struct-continues from ground. FORM. -/
theorem orbitHasReturn :
    structOrbits (f2f (f2f ground)) ground ∧
    structContinues (f2f (f2f ground)) ground :=
  ⟨doubleApplyGroundOrbits, axSim (f2f ground)⟩

-- ============================================================================
-- §V  Relation Declarations
-- Three relations. Declared as opaques here; semantic closes in §VI.
-- ============================================================================

/-- **Similar** (~~): non-empty overlap in continuation capacity.
    The founding relation. Generated structurally from structContinues. -/
axiom Similar : Form → Form → Prop

/-- **Congruent** (=~): full coincidence of continuation capacity.
    Same outcomes; paths discarded. Generated from ~~ by □. -/
axiom Congruent : Form → Form → Prop

/-- **Simulation** (==, written ≡ in Lean4): mutual path reproduction.
    Same outcomes AND same paths. Generated from =~ by □.
    Notation `≡` used to avoid conflict with Lean4's `==` (BEq). -/
axiom Simulation : Form → Form → Prop

-- Notation (scoped to Hypermath namespace)
scoped notation:50 a " ~~ " b => Similar a b
scoped notation:50 a " =~ " b => Congruent a b
scoped notation:50 a " ≡ "  b => Simulation a b

-- ============================================================================
-- §VI  Closing the Opaque Predicates
-- Three closes. Each moves a §II opaque from pre-relational to relational.
-- All FORM.
-- ============================================================================

/-- struct-continues closes to ~~:
    `structContinues x ground ↔ x ~~ ground` -/
axiom closeStructContinues : ∀ x : Form, structContinues x ground ↔ (x ~~ ground)

/-- struct-distinct closes to ¬≡:
    `structDistinct x y ↔ ¬ (x ≡ y)` -/
axiom closeStructDistinct : ∀ x y : Form, structDistinct x y ↔ ¬ (x ≡ y)

/-- struct-orbits closes to ~~:
    `structOrbits (f2f (f2f x)) x ↔ f2f (f2f x) ~~ x` -/
axiom closeStructOrbits : ∀ x : Form, structOrbits (f2f (f2f x)) x ↔ (f2f (f2f x) ~~ x)

-- ============================================================================
-- §VII  Graduation — L0 → L1
-- Four NCs. All discharged. Graduation status: FORM. L1 licensed.
-- ============================================================================

-- NC-1: structDistinct is inhabited.
theorem nc1_L0 : ∃ x y : Form, structDistinct x y :=
  ⟨f2f ground, ground, applyGroundIsDistinct⟩

-- NC-2: Two struct-distinct Forms both continuing from ground.
theorem nc2_L0 :
    ∃ x y : Form,
      structDistinct x y ∧ structContinues x ground ∧ structContinues y ground :=
  twoMembersInClass

-- NC-3: Orbit is closed.
theorem nc3_L0 : ∃ x : Form, structOrbits (f2f (f2f x)) x :=
  ⟨ground, doubleApplyGroundOrbits⟩

-- NC-4: All three structural predicates are inhabited simultaneously.
theorem nc4_L0 :
    (∃ x y : Form, structDistinct x y) ∧
    (∃ x y : Form, structContinues x y) ∧
    (∃ x : Form, structOrbits (f2f (f2f x)) x) :=
  ⟨nc1_L0, ⟨f2f ground, ground, applyGroundContinues⟩, nc3_L0⟩

-- Graduation status: FORM. L1 is fully licensed.

-- ============================================================================
-- §VIII  Executive Framework
-- Seven opaque predicates and seven axioms forming the syntax-substance-
-- semantics triangle. Three derives. FORM (with FRAME/L1 residuals named).
-- ============================================================================

/-- `HMSyntax x`: x has a structural shape inspectable at ~~ level. -/
axiom HMSyntax : Form → Prop

/-- `Substance x`: x carries derivable matter — middle vertex of the triangle. -/
axiom Substance : Form → Prop

/-- `Semantics x`: x carries meaning derived from its Form membership. -/
axiom Semantics : Form → Prop

/-- `Derives x y`: x is in the derivation-approach of y. Directional. -/
axiom Derives : Form → Form → Prop

/-- `Discharge c e`: evidence e satisfies criterion c. -/
axiom Discharge : Form → Form → Prop

/-- `Definition n f`: name n precisely denotes form f. -/
axiom Definition : Form → Form → Prop

/-- `FormClosure x`: the syntax-substance-semantics triangle completes for x. -/
axiom FormClosure : Form → Prop

-- Triangle axioms
axiom axSyntaxRequiresSubstance    : ∀ x : Form, HMSyntax x  → Substance x
axiom axSubstanceRequiresSemantics : ∀ x : Form, Substance x → Semantics x
axiom axSemanticsRequiresSyntax    : ∀ x : Form, Semantics x → HMSyntax x
axiom axFormClosesLoop             : ∀ x : Form, HMSyntax x → Semantics x → FormClosure x
axiom axGroundSyntaxAx             : HMSyntax ground
axiom axGroundSubstanceAx          : Substance ground
axiom axGroundSemanticsAx          : Semantics ground

/-- ground inhabits all three triangle vertices; therefore FormClosure(ground). FORM. -/
theorem groundIsFormClosed : FormClosure ground :=
  axFormClosesLoop ground axGroundSyntaxAx axGroundSemanticsAx

-- ============================================================================
-- §VIII.a  Semantic Closes for the Executive Opaques
-- Steps 25–31. Each close mentions only L0 symbols, so L0 closes what it opens.
-- ============================================================================

/-- syntax closes to orbit-depth at ~~ level. FORM. Step 25. -/
axiom closeSyntaxOpaque :
    ∀ x : Form,
      HMSyntax x ↔
      ∃ n : Nat, Nat.repeat f2f n ground ~~ x

/-- substance closes to =~-equivalence class of x. FORM. Step 26. -/
axiom closeSubstanceOpaque :
    ∀ x : Form, Substance x ↔ (x =~ x)

/-- semantics closes to ≡-equivalence class of x. FORM. Step 27. -/
axiom closeSemanticsOpaque :
    ∀ x : Form, Semantics x ↔ (x ≡ x)

/-- derives(x, y) closes to: ∃ finite n, f2f^n(x) =~ y. FORM. Step 28.

    **Tier: abstraction (`~=`, abstracted from), not congruence (`=~`, congruent
    from).** Each witness lands at `=~`, but the existential discards n, and
    discarding the quanta coordinate is the defining move of `~=`. `derives`
    therefore ranges over `~=`-classes of `DerivesIn` witnesses (L1Relations
    §IV.a). See `QuadrilateralFiltration` §4c. -/
axiom closeDerivesOpaque :
    ∀ x y : Form, Derives x y ↔ ∃ n : Nat, Nat.repeat f2f n x =~ y

/-- discharge(c, e) closes to: Derives e c is FORM. FORM. Step 29. -/
axiom closeDischargeOpaque :
    ∀ c e : Form, Discharge c e ↔ Derives e c

/-- definition(n, x) closes to: Derives n x is FORM. FORM. Step 30. -/
axiom closeDefinitionOpaque :
    ∀ n x : Form, Definition n x ↔ Derives n x

/-- form-closure(x) closes to: syntax ∧ substance ∧ semantics all FORM. FORM. Step 31. -/
axiom closeFormClosureOpaque :
    ∀ x : Form,
      FormClosure x ↔ (HMSyntax x ∧ Substance x ∧ Semantics x)

-- ============================================================================
-- §VIII.b  Closing Clauses
-- Each states, as an assumption, the reading the source already gives the
-- relation, and each is satisfied by `HypermathFullAxiomModel` (see
-- `HypermathFullAxiomModel.closing_clauses_consistent_with_full_axioms`).
-- ============================================================================

/-- **ax-diff-congruent**: forming never lands on ground's substance. ax-diff
    states the distinction at `≡`; this states it at `=~`. The loop returns to
    ground at `~~` and never at `=~`. -/
axiom axDiffCongruent : ∀ x : Form, ¬ (f2f x =~ ground)

/-- **ax-similar-refl**: every Form shares continuation capacity with itself. -/
axiom axSimilarRefl : ∀ x : Form, x ~~ x

/-- **ax-similar-symm**: shared continuation capacity is shared both ways. -/
axiom axSimilarSymm : ∀ x y : Form, (x ~~ y) → (y ~~ x)

/-- **ax-congruent-trans**: same substance composes. -/
axiom axCongruentTrans : ∀ x y z : Form, (x =~ y) → (y =~ z) → (x =~ z)

/-- f2f(ground) is `=~`-reflexive: ax-box puts it in the orbit, so it has
    syntax, so it has substance. -/
theorem applyGroundIsCongruentToItself : f2f ground =~ f2f ground :=
  (closeSubstanceOpaque _).mp
    (axSyntaxRequiresSubstance _
      ((closeSyntaxOpaque _).mpr
        ⟨3, (closeStructOrbits (f2f ground)).mp (axBox (f2f ground))⟩))

theorem repeatApplyInner (n : Nat) (x : Form) :
    Nat.repeat f2f n (f2f x) = f2f (Nat.repeat f2f n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f2f ih

/-- derives-is-directional: Derives is not symmetric. FORM.

    ground derives f2f(ground) in one step. A return would put an f2f-image at
    ground's substance, which `axDiffCongruent` denies. -/
theorem derivesIsDirectional_FRAME : ¬ ∀ x y : Form, Derives x y → Derives y x := by
  intro symm
  have fwd : Derives ground (f2f ground) :=
    (closeDerivesOpaque _ _).mpr ⟨1, applyGroundIsCongruentToItself⟩
  obtain ⟨n, back⟩ := (closeDerivesOpaque _ _).mp (symm _ _ fwd)
  rw [repeatApplyInner] at back
  exact axDiffCongruent _ back

/-- definition-of-ground: ground is defined by its primitive declaration. FORM.
    name-quoting is a file-format convention; D indexes by Form position, not string.

    Zero applications of forming reach ground from ground, and that is a `=~`
    landing by `axGroundSubstanceAx`, so ground defines itself. -/
theorem definitionOfGround : Definition ground ground :=
  (closeDefinitionOpaque ground ground).mpr
    ((closeDerivesOpaque ground ground).mpr
      ⟨0, (closeSubstanceOpaque ground).mp axGroundSubstanceAx⟩)

-- ============================================================================
-- §IX  Self-Kernel
-- Structural census. 45 steps. Every entity declared in L0 accounted for.
-- Steps 25-31: closed in §VIII.a, in this layer.
-- Step 24 (definitionOfGround): proved in this layer from those closes.
-- Step 40 (derivesIsDirectional): proved in this layer from axDiffCongruent.
-- Census status: FORM.
-- ============================================================================

end Hypermath
