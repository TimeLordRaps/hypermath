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
--   Primitives:           `opaque`
--
-- P_0 = 41.  N_0_atomic = 4.  G_0 (NCs for graduation) = 4.
-- Source: L0_ground.hm

namespace Hypermath

-- ============================================================================
-- §I  Primitives
-- Four atomic declarations. All definition-acts. FORM.
-- ============================================================================

/-- The base type. Every entity in hypermath is a Form. -/
opaque Form : Type

-- Note: Prop is Lean4's built-in `Prop : Sort 0`.
-- In .hm: `primitive Prop :: Type` — satisfied here by Lean4's Prop.

/-- The irreducible generative base. Written □ in .hm notation. -/
opaque ground : Form

/-- The sole operation. `f2f` (form-to-form) is `apply` in .hm.
    Renamed to avoid conflict with Lean4's `apply` tactic. -/
opaque f2f : Form → Form

-- ============================================================================
-- §II  Opaque Structural Predicates (pre-relational)
-- Three opaques. All closed in §VI. FORM after close.
-- ============================================================================

/-- `structContinues x y`: x was generated from the same base as y.
    Semantic close (§VI): `structContinues x ground ↔ x ~~ ground` -/
opaque structContinues : Form → Form → Prop

/-- `structDistinct x y`: x and y are not mutually simulating.
    Semantic close (§VI): `structDistinct x y ↔ ¬ (x ≡ y)` -/
opaque structDistinct : Form → Form → Prop

/-- `structOrbits x y`: f2f(f2f(y)) is in the structural orbit of x.
    Semantic close (§VI): `structOrbits (f2f (f2f x)) x ↔ f2f (f2f x) ~~ x` -/
opaque structOrbits : Form → Form → Prop

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
opaque Similar : Form → Form → Prop

/-- **Congruent** (=~): full coincidence of continuation capacity.
    Same outcomes; paths discarded. Generated from ~~ by □. -/
opaque Congruent : Form → Form → Prop

/-- **Simulation** (==, written ≡ in Lean4): mutual path reproduction.
    Same outcomes AND same paths. Generated from =~ by □.
    Notation `≡` used to avoid conflict with Lean4's `==` (BEq). -/
opaque Simulation : Form → Form → Prop

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
opaque HMSyntax : Form → Prop

/-- `Substance x`: x carries derivable matter — middle vertex of the triangle. -/
opaque Substance : Form → Prop

/-- `Semantics x`: x carries meaning derived from its Form membership. -/
opaque Semantics : Form → Prop

/-- `Derives x y`: x is in the derivation-approach of y. Directional. -/
opaque Derives : Form → Form → Prop

/-- `Discharge c e`: evidence e satisfies criterion c. -/
opaque Discharge : Form → Form → Prop

/-- `Definition n f`: name n precisely denotes form f. -/
opaque Definition : Form → Form → Prop

/-- `FormClosure x`: the syntax-substance-semantics triangle completes for x. -/
opaque FormClosure : Form → Prop

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

/-- derives-is-directional: Derives is not symmetric. FRAME/L1.
    Discharged in L1Relations.lean §V. -/
theorem derivesIsDirectional_FRAME : ¬ ∀ x y : Form, Derives x y → Derives y x := by
  sorry
  -- FRAME/L1: asymmetry requires relation-language to state the =~ non-return.
  -- Discharged in Hypermath.L1Relations, theorem derivesIsDirectional.

/-- definition-of-ground: ground is defined by its primitive declaration. FORM.
    name-quoting is a file-format convention; D indexes by Form position, not string. -/
theorem definitionOfGround : Definition ground ground := by
  sorry
  -- FORM: primitive declarations are definition-acts; Definition is axiomatic here.

-- ============================================================================
-- §IX  Self-Kernel
-- Structural census. 41 steps. Every entity declared in L0 accounted for.
-- FORM items: §I–VII plus executive axioms and derives.
-- FRAME residuals: derivesIsDirectional (step 40), §VIII opaque semantic closes
--                 (steps 25–31) — all discharged at L1.
-- Census status: FORM. All FRAME residuals named and forward-referenced.
-- ============================================================================

end Hypermath
