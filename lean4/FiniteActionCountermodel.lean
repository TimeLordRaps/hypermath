import Hypermath.FiniteAction

/-!
A finite interpretation of all 38 current logical axiom clauses, with colliding
finite numeral positions that induce different iteration actions. Every field
of FullAxioms repeats the corresponding declared clause type with exactly the
same name under this interpretation of the source parameters.

Congruent is equality of four explicitly defined classes; Similar is universal,
Simulation is literal equality, and Derives is exactly finite iteration followed
by Congruent landing. The class equivalence does not identify all Forms.
Ground enters a two-cycle; ordinalLimit lies in a disjoint three-cycle.
The opaque Nat path scaffold has no enforced relationship to these cycles.
Admitted theorems and stronger native semantic claims are not assumptions.
This refutes exact action descent from the stated clauses, not native adequacy
or the possibility of an action retaining its iteration witness.
-/

namespace HypermathFiniteActionCountermodel

inductive Form where
  | a0 | a1 | a2 | b0 | b1 | b2
  deriving DecidableEq
instance : Inhabited Form := ⟨.a0⟩
def ground : Form := .a0
def f2f : Form → Form
  | .a0 => .a1
  | .a1 => .a2
  | .a2 => .a1
  | .b0 => .b1
  | .b1 => .b2
  | .b2 => .b0
def Similar (_ _ : Form) : Prop := True
def congruenceClass : Form → Nat
  | .a0 => 0
  | .a1 => 1
  | .a2 => 2
  | .b0 => 3
  | .b1 => 1
  | .b2 => 2
def Congruent (x y : Form) : Prop := congruenceClass x = congruenceClass y
def Simulation (x y : Form) : Prop := x = y
def structContinues (_ _ : Form) : Prop := True
def structDistinct (x y : Form) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Form) : Prop := True
def HMSyntax (_ : Form) : Prop := True
def Substance (_ : Form) : Prop := True
def Semantics (_ : Form) : Prop := True
def FormClosure (_ : Form) : Prop := True
def Derives (x y : Form) : Prop := ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
def Discharge (c e : Form) : Prop := Derives e c
def Definition (n x : Form) : Prop := Derives n x
def deriver : Form := .a1
abbrev DerivationPath := Nat
def pathStep (_ _ : Form) : DerivationPath := 1
def pathGround : DerivationPath := 0
def pathLength (p : DerivationPath) : Form := Nat.repeat f2f p ground
def pathTrace (_ : DerivationPath) : Form := ground
def compose (p q : DerivationPath) : DerivationPath := p + q
def congruentPath (p q : DerivationPath) : Prop := p = q
def ordinalLimit : Form := .b0
def pathStart (_ : DerivationPath) : Form := ground
def pathEnd (_ : DerivationPath) : Form := ordinalLimit
def ordinalSucc : Form → Form := f2f
/-- A constant interpretation is allowed: computation laws are not declared
axioms. The exact three advertised computation claims are refuted below. -/
def ordinalApply (_ _ : Form) : Form := ground

/-- Instantiate the actual finite closure and preserving trace definitions. -/
def finiteApplyPosition (n : Nat) : Form := Nat.repeat f2f n ground
def finiteApplyFromGround (x : Form) : Prop := ∃ n : Nat, finiteApplyPosition n = x
def DStep (x y : Form) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Form) := Hypermath.Trace DStep x y
def D (x y : Form) : Prop := Nonempty (DEntry x y)

def GroundChain (x : Form) : Prop := x = .a0 ∨ x = .a1 ∨ x = .a2

theorem finite_position_in_ground_chain (n : Nat) :
    GroundChain (Nat.repeat f2f n ground) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    change GroundChain (f2f (Nat.repeat f2f n ground))
    rcases ih with ha | ha | ha <;> rw [ha] <;> simp [GroundChain, f2f]

theorem a_cycle_closed (n : Nat) :
    Nat.repeat f2f n Form.a1 = Form.a1 ∨ Nat.repeat f2f n Form.a1 = Form.a2 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    change f2f (Nat.repeat f2f n Form.a1) = Form.a1 ∨
      f2f (Nat.repeat f2f n Form.a1) = Form.a2
    rcases ih with ha | ha <;> rw [ha] <;> simp [f2f]

theorem congruence_is_equivalence : Equivalence Congruent :=
  ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- Exact current logical clause types; no admitted theorem is included. -/
structure FullAxioms : Prop where
  axBox : ∀ (x : Form), structOrbits (f2f (f2f x)) x
  axComposeAssoc : ∀ (p q r : DerivationPath), congruentPath (compose p (compose q r)) (compose (compose p q) r)
  axComposeIdentity : ∀ (p : DerivationPath), And (congruentPath (compose p pathGround) p) (congruentPath (compose pathGround p) p)
  axComposeNonempty : Form → Form → Exists fun p => Not (congruentPath p pathGround)
  axCoop : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axCoopComm : ∀ (a b : Form), Exists fun ca => Exists fun cab => And (Similar ca a) (And (Similar ca b) (And (Similar cab b) (And (Similar cab a) (Congruent ca cab))))
  axCoopIdentity : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axDiff : ∀ (x : Form), structDistinct (f2f x) ground
  axFormClosesLoop : ∀ (x : Form), HMSyntax x → Semantics x → FormClosure x
  axGroundSelf : structContinues ground ground
  axGroundSemanticsAx : Semantics ground
  axGroundSubstanceAx : Substance ground
  axGroundSyntaxAx : HMSyntax ground
  axLimitDerives : Exists fun limitPath => And (Similar (pathStart limitPath) ground) (Congruent (pathEnd limitPath) ordinalLimit)
  axLimitIsLimit : ∀ (y : Form), (∀ (n : Nat), Derives (Nat.repeat f2f n ground) y) → Derives ordinalLimit y
  axLimitNotFinite : ∀ (n : Nat), Not (Simulation (Nat.repeat f2f n ground) ordinalLimit)
  axSemanticsRequiresSyntax : ∀ (x : Form), Semantics x → HMSyntax x
  axSeq : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axSeqAsymm : ∀ (a b : Form), Not (Congruent a b) → Exists fun c => Exists fun d => And (Similar c a) (And (Similar c b) (And (Similar d b) (And (Similar d a) (Not (Congruent c d)))))
  axSeqIdentityL : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axSeqIdentityR : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axSim : ∀ (x : Form), structContinues (f2f x) ground
  axSubstanceRequiresSemantics : ∀ (x : Form), Substance x → Semantics x
  axSuccExtends : ∀ (x : Form), And (Derives x (ordinalSucc x)) (Not (Simulation (ordinalSucc x) x))
  axSyntaxRequiresSubstance : ∀ (x : Form), HMSyntax x → Substance x
  closeDefinitionOpaque : ∀ (n x : Form), Iff (Definition n x) (Derives n x)
  closeDerivesOpaque : ∀ (x y : Form), Iff (Derives x y) (Exists fun n => Congruent (Nat.repeat f2f n x) y)
  closeDischargeOpaque : ∀ (c e : Form), Iff (Discharge c e) (Derives e c)
  closeFormClosureOpaque : ∀ (x : Form), Iff (FormClosure x) (And (HMSyntax x) (And (Substance x) (Semantics x)))
  closeSemanticsOpaque : ∀ (x : Form), Iff (Semantics x) (Simulation x x)
  closeStructContinues : ∀ (x : Form), Iff (structContinues x ground) (Similar x ground)
  closeStructDistinct : ∀ (x y : Form), Iff (structDistinct x y) (Not (Simulation x y))
  closeStructOrbits : ∀ (x : Form), Iff (structOrbits (f2f (f2f x)) x) (Similar (f2f (f2f x)) x)
  closeSubstanceOpaque : ∀ (x : Form), Iff (Substance x) (Congruent x x)
  closeSyntaxOpaque : ∀ (x : Form), Iff (HMSyntax x) (Exists fun n => Similar (Nat.repeat f2f n ground) x)
  filtrationCongSim : ∀ (x y : Form), Congruent x y → Similar x y
  filtrationSimCong : ∀ (x y : Form), Simulation x y → Congruent x y
  traceLevels : ∀ (x : Form), And (Similar (f2f x) x) (And (Congruent (f2f x) x → Similar (f2f x) x) (Simulation (f2f x) x → Congruent (f2f x) x))

theorem full_axioms_hold : FullAxioms := {
  axBox := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axComposeAssoc := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axComposeIdentity := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axComposeNonempty := by
    intro x y
    exact ⟨1, by simp [congruentPath, pathGround]⟩
  axCoop := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axCoopComm := by
    intro a b
    exact ⟨a, a, trivial, trivial, trivial, trivial, rfl⟩
  axCoopIdentity := by
    intro a
    exact ⟨a, trivial, rfl⟩
  axDiff := by
    intro x
    cases x <;> simp [structDistinct, Simulation, f2f, ground]
  axFormClosesLoop := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axGroundSelf := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axGroundSemanticsAx := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axGroundSubstanceAx := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axGroundSyntaxAx := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axLimitDerives := by
    exact ⟨0, trivial, rfl⟩
  axLimitIsLimit := by
    intro y upper
    obtain ⟨n, reaches⟩ := upper 1
    change Congruent (Nat.repeat f2f n Form.a1) y at reaches
    rcases a_cycle_closed n with ha | ha
    · rw [ha] at reaches
      exact ⟨1, reaches⟩
    · rw [ha] at reaches
      exact ⟨2, reaches⟩
  axLimitNotFinite := by
    intro n same
    have inside := finite_position_in_ground_chain n
    change Nat.repeat f2f n ground = Form.b0 at same
    rw [same] at inside
    simp [GroundChain] at inside
  axSemanticsRequiresSyntax := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axSeq := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axSeqAsymm := by
    intro a b different
    exact ⟨a, b, trivial, trivial, trivial, trivial, different⟩
  axSeqIdentityL := by
    intro a
    exact ⟨a, trivial, rfl⟩
  axSeqIdentityR := by
    intro a
    exact ⟨a, trivial, rfl⟩
  axSim := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axSubstanceRequiresSemantics := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  axSuccExtends := by
    intro x
    constructor
    · exact ⟨1, rfl⟩
    · cases x <;> simp [ordinalSucc, Simulation, f2f]
  axSyntaxRequiresSubstance := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeDefinitionOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeDerivesOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeDischargeOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeFormClosureOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeSemanticsOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeStructContinues := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeStructDistinct := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeStructOrbits := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeSubstanceOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  closeSyntaxOpaque := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  filtrationCongSim := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  filtrationSimCong := by
    simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, Nat.add_assoc]
  traceLevels := by
    intro x
    exact ⟨trivial, (fun _ => trivial), (fun h => congrArg congruenceClass h)⟩
}

/-- Ground's first and third positions are exactly the same Form. -/
theorem numeral_collision : finiteApplyPosition 1 = finiteApplyPosition 3 := rfl

/-- That equality does not identify the corresponding actions on the other cycle. -/
theorem action_disagreement : Nat.repeat f2f 1 Form.b0 ≠ Nat.repeat f2f 3 Form.b0 := by
  decide

theorem finite_action_incompatible :
    ¬ Hypermath.FiniteAction.FiniteActionCompatible f2f ground := by
  intro compatible
  exact action_disagreement (compatible 1 3 numeral_collision Form.b0)

/-- No single exact action indexed only by numeral Form satisfies every count. -/
theorem no_exact_finite_action :
    ¬ ∃ action : Form → Form → Form,
      Hypermath.FiniteAction.ExactFiniteAction f2f ground action := by
  intro ⟨action, exactAction⟩
  exact finite_action_incompatible
    (Hypermath.FiniteAction.exact_implies_compatible exactAction)

/-- The colliding counts disagree even after passage to the class equivalence. -/
theorem action_congruence_disagreement :
    ¬ Congruent (Nat.repeat f2f 1 Form.b0) (Nat.repeat f2f 3 Form.b0) := by
  unfold Congruent
  decide

theorem relation_action_incompatible :
    ¬ Hypermath.FiniteAction.RelationActionCompatible Congruent f2f ground := by
  intro compatible
  exact action_congruence_disagreement (compatible 1 3 numeral_collision Form.b0)

/-- There is no action agreeing up to Congruent with every represented count,
even though Congruent is a fully explicit equivalence relation. -/
theorem no_congruent_finite_action :
    ¬ ∃ action : Form → Form → Form,
      Hypermath.FiniteAction.CongruentActionAgreement Congruent f2f ground action := by
  intro ⟨action, agreement⟩
  exact relation_action_incompatible
    (Hypermath.FiniteAction.agreement_implies_relation_compatible
      (fun h => h.symm) (fun h k => h.trans k) agreement)

/-- Exact type of the currently advertised ordinalZeroIdentity proposition. -/
def ordinalZeroIdentityClaim : Prop :=
  ∀ x : Form, Congruent (ordinalApply ground x) x

/-- Exact type of the currently advertised ordinalSuccApplies proposition. -/
def ordinalSuccAppliesClaim : Prop :=
  ∀ p x : Form, Congruent (ordinalApply (ordinalSucc p) x) (f2f (ordinalApply p x))

/-- Exact type of the currently advertised pathLengthArithmetic proposition,
including its operand order in ordinalApply. -/
def pathLengthArithmeticClaim : Prop :=
  ∀ p q : DerivationPath,
    Congruent (pathLength (compose p q)) (ordinalApply (pathLength q) (pathLength p))

theorem ordinal_zero_identity_claim_fails : ¬ ordinalZeroIdentityClaim := by
  intro claim
  have impossible := claim Form.b0
  change (0 : Nat) = 3 at impossible
  exact Nat.noConfusion impossible

theorem ordinal_successor_action_claim_fails : ¬ ordinalSuccAppliesClaim := by
  intro claim
  have impossible := claim ground ground
  change (0 : Nat) = 1 at impossible
  exact Nat.noConfusion impossible

theorem path_length_arithmetic_claim_fails : ¬ pathLengthArithmeticClaim := by
  intro claim
  have impossible := claim 1 0
  change (1 : Nat) = 0 at impossible
  exact Nat.noConfusion impossible

#print axioms full_axioms_hold
#print axioms numeral_collision
#print axioms action_disagreement
#print axioms finite_action_incompatible
#print axioms no_exact_finite_action
#print axioms congruence_is_equivalence
#print axioms relation_action_incompatible
#print axioms no_congruent_finite_action
#print axioms ordinal_zero_identity_claim_fails
#print axioms ordinal_successor_action_claim_fails
#print axioms path_length_arithmetic_claim_fails

end HypermathFiniteActionCountermodel
