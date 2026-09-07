/- A finite countermodel to selected claimed consequences of the L0/L1 axiom
   clauses. This file imports no Hypermath declarations and uses no sorry or
   custom axioms. It does not model every later L2/L3 clause or prove that the
   intended complete theory is consistent. It identifies missing implications
   in the stated prefix, including the attempted reverse use of filtration. -/

namespace HypermathCountermodel

def ground : Bool := false
def f2f (_ : Bool) : Bool := true
def Similar (_ _ : Bool) : Prop := True
def Congruent (_ _ : Bool) : Prop := True
def Simulation (x y : Bool) : Prop := x = y
def structContinues (_ _ : Bool) : Prop := True
def structDistinct (x y : Bool) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Bool) : Prop := True
def HMSyntax (_ : Bool) : Prop := True
def Substance (_ : Bool) : Prop := True
def Semantics (_ : Bool) : Prop := True
def FormClosure (_ : Bool) : Prop := True
def Derives (_ _ : Bool) : Prop := True
def Discharge (_ _ : Bool) : Prop := True
def Definition (_ _ : Bool) : Prop := True
def deriver : Bool := false
def D (_ _ : Bool) : Prop := False

/-- All 24 logical axiom clauses of L0Ground and L1Relations, with Bool
    replacing their uninterpreted Form parameter. Theorems admitted with
    sorry are deliberately not treated as axioms of this model. -/
structure PrefixAxioms : Prop where
  axDiff : ∀ x, structDistinct (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct x y ↔ ¬ Simulation x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation x y → Congruent x y
  filtrationCongSim : ∀ x y, Congruent x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation x x
  closeDerivesOpaque : ∀ x y, Derives x y ↔ ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge c e ↔ Derives e c
  closeDefinitionOpaque : ∀ n x, Definition n x ↔ Derives n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent (f2f x) x → Similar (f2f x) x) ∧
    (Simulation (f2f x) x → Congruent (f2f x) x)

theorem prefixAxioms_hold : PrefixAxioms := by
  constructor <;> simp [ground, f2f, Similar, Congruent, Simulation,
    structContinues, structDistinct, structOrbits, HMSyntax, Substance,
    Semantics, FormClosure, Derives, Discharge, Definition]

/-- The premise claimed for axSeqAsymm is not supplied by axDiff. -/
theorem reverse_filtration_fails :
    ¬ Simulation (f2f ground) ground ∧ Congruent (f2f ground) ground := by
  simp [Simulation, Congruent, f2f, ground]

/-- Derives can be symmetric while all prefix axiom clauses hold. -/
theorem directionality_claim_fails :
    ¬ (¬ ∀ x y : Bool, Derives x y → Derives y x) := by
  simp [Derives]

/-- No prefix axiom constrains D, so its advertised reflexivity does not follow. -/
theorem d_reflexivity_claim_fails : ¬ (∀ x : Bool, D x x) := by
  simp [D]

/-- The prefix does not provide the promised simulation cycle. -/
theorem driver_cycle_claim_fails : ¬ Simulation (f2f (f2f deriver)) deriver := by
  simp [Simulation, f2f, deriver]

#print axioms prefixAxioms_hold
#print axioms reverse_filtration_fails
#print axioms directionality_claim_fails
#print axioms d_reflexivity_claim_fails
#print axioms driver_cycle_claim_fails

end HypermathCountermodel
