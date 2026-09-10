import Hypermath.Trace
import Hypermath.RecordEncoding

/-!
An explicit model of all 38 logical axiom clauses declared in L0Ground,
L1Relations, L2Operations, and L3Ordinatics. FullAxioms repeats their entire
types under an interpretation of every source parameter. Admitted theorems
and prose glosses are not model axioms.

Forms have two disjoint successor chains. The second contains ordinalLimit.
Similar is universal; Congruent and Simulation are equality. The purported
least-upper-bound implication has a false antecedent for every Form because
there is no common upper bound of the first chain. Opaque path endpoints
have no required relationship to path edges in the actual axioms.
This models those clauses, not the stronger intended source semantics,
infinite paths, ordinal arithmetic, or a completed theory.
-/

namespace HypermathFullAxiomModel
abbrev Form := Nat × Bool
def ground : Form := (0, false)
def f2f (x : Form) : Form := (x.1 + 1, x.2)
def Similar (_ _ : Form) : Prop := True
def Congruent (x y : Form) : Prop := x = y
def Simulation (x y : Form) : Prop := x = y
def structContinues (_ _ : Form) : Prop := True
def structDistinct (x y : Form) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Form) : Prop := True
def HMSyntax (_ : Form) : Prop := True
def Substance (_ : Form) : Prop := True
def Semantics (_ : Form) : Prop := True
def FormClosure (_ : Form) : Prop := True
def Derives (x y : Form) : Prop := ∃ n : Nat, Nat.repeat f2f n x = y
def Discharge (c e : Form) : Prop := Derives e c
def Definition (n x : Form) : Prop := Derives n x
def deriver : Form := ground
abbrev DerivationPath := Nat
def pathStep (_ _ : Form) : DerivationPath := 1
def pathGround : DerivationPath := 0
def pathLength (p : DerivationPath) : Form := (p, false)
def pathTrace (_ : DerivationPath) : Form := ground
def compose (p q : DerivationPath) : DerivationPath := p + q
def congruentPath (p q : DerivationPath) : Prop := p = q
def ordinalLimit : Form := (0, true)
def pathStart (_ : DerivationPath) : Form := ground
def pathEnd (_ : DerivationPath) : Form := ordinalLimit
def ordinalSucc : Form → Form := f2f
/-- A chosen value for the unconstrained parameter. OrdinalApply computation
laws are not among the 38 logical clauses certified below. -/
def ordinalApply (_ x : Form) : Form := x

/-- The exact production finite closure and preserving D definitions,
instantiated with this model's Forms and operation, not independent labels. -/
def finiteApplyPosition (n : Nat) : Form := Nat.repeat f2f n ground
def finiteApplyFromGround (x : Form) : Prop := ∃ n : Nat, finiteApplyPosition n = x
def DStep (x y : Form) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Form) := Hypermath.Trace DStep x y
def D (x y : Form) : Prop := Nonempty (DEntry x y)

theorem repeat_value (n : Nat) (x : Form) : Nat.repeat f2f n x = (x.1 + n, x.2) := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => simp only [Nat.repeat, ih, f2f, Nat.add_assoc]

/-- Each field retains the corresponding source logical axiom's exact name. -/
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

theorem model_axBox : ∀ (x : Form), structOrbits (f2f (f2f x)) x := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axComposeAssoc : ∀ (p q r : DerivationPath), congruentPath (compose p (compose q r)) (compose (compose p q) r) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axComposeIdentity : ∀ (p : DerivationPath), And (congruentPath (compose p pathGround) p) (congruentPath (compose pathGround p) p) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axComposeNonempty : Form → Form → Exists fun p => Not (congruentPath p pathGround) := by
  intro x y
  exact ⟨1, by simp [congruentPath, pathGround]⟩

theorem model_axCoop : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axCoopComm : ∀ (a b : Form), Exists fun ca => Exists fun cab => And (Similar ca a) (And (Similar ca b) (And (Similar cab b) (And (Similar cab a) (Congruent ca cab)))) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axCoopIdentity : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axDiff : ∀ (x : Form), structDistinct (f2f x) ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axFormClosesLoop : ∀ (x : Form), HMSyntax x → Semantics x → FormClosure x := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axGroundSelf : structContinues ground ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axGroundSemanticsAx : Semantics ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axGroundSubstanceAx : Substance ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axGroundSyntaxAx : HMSyntax ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axLimitDerives : Exists fun limitPath => And (Similar (pathStart limitPath) ground) (Congruent (pathEnd limitPath) ordinalLimit) := by
  exact ⟨0, trivial, rfl⟩

theorem model_axLimitIsLimit : ∀ (y : Form), (∀ (n : Nat), Derives (Nat.repeat f2f n ground) y) → Derives ordinalLimit y := by
  intro y upper
  obtain ⟨n, reaches⟩ := upper (y.1 + 1)
  have impossible : y.1 + 1 + n = y.1 := by
    simpa only [repeat_value, ground, Nat.zero_add] using congrArg Prod.fst reaches
  have larger : y.1 < y.1 + 1 + n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
  exact False.elim ((Nat.ne_of_lt larger) impossible.symm)

theorem model_axLimitNotFinite : ∀ (n : Nat), Not (Simulation (Nat.repeat f2f n ground) ordinalLimit) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSemanticsRequiresSyntax : ∀ (x : Form), Semantics x → HMSyntax x := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSeq : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSeqAsymm : ∀ (a b : Form), Not (Congruent a b) → Exists fun c => Exists fun d => And (Similar c a) (And (Similar c b) (And (Similar d b) (And (Similar d a) (Not (Congruent c d))))) := by
  intro a b different
  exact ⟨ground, f2f ground, trivial, trivial, trivial, trivial,
    by simp [Congruent, ground, f2f]⟩

theorem model_axSeqIdentityL : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSeqIdentityR : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSim : ∀ (x : Form), structContinues (f2f x) ground := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSubstanceRequiresSemantics : ∀ (x : Form), Substance x → Semantics x := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_axSuccExtends : ∀ (x : Form), And (Derives x (ordinalSucc x)) (Not (Simulation (ordinalSucc x) x)) := by
  intro x
  constructor
  · exact ⟨1, rfl⟩
  · intro same
    have impossible := congrArg Prod.fst same
    simp [ordinalSucc, f2f] at impossible

theorem model_axSyntaxRequiresSubstance : ∀ (x : Form), HMSyntax x → Substance x := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeDefinitionOpaque : ∀ (n x : Form), Iff (Definition n x) (Derives n x) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeDerivesOpaque : ∀ (x y : Form), Iff (Derives x y) (Exists fun n => Congruent (Nat.repeat f2f n x) y) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeDischargeOpaque : ∀ (c e : Form), Iff (Discharge c e) (Derives e c) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeFormClosureOpaque : ∀ (x : Form), Iff (FormClosure x) (And (HMSyntax x) (And (Substance x) (Semantics x))) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeSemanticsOpaque : ∀ (x : Form), Iff (Semantics x) (Simulation x x) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeStructContinues : ∀ (x : Form), Iff (structContinues x ground) (Similar x ground) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeStructDistinct : ∀ (x y : Form), Iff (structDistinct x y) (Not (Simulation x y)) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeStructOrbits : ∀ (x : Form), Iff (structOrbits (f2f (f2f x)) x) (Similar (f2f (f2f x)) x) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeSubstanceOpaque : ∀ (x : Form), Iff (Substance x) (Congruent x x) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_closeSyntaxOpaque : ∀ (x : Form), Iff (HMSyntax x) (Exists fun n => Similar (Nat.repeat f2f n ground) x) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_filtrationCongSim : ∀ (x y : Form), Congruent x y → Similar x y := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_filtrationSimCong : ∀ (x y : Form), Simulation x y → Congruent x y := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem model_traceLevels : ∀ (x : Form), And (Similar (f2f x) x) (And (Congruent (f2f x) x → Similar (f2f x) x) (Simulation (f2f x) x → Congruent (f2f x) x)) := by
  simp [ground, f2f, Similar, Congruent, Simulation, structContinues, structDistinct, structOrbits, HMSyntax, Substance, Semantics, FormClosure, Derives, Discharge, Definition, ordinalLimit, ordinalSucc, compose, congruentPath, pathGround, repeat_value, Nat.add_assoc]

theorem full_axioms_hold : FullAxioms := {
  axBox := model_axBox
  axComposeAssoc := model_axComposeAssoc
  axComposeIdentity := model_axComposeIdentity
  axComposeNonempty := model_axComposeNonempty
  axCoop := model_axCoop
  axCoopComm := model_axCoopComm
  axCoopIdentity := model_axCoopIdentity
  axDiff := model_axDiff
  axFormClosesLoop := model_axFormClosesLoop
  axGroundSelf := model_axGroundSelf
  axGroundSemanticsAx := model_axGroundSemanticsAx
  axGroundSubstanceAx := model_axGroundSubstanceAx
  axGroundSyntaxAx := model_axGroundSyntaxAx
  axLimitDerives := model_axLimitDerives
  axLimitIsLimit := model_axLimitIsLimit
  axLimitNotFinite := model_axLimitNotFinite
  axSemanticsRequiresSyntax := model_axSemanticsRequiresSyntax
  axSeq := model_axSeq
  axSeqAsymm := model_axSeqAsymm
  axSeqIdentityL := model_axSeqIdentityL
  axSeqIdentityR := model_axSeqIdentityR
  axSim := model_axSim
  axSubstanceRequiresSemantics := model_axSubstanceRequiresSemantics
  axSuccExtends := model_axSuccExtends
  axSyntaxRequiresSubstance := model_axSyntaxRequiresSubstance
  closeDefinitionOpaque := model_closeDefinitionOpaque
  closeDerivesOpaque := model_closeDerivesOpaque
  closeDischargeOpaque := model_closeDischargeOpaque
  closeFormClosureOpaque := model_closeFormClosureOpaque
  closeSemanticsOpaque := model_closeSemanticsOpaque
  closeStructContinues := model_closeStructContinues
  closeStructDistinct := model_closeStructDistinct
  closeStructOrbits := model_closeStructOrbits
  closeSubstanceOpaque := model_closeSubstanceOpaque
  closeSyntaxOpaque := model_closeSyntaxOpaque
  filtrationCongSim := model_filtrationCongSim
  filtrationSimCong := model_filtrationSimCong
  traceLevels := model_traceLevels
}

theorem finite_numerals_injective :
    ∀ n m : Nat, finiteApplyPosition n = finiteApplyPosition m → n = m := by
  intro n m same
  simpa only [finiteApplyPosition, repeat_value, ground, Nat.zero_add] using congrArg Prod.fst same

theorem limit_not_finite : ¬ finiteApplyFromGround ordinalLimit := by
  rintro ⟨n, same⟩
  have impossible := congrArg Prod.snd same
  simp [finiteApplyPosition, repeat_value, ground, ordinalLimit] at impossible

theorem no_step {x y : Form} (edge : DStep x y) : False := by
  have same : f2f x = x := edge.1 ▸ edge.2
  have impossible := congrArg Prod.fst same
  simp [f2f] at impossible

theorem trace_is_zero {x y : Form} (path : DEntry x y) : x = y ∧ path.length = 0 := by
  cases path with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons edge _ => exact False.elim (no_step edge)

theorem ground_does_not_reach_limit : ¬ D ground ordinalLimit := by
  rintro ⟨path⟩
  have same := (trace_is_zero path).1
  have impossible := congrArg Prod.snd same
  simp [ground, ordinalLimit] at impossible

/-- Boundary separation holds even though every Form has syntax in this model. -/
theorem boundary_probe :
    (∀ x : Form, HMSyntax x) ∧ ¬ finiteApplyFromGround ordinalLimit ∧ ¬ D ground ordinalLimit :=
  ⟨fun _ => trivial, limit_not_finite, ground_does_not_reach_limit⟩

/-! A concrete faithful interpretation of composed records. The model and all
38 clauses above are unchanged. Decoding and checking below are host functions
on these model values; they are not added to the native source signature. -/

open Hypermath.GroundSyntax Hypermath.GroundDerivation Hypermath.RecordEncoding

def groundModel : Hypermath.GroundDerivation.Model where
  Carrier := Form
  base := ground
  step := f2f
  distinct := structDistinct
  continues := structContinues
  orbits := structOrbits
  diffRule := model_axDiff
  simRule := model_axSim
  boxRule := model_axBox
  groundRule := model_axGroundSelf
  similar := Similar
  simulation := Simulation
  closeContinues := model_closeStructContinues
  closeDistinct := model_closeStructDistinct
  closeOrbits := model_closeStructOrbits

/-- Packed model values avoid constructing the unary term. -/
def recordValue (record : Record) : Form := (recordCode record, false)
def formulaValue (formula : Formula) : Form := (formulaCode formula, false)

theorem recordValue_is_interpretation (record : Record) :
    recordValue record = (recordTerm record).interpret ground f2f := by
  simp [recordValue, recordTerm, Term.interpret_ofDepth, repeat_value, ground]

theorem formulaValue_is_interpretation (formula : Formula) :
    formulaValue formula = (formulaTerm formula).interpret ground f2f := by
  simp [formulaValue, formulaTerm, Term.interpret_ofDepth, repeat_value, ground]

def readRecordValue : Form → Option Record
  | (number, false) => decodeRecord number
  | (_, true) => none

def readFormulaValue : Form → Option Formula
  | (number, false) => decodeFormula number
  | (_, true) => none

theorem readRecordValue_recordValue (record : Record) :
    readRecordValue (recordValue record) = some record := decode_recordCode record

theorem readFormulaValue_formulaValue (formula : Formula) :
    readFormulaValue (formulaValue formula) = some formula := decode_formulaCode formula

theorem interpreted_record_recovered (record : Record) :
    readRecordValue ((recordTerm record).interpret ground f2f) = some record := by
  rw [← recordValue_is_interpretation]
  exact readRecordValue_recordValue record

theorem interpreted_observation_preserved {β : Type} (query : Record → β) (record : Record) :
    (readRecordValue ((recordTerm record).interpret ground f2f)).map query =
      some (query record) := by
  rw [interpreted_record_recovered]
  rfl

theorem recordValue_injective {first second : Record}
    (same : recordValue first = recordValue second) : first = second :=
  recordCode_injective (congrArg Prod.fst same)

def checkValues (record formula : Form) : Bool :=
  checkDecoded (readRecordValue record) (readFormulaValue formula)

theorem checkValues_values (record : Record) (formula : Formula) :
    checkValues (recordValue record) (formulaValue formula) =
      Hypermath.GroundDerivation.check record formula := checkNumbers_codes record formula

theorem checkValues_sound (record formula : Form)
    (accepted : checkValues record formula = true) :
    ∃ claim, readFormulaValue formula = some claim ∧ claim.holds groundModel := by
  cases r : readRecordValue record with
  | none => simp [checkValues, checkDecoded, r] at accepted
  | some proof =>
      cases f : readFormulaValue formula with
      | none => simp [checkValues, checkDecoded, r, f] at accepted
      | some claim =>
          exact ⟨claim, rfl, Hypermath.GroundDerivation.check_sound groundModel proof claim
            (by simpa [checkValues, checkDecoded, r, f] using accepted)⟩

/-- This is one faithful model of the clauses, not a universal recovery law. -/
theorem full_clauses_with_faithful_records :
    FullAxioms ∧
    (∀ record, readRecordValue ((recordTerm record).interpret ground f2f) = some record) ∧
    (∀ record formula, checkValues (recordValue record) (formulaValue formula) =
      Hypermath.GroundDerivation.check record formula) :=
  ⟨full_axioms_hold, interpreted_record_recovered, checkValues_values⟩

theorem other_chain_not_a_record (number : Nat) : readRecordValue (number, true) = none := rfl
theorem other_chain_not_a_formula (number : Nat) : readFormulaValue (number, true) = none := rfl

theorem record_formula_values_disjoint (record : Record) (formula : Formula) :
    recordValue record ≠ formulaValue formula := by
  intro same
  have decoded := congrArg readRecordValue same
  change decodeRecord (recordCode record) = decodeRecord (formulaCode formula) at decoded
  rw [decode_recordCode, decodeRecord_formulaCode] at decoded
  cases decoded

/-- The existing preserving path relation cannot implement this direct
record-to-conclusion transition, even in the faithful model. This refutes that
particular realization, not other ranked or source-native mechanisms. -/
theorem no_preserving_record_to_formula (record : Record) (formula : Formula) :
    ¬ D (recordValue record) (formulaValue formula) := by
  rintro ⟨path⟩
  exact record_formula_values_disjoint record formula (trace_is_zero path).1

theorem interpreted_separation_checked (term : Term) :
    checkValues (recordValue (quote (separation term)))
      (formulaValue (.both (.similar (.apply term) .ground)
        (.notSimulation (.apply term) .ground))) = true := by
  rw [checkValues_values]
  exact check_quote (separation term)

theorem interpreted_wrong_claim_rejected :
    checkValues (recordValue (.primitive .groundSelf))
      (formulaValue (.notSimulation .ground .ground)) = false := by
  rw [checkValues_values]
  rfl

theorem other_chain_rejected (number : Nat) (formula : Form) :
    checkValues (number, true) formula = false := rfl

/-! Source executive closure and proof-record acceptance are different claims.
The predicates below use the existing model parameters without changing any
of the 38 clauses. Every encoded raw record is a generated, closed Form,
including records with invalid inference steps. -/

/-- Exactly the existing executive predicates and ground anchoring, not a
new acceptance predicate or a native proof rule. -/
def NativeRecordReady (record : Record) : Prop :=
  HMSyntax (recordValue record) ∧ Substance (recordValue record) ∧
  Semantics (recordValue record) ∧ FormClosure (recordValue record) ∧
  Derives ground (recordValue record) ∧ Definition ground (recordValue record) ∧
  Discharge (recordValue record) ground

theorem record_native_ready (record : Record) : NativeRecordReady record := by
  have generated : Derives ground (recordValue record) :=
    ⟨recordCode record, by simp [repeat_value, ground, recordValue]⟩
  exact ⟨trivial, trivial, trivial, trivial, generated, generated, generated⟩

def groundClaim : Formula := .structural (.continues .ground .ground)
def validGroundRecord : Record := .primitive .groundSelf
/-- A projection falsely annotates a primitive premise as a conjunction. -/
def invalidGroundRecord : Record :=
  .projectLeft groundClaim groundClaim validGroundRecord

theorem same_conclusion_opposite_acceptance :
    validGroundRecord.conclusion = invalidGroundRecord.conclusion ∧
    Hypermath.GroundDerivation.check validGroundRecord groundClaim = true ∧
    Hypermath.GroundDerivation.check invalidGroundRecord groundClaim = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- The rejected record has a true, derivable conclusion and satisfies every
listed native executive condition. The defect is in its claimed inference. -/
theorem rejected_record_has_native_closure :
    NativeRecordReady invalidGroundRecord ∧ groundClaim.holds groundModel ∧
    Nonempty (Derivation groundClaim) ∧
    checkValues (recordValue invalidGroundRecord) (formulaValue groundClaim) = false := by
  refine ⟨record_native_ready _, model_axGroundSelf, ⟨.primitive .groundSelf⟩, ?_⟩
  rw [checkValues_values]
  rfl

/-- Reading only the conclusion loses the distinction between a valid and
invalid formation tree, even though both have the same native closure status. -/
theorem no_conclusion_only_record_checker :
    ¬ ∃ checker : Formula → Formula → Bool, ∀ record claimed,
      checker record.conclusion claimed = Hypermath.GroundDerivation.check record claimed := by
  rintro ⟨checker, agreement⟩
  have accepted := agreement validGroundRecord groundClaim
  have rejected := agreement invalidGroundRecord groundClaim
  change checker groundClaim groundClaim = true at accepted
  change checker groundClaim groundClaim = false at rejected
  exact Bool.noConfusion (accepted.symm.trans rejected)

theorem native_closure_is_not_record_acceptance :
    ¬ ∀ record, NativeRecordReady record ↔
      checkValues (recordValue record) (formulaValue record.conclusion) = true := by
  intro agreement
  have accepted := (agreement invalidGroundRecord).mp (record_native_ready _)
  rw [checkValues_values] at accepted
  change false = true at accepted
  exact Bool.noConfusion accepted

theorem full_clauses_with_rejected_closed_record :
    FullAxioms ∧ NativeRecordReady invalidGroundRecord ∧
    checkValues (recordValue invalidGroundRecord) (formulaValue groundClaim) = false :=
  ⟨full_axioms_hold, rejected_record_has_native_closure.1,
    rejected_record_has_native_closure.2.2.2⟩

#print axioms recordValue_is_interpretation
#print axioms formulaValue_is_interpretation
#print axioms readRecordValue_recordValue
#print axioms readFormulaValue_formulaValue
#print axioms interpreted_record_recovered
#print axioms interpreted_observation_preserved
#print axioms recordValue_injective
#print axioms checkValues_values
#print axioms checkValues_sound
#print axioms full_clauses_with_faithful_records
#print axioms other_chain_not_a_record
#print axioms other_chain_not_a_formula
#print axioms record_formula_values_disjoint
#print axioms no_preserving_record_to_formula
#print axioms interpreted_separation_checked
#print axioms interpreted_wrong_claim_rejected
#print axioms other_chain_rejected
#print axioms record_native_ready
#print axioms same_conclusion_opposite_acceptance
#print axioms rejected_record_has_native_closure
#print axioms no_conclusion_only_record_checker
#print axioms native_closure_is_not_record_acceptance
#print axioms full_clauses_with_rejected_closed_record

#print axioms full_axioms_hold
#print axioms finite_numerals_injective
#print axioms boundary_probe

end HypermathFullAxiomModel
