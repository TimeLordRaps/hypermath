import Hypermath.Trace

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

#print axioms full_axioms_hold
#print axioms finite_numerals_injective
#print axioms boundary_probe

end HypermathFullAxiomModel
