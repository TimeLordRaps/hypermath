/-!
# Recursion rescue: the finite countermodel also satisfies the three L3 computation claims

Self-contained (no imports). Everything from `namespace` through `full_axioms_hold` below is
reproduced verbatim from `lean4/FiniteActionCountermodel.lean` (that file's lines 22-65 for the
model, 77-98 and 99-240 for helper lemmas, `FullAxioms` and `full_axioms_hold`), except that
(a) the constant `ordinalApply` and the trace-defined `D` are omitted (`FullAxioms` mentions
neither) and (b) the namespace is `HypermathRecursionRescue`, so nothing here collides with, or
modifies, the reviewed file. If `FiniteActionCountermodel.lean` ever changes, this copy must be
re-synchronised by hand; it is not mechanically tied to it.

What is shown: in the six-element model that satisfies all 38 `FullAxioms` clauses, giving
`ordinalApply` a defined table (`ordinalApplyRec`, found by exhaustive search over that finite
model) makes `ordinalZeroIdentity`, `ordinalSuccApplies` and `pathLengthArithmetic` hold, up to
the model's `Congruent`. So the finite countermodel refutes "the claims follow from the clauses
as formalized", not "the claims are consistent with the clauses".

What is not shown: that the table is the intended semantics of ordinal application; that any
infinite or transfinite model has this property; that the native `.hm` semantics, which these
38 Lean clauses only approximate (source adequacy is UNKNOWN), supports the claims. The `.hm`
tags of the three derives are unchanged; whether to add recursion equations to L3 or retag the
claims is an owner decision that this file does not make.
-/

namespace HypermathRecursionRescue

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


def ordinalApplyRec : Form → Form → Form
  | .a0, .a0 => .a0 | .a0, .a1 => .a1 | .a0, .a2 => .a2 | .a0, .b0 => .b0 | .a0, .b1 => .a1 | .a0, .b2 => .a2
  | .a1, .a0 => .a1 | .a1, .a1 => .a2 | .a1, .a2 => .a1 | .a1, .b0 => .a1 | .a1, .b1 => .a2 | .a1, .b2 => .a1
  | .a2, .a0 => .a2 | .a2, .a1 => .a1 | .a2, .a2 => .a2 | .a2, .b0 => .a2 | .a2, .b1 => .a1 | .a2, .b2 => .a2
  | .b0, _ => .a1
  | .b1, _ => .b2
  | .b2, _ => .b0

theorem rec_zero_identity : ∀ x : Form, Congruent (ordinalApplyRec ground x) x := by
  intro x; cases x <;> rfl

theorem rec_succ_applies :
    ∀ p x : Form, Congruent (ordinalApplyRec (ordinalSucc p) x) (f2f (ordinalApplyRec p x)) := by
  intro p x; cases p <;> cases x <;> rfl

/-- The ground chain, closed form: a0, a1, a2, a1, a2, … -/
def chain : Nat → Form
  | 0 => .a0
  | n + 1 => if n % 2 = 0 then .a1 else .a2

theorem repeat_eq_chain (n : Nat) : Nat.repeat f2f n ground = chain n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show f2f (Nat.repeat f2f n ground) = chain (n + 1)
    rw [ih]
    cases n with
    | zero => rfl
    | succ m =>
      simp only [chain]
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · have : (m + 1) % 2 = 1 := by omega
        simp [h, this, f2f]
      · have : (m + 1) % 2 = 0 := by omega
        simp [h, this, f2f]

theorem rec_path_length_arithmetic :
    ∀ p q : DerivationPath,
      Congruent (pathLength (compose p q)) (ordinalApplyRec (pathLength q) (pathLength p)) := by
  intro p q
  simp only [pathLength, compose, repeat_eq_chain]
  rcases p with _ | p <;> rcases q with _ | q
  · rfl
  · simp only [chain, Nat.zero_add]
    rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [h, ordinalApplyRec] <;> rfl
  · simp only [chain, Nat.add_zero]
    rcases Nat.mod_two_eq_zero_or_one p with h | h <;> simp [h, ordinalApplyRec] <;> rfl
  · have e : p + 1 + (q + 1) = (p + q + 1) + 1 := by omega
    rw [e]; simp only [chain]
    rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;>
    rcases Nat.mod_two_eq_zero_or_one q with hq | hq
    all_goals
      first
      | (have hs : (p + q + 1) % 2 = 1 := by omega
         simp [hp, hq, hs, ordinalApplyRec]; rfl)
      | (have hs : (p + q + 1) % 2 = 0 := by omega
         simp [hp, hq, hs, ordinalApplyRec]; rfl)

/-- Every current axiom clause AND the three computation claims, in one model. -/
theorem clauses_and_computation_laws_consistent :
    FullAxioms ∧
    (∀ x : Form, Congruent (ordinalApplyRec ground x) x) ∧
    (∀ p x : Form, Congruent (ordinalApplyRec (ordinalSucc p) x) (f2f (ordinalApplyRec p x))) ∧
    (∀ p q : DerivationPath,
      Congruent (pathLength (compose p q)) (ordinalApplyRec (pathLength q) (pathLength p))) :=
  ⟨full_axioms_hold, rec_zero_identity, rec_succ_applies, rec_path_length_arithmetic⟩

end HypermathRecursionRescue

#print axioms HypermathRecursionRescue.full_axioms_hold
#print axioms HypermathRecursionRescue.rec_zero_identity
#print axioms HypermathRecursionRescue.rec_succ_applies
#print axioms HypermathRecursionRescue.rec_path_length_arithmetic
#print axioms HypermathRecursionRescue.clauses_and_computation_laws_consistent
