import Hypermath.PathTransport

/-!
# A native-clause model with a witnessed cycle but no path reproduction

Every declared logical clause is interpreted below, together with an actual
two-step simulation-preserving cycle. Nevertheless, two ground-generated
forms in the same Simulation class do not reproduce each other's paths.
This tests the declared clauses, not the stronger prose meaning of mutual
reproduction. The relation names alone do not impose that meaning.
-/

namespace HypermathTransportCountermodel

inductive Form where
  | a0 | a1 | a2 | a3 | a4 | limit
  deriving DecidableEq

instance : Inhabited Form := ⟨.a0⟩
def ground : Form := .a0
def f2f : Form → Form
  | .a0 => .a1
  | .a1 => .a2
  | .a2 => .a3
  | .a3 => .a4
  | .a4 => .a3
  | .limit => .limit

def Similar (_ _ : Form) : Prop := True
def Congruent (_ _ : Form) : Prop := True
def semanticClass : Form → Nat
  | .a0 => 0
  | .a1 | .a3 | .a4 => 1
  | .a2 => 2
  | .limit => 3
def Simulation (x y : Form) : Prop := semanticClass x = semanticClass y
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
def deriver : Form := .a3
abbrev DerivationPath := Nat
def pathStep (_ _ : Form) : DerivationPath := 1
def pathGround : DerivationPath := 0
def pathLength (p : DerivationPath) : Form := Nat.repeat f2f p ground
def pathTrace (_ : DerivationPath) : Form := ground
def compose (p q : DerivationPath) : DerivationPath := p + q
def congruentPath (p q : DerivationPath) : Prop := p = q
def ordinalLimit : Form := .limit
def pathStart (_ : DerivationPath) : Form := ground
def pathEnd (_ : DerivationPath) : Form := ordinalLimit
/-- Only the declared successor clauses are required. This does not interpret
ordinal arithmetic or assume successor equals primitive forming. -/
def ordinalSucc : Form → Form
  | .a0 => .a1
  | _ => .a0
def ordinalApply (_ x : Form) : Form := x

def finiteApplyPosition (n : Nat) : Form := Nat.repeat f2f n ground
def finiteApplyFromGround (x : Form) : Prop := ∃ n : Nat, finiteApplyPosition n = x
def DStep (x y : Form) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Form) := Hypermath.Trace DStep x y
def D (x y : Form) : Prop := Nonempty (DEntry x y)
def SimulationStep (x y : Form) : Prop := y = f2f x ∧ Simulation y x
abbrev SimulationEntry (x y : Form) := Hypermath.Trace SimulationStep x y
def driverCycleClaim : Prop := Simulation (f2f (f2f deriver)) deriver

/-- The same strengthened certificate fields as the native driver witness. -/
structure DriverCycleWitness where
  path : SimulationEntry deriver (f2f (f2f deriver))
  length_two : Hypermath.Trace.length path = 2
  closes : driverCycleClaim

def NativeOneStepLaw : Prop :=
  ∀ {x copyStart : Form}, Simulation x copyStart → Congruent (f2f x) x →
    Congruent (f2f copyStart) copyStart ∧ Simulation (f2f x) (f2f copyStart)

theorem simulation_is_equivalence : Equivalence Simulation :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem forming_preserves_not_limit (x : Form) (h : x ≠ .limit) : f2f x ≠ .limit := by
  cases x <;> simp_all [f2f]

theorem finite_position_not_limit (n : Nat) : finiteApplyPosition n ≠ .limit := by
  induction n with
  | zero => decide
  | succ n ih => exact forming_preserves_not_limit _ ih

theorem simulation_limit_iff (x : Form) : Simulation x ordinalLimit ↔ x = .limit := by
  cases x <;> simp [Simulation, semanticClass, ordinalLimit]

/-- Exact current logical clause types; no admitted theorem or prose law is included. -/
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
  axBox := by intros; trivial
  axComposeAssoc := by intros; exact (Nat.add_assoc _ _ _).symm
  axComposeIdentity := by intro p; exact ⟨Nat.add_zero p, Nat.zero_add p⟩
  axComposeNonempty := by intros; exact ⟨1, by simp [congruentPath, pathGround]⟩
  axCoop := by intro a b; exact ⟨a, trivial, trivial⟩
  axCoopComm := by intro a b; exact ⟨a, a, trivial, trivial, trivial, trivial, trivial⟩
  axCoopIdentity := by intro a; exact ⟨a, trivial, trivial⟩
  axDiff := by intro x; cases x <;> simp [structDistinct, Simulation, semanticClass, f2f, ground]
  axFormClosesLoop := by intros; trivial
  axGroundSelf := trivial
  axGroundSemanticsAx := trivial
  axGroundSubstanceAx := trivial
  axGroundSyntaxAx := trivial
  axLimitDerives := ⟨0, trivial, trivial⟩
  axLimitIsLimit := by intro y _; exact ⟨0, trivial⟩
  axLimitNotFinite := by
    intro n same
    exact finite_position_not_limit n ((simulation_limit_iff _).mp same)
  axSemanticsRequiresSyntax := by intros; trivial
  axSeq := by intro a b; exact ⟨a, trivial, trivial⟩
  axSeqAsymm := by intro a b impossible; exact False.elim (impossible trivial)
  axSeqIdentityL := by intro a; exact ⟨a, trivial, trivial⟩
  axSeqIdentityR := by intro a; exact ⟨a, trivial, trivial⟩
  axSim := by intros; trivial
  axSubstanceRequiresSemantics := by intros; trivial
  axSuccExtends := by
    intro x
    refine ⟨⟨0, trivial⟩, ?_⟩
    cases x <;> simp [Simulation, semanticClass, ordinalSucc]
  axSyntaxRequiresSubstance := by intros; trivial
  closeDefinitionOpaque := by intros; rfl
  closeDerivesOpaque := by intros; rfl
  closeDischargeOpaque := by intros; rfl
  closeFormClosureOpaque := by intro x; exact ⟨fun _ => ⟨trivial, trivial, trivial⟩, fun _ => trivial⟩
  closeSemanticsOpaque := by intro x; exact ⟨fun _ => rfl, fun _ => trivial⟩
  closeStructContinues := by intros; rfl
  closeStructDistinct := by intros; rfl
  closeStructOrbits := by intros; rfl
  closeSubstanceOpaque := by intros; rfl
  closeSyntaxOpaque := by intro x; exact ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  filtrationCongSim := by intros; trivial
  filtrationSimCong := by intros; trivial
  traceLevels := by intro x; exact ⟨trivial, fun _ => trivial, fun _ => trivial⟩
}

def cycleWitness : DriverCycleWitness :=
  ⟨.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)), rfl, rfl⟩

/-- All four conjuncts of the current native self-derivation proposition. -/
def selfDerivation : Prop :=
  structContinues ground ground ∧
  (∀ x : Form, D x x) ∧
  (∀ p : DerivationPath,
    congruentPath (compose p pathGround) p ∧
    congruentPath (compose pathGround p) p) ∧
  Simulation (f2f (f2f deriver)) deriver

theorem self_derivation_holds : selfDerivation :=
  ⟨trivial, fun x => ⟨.nil x⟩, fun p => ⟨Nat.add_zero p, Nat.zero_add p⟩, rfl⟩

theorem cycle_has_two_steps : cycleWitness.path.length = 2 := rfl

theorem related_starts_are_ground_generated :
    finiteApplyPosition 1 = .a1 ∧ finiteApplyPosition 3 = deriver ∧
    Simulation .a1 deriver := ⟨rfl, rfl, rfl⟩

def unmatchedStep : DEntry .a1 .a2 := .cons ⟨rfl, trivial⟩ (.nil _)

def InCycle (x : Form) : Prop := x = .a3 ∨ x = .a4

theorem step_stays_in_cycle {x y : Form} (inside : InCycle x) (edge : DStep x y) :
    InCycle y := by
  rw [edge.1]
  rcases inside with h | h <;> rw [h] <;> simp [InCycle, f2f]

theorem path_stays_in_cycle {x y : Form} (inside : InCycle x) (path : DEntry x y) :
    InCycle y := by
  induction path with
  | nil => exact inside
  | cons edge _ ih => exact ih (step_stays_in_cycle inside edge)

/-- Even an arbitrary finite copied path, including an empty one, cannot
reproduce the endpoint of a1 -> a2 when started at the related deriver. -/
theorem no_finite_reproduction :
    ¬ ∃ endpoint : Form, Nonempty (DEntry deriver endpoint) ∧ Simulation .a2 endpoint := by
  rintro ⟨endpoint, ⟨path⟩, related⟩
  have inside := path_stays_in_cycle (show InCycle deriver from Or.inl rfl) path
  rcases inside with h | h <;> rw [h] at related <;> cases related

theorem native_one_step_law_fails : ¬ NativeOneStepLaw := by
  intro law
  have impossible := (law (x := .a1) (copyStart := deriver) rfl trivial).2
  cases impossible

theorem no_step_transfer :
    ¬ Nonempty (Hypermath.PathTransport.StepTransfer DStep Simulation) := by
  rintro ⟨transfer⟩
  let next := transfer (x := .a1) (copyStart := deriver) rfl
    (show DStep .a1 .a2 from ⟨rfl, trivial⟩)
  exact no_finite_reproduction ⟨next.val, ⟨.cons next.property.1 (.nil _)⟩, next.property.2⟩

/-- A single joint certificate prevents a vacuous "no paths/no cycle" reading. -/
theorem full_model_with_cycle_without_reproduction :
    FullAxioms ∧ selfDerivation ∧ Nonempty DriverCycleWitness ∧
    finiteApplyFromGround .a1 ∧ finiteApplyFromGround deriver ∧
    Simulation .a1 deriver ∧ Nonempty (DEntry .a1 .a2) ∧
    ¬ ∃ endpoint : Form, Nonempty (DEntry deriver endpoint) ∧ Simulation .a2 endpoint :=
  ⟨full_axioms_hold, self_derivation_holds, ⟨cycleWitness⟩, ⟨1, rfl⟩, ⟨3, rfl⟩, rfl,
    ⟨unmatchedStep⟩, no_finite_reproduction⟩

def probe : IO Unit := do
  IO.println "START transport countermodel: grounded starts and witnessed two-step cycle"
  unless cycleWitness.path.length == 2 do
    throw (IO.userError "cycle lost its two actual steps")
  unless unmatchedStep.edges == [(Form.a1, Form.a2)] do
    throw (IO.userError "unmatched original step changed")
  unless (List.range 12).all (fun n =>
      let endpoint := Nat.repeat f2f n deriver
      endpoint == Form.a3 || endpoint == Form.a4) do
    throw (IO.userError "bounded probe left the proved invariant")
  IO.println "PASS transport countermodel: finite probe agrees with the universal no-reproduction theorem"

end HypermathTransportCountermodel
