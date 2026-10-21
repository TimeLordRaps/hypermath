import Hypermath.Trace

/-!
# A model where the deriver's cycle actually moves

`Hypermath/TransportCountermodel.lean` supplies the only inhabited
`DriverCycleWitness` in the development, and apply fixes its deriver:
`f2f .limit = .limit`, so the two-step return returns from where it never left.
A certificate at a fixed point is available from reflexivity of `Simulation`
alone, so it is evidence about the clauses and not about the cycle.

Here the limit sits on a genuine two-cycle `l0 -> l1 -> l0` with the deriver at
its head, every one of the 39 pre-closure clauses holds, and the certificate
is inhabited. So a cycle that moves is consistent with those clauses, which is the strongest
positive statement the development can make about the deriver's cycle short of
proving it.

Both forms of the limit cycle share one semantic class. That is what the other
model cannot do: `HypermathTargetAtLimitModel` reads `Simulation` as equality,
so the two forms of its limit cycle are never simulated by one another whatever
their classes. Here `Simulation` is agreement of `semanticClass`, and the
classes are free because `Derives` is total, so nothing forces the cycle's two
forms apart.

The model is deliberately silent about transport: `Congruent` is total, so it
says nothing about reproduction, and `Hypermath/TransportCountermodel.lean`
remains the subject of that question.

Totality of `Congruent` also means this is a model of the 39 clauses that
precede the closing clauses of L0 §VIII.b and L2 §II, not of the current
theory: `axDiffCongruent` refutes it, as `nondegenerate_violates_axDiffCongruent`
records.
-/

namespace HypermathNondegenerateCycleModel

inductive Form where
  | a0 | a1 | a2 | a3 | a4 | l0 | l1
  deriving DecidableEq

instance : Inhabited Form := ⟨.a0⟩
def ground : Form := .a0

/-- The finite tower runs into the `a3`/`a4` orbit; the limit cycle is disjoint
from it and is itself a two-cycle. -/
def f2f : Form → Form
  | .a0 => .a1
  | .a1 => .a2
  | .a2 => .a3
  | .a3 => .a4
  | .a4 => .a3
  | .l0 => .l1
  | .l1 => .l0

def Similar (_ _ : Form) : Prop := True
def Congruent (_ _ : Form) : Prop := True

/-- The limit cycle's two forms share a class. Nothing forces them apart: the
clauses constrain this assignment only through `axDiff`, `axSuccExtends` and
`axLimitNotFinite`, and all three are about telling forms apart, never about
telling the two halves of one cycle apart. -/
def semanticClass : Form → Nat
  | .a0 => 0
  | .a1 | .a3 | .a4 => 1
  | .a2 => 2
  | .l0 | .l1 => 3

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

/-- The deriver, at the limit, on a cycle that moves. -/
def deriver : Form := .l0
def ordinalLimit : Form := .l0

abbrev DerivationPath := Nat
def pathGround : DerivationPath := 0
def compose (p q : DerivationPath) : DerivationPath := p + q
def congruentPath (p q : DerivationPath) : Prop := p = q
def pathStart (_ : DerivationPath) : Form := ground
def pathEnd (_ : DerivationPath) : Form := ordinalLimit

/-- Only the declared successor clauses are required; this is not ordinal
arithmetic, and in particular it is not apply. -/
def ordinalSucc : Form → Form
  | .a0 => .a1
  | _ => .a0

def SimulationStep (x y : Form) : Prop := y = f2f x ∧ Simulation y x
abbrev SimulationEntry (x y : Form) := Hypermath.Trace SimulationStep x y
def driverCycleClaim : Prop := Simulation (f2f (f2f deriver)) deriver

/-- The same strengthened certificate fields as the native driver witness. -/
structure DriverCycleWitness where
  path : SimulationEntry deriver (f2f (f2f deriver))
  length_two : Hypermath.Trace.length path = 2
  closes : driverCycleClaim

def InLimitCycle (x : Form) : Prop := x = .l0 ∨ x = .l1

theorem forming_stays_outside (x : Form) (outside : ¬ InLimitCycle x) :
    ¬ InLimitCycle (f2f x) := by
  cases x <;> simp_all [InLimitCycle, f2f]

theorem finite_position_outside (n : Nat) :
    ¬ InLimitCycle (Nat.repeat f2f n ground) := by
  induction n with
  | zero => simp [InLimitCycle, ground, Nat.repeat]
  | succ n ih => exact forming_stays_outside _ ih

theorem simulation_limit_iff (x : Form) :
    Simulation x ordinalLimit ↔ InLimitCycle x := by
  cases x <;> simp [Simulation, semanticClass, ordinalLimit, InLimitCycle]

/-- Exact current logical clause types; no admitted theorem or prose law is
included. This is the same list the other models certify. -/
structure FullAxioms : Prop where
  axBox : ∀ (x : Form), structOrbits (f2f (f2f x)) x
  axComposeAssoc : ∀ (p q r : DerivationPath), congruentPath (compose p (compose q r)) (compose (compose p q) r)
  axComposeIdentity : ∀ (p : DerivationPath), And (congruentPath (compose p pathGround) p) (congruentPath (compose pathGround p) p)
  axComposeNonempty : Form → Form → Exists fun p => Not (congruentPath p pathGround)
  axCoop : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axCoopComm : ∀ (a b : Form), Exists fun ca => Exists fun cab => And (Similar ca a) (And (Similar ca b) (And (Similar cab b) (And (Similar cab a) (Congruent ca cab))))
  axCoopIdentity : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axDeriverAtLimit : Eq deriver ordinalLimit
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
    exact finite_position_outside n ((simulation_limit_iff _).mp same)
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
  axDeriverAtLimit := rfl
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

/-- Two real edges, `l0 -> l1` and `l1 -> l0`, each retaining simulation because
the two forms share a class, and the return closing at the deriver. -/
def cycleWitness : DriverCycleWitness :=
  ⟨.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _)), rfl, rfl⟩

theorem cycle_has_two_steps : Hypermath.Trace.length cycleWitness.path = 2 := rfl

/-- **The cycle moves.** This is the property the transport countermodel's
witness lacks, and it is the whole point of this model. -/
theorem apply_moves_the_deriver : f2f deriver ≠ deriver := by decide

/-- **A cycle that moves is consistent with the 39 pre-closure clauses.** -/
theorem nondegenerate_cycle_with_all_clauses :
    FullAxioms ∧ f2f deriver ≠ deriver ∧ Nonempty DriverCycleWitness :=
  ⟨full_axioms_hold, apply_moves_the_deriver, ⟨cycleWitness⟩⟩

/-- **The closing clause `axDiffCongruent` refutes this model**, because its
`=~` is total. -/
theorem nondegenerate_violates_axDiffCongruent :
    ¬ ∀ x : Form, ¬ Congruent (f2f x) ground :=
  fun closing => closing ground trivial

end HypermathNondegenerateCycleModel
