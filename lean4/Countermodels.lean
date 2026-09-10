import Hypermath.Trace

/- Finite countermodels to selected claimed consequences of the L0/L1 axiom
   clauses. Only the generic constructive Trace implementation is imported;
   no production Form parameters or logical axioms are used. The Bool model
   tests reverse filtration, directionality, and the promised endpoint cycle.
   The separate Fin 3 model tests the now-defined congruence-preserving D.
   Neither model covers every later L2/L3 clause or establishes consistency
   of the intended complete theory. There are no admitted proofs here. -/

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

/-- The prefix does not provide the promised simulation cycle. -/
theorem driver_cycle_claim_fails : ¬ Simulation (f2f (f2f deriver)) deriver := by
  simp [Simulation, f2f, deriver]

namespace PreservingTrace

/-- Three Forms with an exact two-step cycle away from ground. -/
def ground : Fin 3 := 0
def f2f (x : Fin 3) : Fin 3 := if x = 1 then 2 else 1
def Similar (_ _ : Fin 3) : Prop := True
def Congruent (x y : Fin 3) : Prop := x = y
def Simulation (x y : Fin 3) : Prop := x = y
def structContinues (_ _ : Fin 3) : Prop := True
def structDistinct (x y : Fin 3) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Fin 3) : Prop := True
def HMSyntax (_ : Fin 3) : Prop := True
def Substance (_ : Fin 3) : Prop := True
def Semantics (_ : Fin 3) : Prop := True
def FormClosure (_ : Fin 3) : Prop := True
def Derives (x y : Fin 3) : Prop := ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
def Discharge (c e : Fin 3) : Prop := Derives e c
def Definition (n x : Fin 3) : Prop := Derives n x
def deriver : Fin 3 := 1

/-- The same 24 logical prefix clauses, interpreted on Fin 3. In particular,
    Derives has its stipulated finite endpoint-reachability interpretation;
    it is not silently identified with the stricter edge-preserving D. -/
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
  all_goals decide

/-- Exactly the production DStep shape, with this model's operations. -/
def DStep (x y : Fin 3) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Fin 3) := Hypermath.Trace DStep x y
def D (x y : Fin 3) : Prop := Nonempty (DEntry x y)

theorem no_congruent_step : ∀ x : Fin 3, ¬ Congruent (f2f x) x := by
  unfold Congruent f2f
  decide

theorem no_step {x y : Fin 3} (edge : DStep x y) : False := by
  exact no_congruent_step x (edge.1 ▸ edge.2)

/-- Zero-step reflexivity survives; every positive step is excluded by evidence. -/
theorem trace_is_zero {x y : Fin 3} (path : DEntry x y) :
    x = y ∧ path.length = 0 := by
  cases path with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons edge _ => exact False.elim (no_step edge)

theorem d_iff_equal (x y : Fin 3) : D x y ↔ x = y := by
  constructor
  · intro ⟨path⟩
    exact (trace_is_zero path).1
  · intro h
    subst y
    exact ⟨Hypermath.Trace.nil x⟩

end PreservingTrace

/-- The preserving-trace countermodel satisfies all 24 logical prefix clauses. -/
theorem preserving_prefix_axioms_hold : PreservingTrace.PrefixAxioms :=
  PreservingTrace.prefixAxioms_hold

/-- The actual trace-defined D need not span ground, despite the prefix axioms. -/
theorem d_spans_ground_claim_fails :
    ¬ (∀ y : Fin 3, PreservingTrace.D PreservingTrace.ground y) := by
  intro spans
  have impossible := (PreservingTrace.d_iff_equal PreservingTrace.ground 1).mp (spans 1)
  exact (by decide : PreservingTrace.ground ≠ (1 : Fin 3)) impossible

/-- Even exact endpoint simulation after two applications does not supply a
    positive-length congruence-preserving trace through the intermediate Form. -/
theorem driver_endpoint_cycle_without_positive_trace :
    PreservingTrace.Simulation
      (PreservingTrace.f2f (PreservingTrace.f2f PreservingTrace.deriver))
      PreservingTrace.deriver ∧
    ¬ (∃ path : PreservingTrace.DEntry PreservingTrace.deriver PreservingTrace.deriver,
      0 < path.length) := by
  constructor
  · unfold PreservingTrace.Simulation PreservingTrace.f2f PreservingTrace.deriver
    decide
  · intro ⟨path, positive⟩
    rw [(PreservingTrace.trace_is_zero path).2] at positive
    exact Nat.not_lt_zero _ positive

#print axioms prefixAxioms_hold
#print axioms reverse_filtration_fails
#print axioms directionality_claim_fails
#print axioms driver_cycle_claim_fails
#print axioms preserving_prefix_axioms_hold
#print axioms d_spans_ground_claim_fails
#print axioms driver_endpoint_cycle_without_positive_trace

end HypermathCountermodel
