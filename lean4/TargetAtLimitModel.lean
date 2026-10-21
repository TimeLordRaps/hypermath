import Hypermath.Trace
import Hypermath.TransportCountermodel
import Hypermath.NondegenerateCycle

/-!
An interpretation of all 44 current logical axiom clauses in which the
self-derivation target **holds** at the declared deriver position and no
congruence-preserving derivation step exists anywhere.

`FiniteActionCountermodel.lean` used to carry this pairing and gave it up. Its
deriver sat inside ground's two-cycle, where the target's two-step return
closes; declaring the deriver to be at the limit moved it onto a disjoint cycle,
and that file keeps a three-cycle there because a three-cycle is what makes its
action disagreement visible. Its header states the incompatibility: a position
with `f2f^2 x = x` has `f2f^1 x = f2f^3 x`, so no single model exhibits both the
action disagreement and the two-step return. That is an argument about those two
properties, not about the target, and the pairing lost there is recovered here
by giving up the action disagreement instead.

The limit's cycle is therefore two steps, `b0 -> b1 -> b0`, with the deriver at
its head as `axDeriverAtLimit` requires. The cycle's congruence classes are not
free: `axLimitIsLimit` says anything derivable from every finite position is
derivable from the limit, and the finite tower's tail `a1 -> a2 -> a1` occupies
classes `1` and `2`, so the limit's cycle must occupy those same two classes.
Two forms, two classes, and every apply edge changes class --- which is exactly
what leaves no preserving step to be found.

Because simulation is equality here and no form is fixed by apply, no simulation
edge exists at all --- so the typed cycle certificate of L3 has no inhabitant
while the target and its endpoint closure both hold. That refutes the converse of
`selfDerivationOfWitness`, which the research note recorded as not supplied.

What this interpretation shows is that the 44 clauses do not refute the target:
they hold together with it, and hold together with it while `D` is empty of
positive-length entries. It is not a proof of the target from the clauses, and
it establishes nothing about native adequacy.
-/

namespace HypermathTargetAtLimitModel

inductive Form where
  | a0 | a1 | a2 | b0 | b1
  deriving DecidableEq
instance : Inhabited Form := ⟨.a0⟩
def ground : Form := .a0
def f2f : Form → Form
  | .a0 => .a1
  | .a1 => .a2
  | .a2 => .a1
  | .b0 => .b1
  | .b1 => .b0
def Similar (_ _ : Form) : Prop := True
/-- The limit's two forms repeat the finite tail's two classes; `axLimitIsLimit`
is what requires it. -/
def congruenceClass : Form → Nat
  | .a0 => 0
  | .a1 => 1
  | .a2 => 2
  | .b0 => 1
  | .b1 => 2
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
/-- The deriver, at the limit. `ordinalLimit` is `.b0` below. -/
def deriver : Form := .b0
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
axioms, and none is claimed here. -/
def ordinalApply (_ _ : Form) : Form := ground

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
  axCongruentPathSymm : ∀ (p q : DerivationPath), congruentPath p q → congruentPath q p
  axCongruentTrans : ∀ (x y z : Form), Congruent x y → Congruent y z → Congruent x z
  axCoop : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axCoopComm : ∀ (a b : Form), Exists fun ca => Exists fun cab => And (Similar ca a) (And (Similar ca b) (And (Similar cab b) (And (Similar cab a) (Congruent ca cab))))
  axCoopIdentity : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axDeriverAtLimit : Eq deriver ordinalLimit
  axDiff : ∀ (x : Form), structDistinct (f2f x) ground
  axDiffCongruent : ∀ (x : Form), Not (Congruent (f2f x) ground)
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
  axSimilarRefl : ∀ (x : Form), Similar x x
  axSimilarSymm : ∀ (x y : Form), Similar x y → Similar y x
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
  axCongruentPathSymm := fun _ _ h => Eq.symm h
  axCongruentTrans := fun _ _ _ h k => Eq.trans h k
  axDiffCongruent := by
    intro x same
    change congruenceClass (f2f x) = congruenceClass ground at same
    cases x <;> simp [f2f, ground, congruenceClass] at same
  axSimilarRefl := fun _ => trivial
  axSimilarSymm := fun _ _ _ => trivial
  axBox := fun _ => trivial
  axComposeAssoc := fun p q r => (Nat.add_assoc p q r).symm
  axComposeIdentity := fun p => ⟨Nat.add_zero p, Nat.zero_add p⟩
  axComposeNonempty := fun _ _ => ⟨1, by simp [congruentPath, pathGround]⟩
  axCoop := fun a _ => ⟨a, trivial, trivial⟩
  axCoopComm := fun a _ => ⟨a, a, trivial, trivial, trivial, trivial, rfl⟩
  axCoopIdentity := fun a => ⟨a, trivial, rfl⟩
  axDeriverAtLimit := rfl
  axDiff := by
    intro x
    change ¬ (f2f x = ground)
    cases x <;> simp [f2f, ground]
  axFormClosesLoop := fun _ _ _ => trivial
  axGroundSelf := trivial
  axGroundSemanticsAx := trivial
  axGroundSubstanceAx := trivial
  axGroundSyntaxAx := trivial
  axLimitDerives := ⟨0, trivial, rfl⟩
  axLimitIsLimit := by
    intro y upper
    obtain ⟨n, reaches⟩ := upper 1
    change Congruent (Nat.repeat f2f n Form.a1) y at reaches
    rcases a_cycle_closed n with ha | ha
    · rw [ha] at reaches
      exact ⟨0, reaches⟩
    · rw [ha] at reaches
      exact ⟨1, reaches⟩
  axLimitNotFinite := by
    intro n same
    have inside := finite_position_in_ground_chain n
    change Nat.repeat f2f n ground = Form.b0 at same
    rw [same] at inside
    simp [GroundChain] at inside
  axSemanticsRequiresSyntax := fun _ _ => trivial
  axSeq := fun a _ => ⟨a, trivial, trivial⟩
  axSeqAsymm := fun a b different => ⟨a, b, trivial, trivial, trivial, trivial, different⟩
  axSeqIdentityL := fun a => ⟨a, trivial, rfl⟩
  axSeqIdentityR := fun a => ⟨a, trivial, rfl⟩
  axSim := fun _ => trivial
  axSubstanceRequiresSemantics := fun _ _ => trivial
  axSuccExtends := by
    intro x
    refine ⟨⟨1, rfl⟩, ?_⟩
    cases x <;> simp [ordinalSucc, Simulation, f2f]
  axSyntaxRequiresSubstance := fun _ _ => trivial
  closeDefinitionOpaque := fun _ _ => Iff.rfl
  closeDerivesOpaque := fun _ _ => Iff.rfl
  closeDischargeOpaque := fun _ _ => Iff.rfl
  closeFormClosureOpaque := fun _ => ⟨fun _ => ⟨trivial, trivial, trivial⟩, fun _ => trivial⟩
  closeSemanticsOpaque := fun _ => ⟨fun _ => rfl, fun _ => trivial⟩
  closeStructContinues := fun _ => ⟨fun _ => trivial, fun _ => trivial⟩
  closeStructDistinct := fun _ _ => Iff.rfl
  closeStructOrbits := fun _ => ⟨fun _ => trivial, fun _ => trivial⟩
  closeSubstanceOpaque := fun _ => ⟨fun _ => rfl, fun _ => trivial⟩
  closeSyntaxOpaque := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  filtrationCongSim := fun _ _ _ => trivial
  filtrationSimCong := by
    intro x y same
    change x = y at same
    rw [same]
    rfl
  traceLevels := by
    intro x
    refine ⟨trivial, fun _ => trivial, ?_⟩
    intro same
    change f2f x = x at same
    cases x <;> simp [f2f] at same
}

/-- The four conjuncts of the current native self-derivation proposition, under
this interpretation. -/
def selfDerivationTarget : Prop :=
  structContinues ground ground ∧
  (∀ x : Form, D x x) ∧
  (∀ p : DerivationPath,
    congruentPath (compose p pathGround) p ∧
    congruentPath (compose pathGround p) p) ∧
  Simulation (f2f (f2f deriver)) deriver

/-- All four conjuncts hold. The second is carried by empty traces, which is why
it survives alongside the absence of any preserving step below; the fourth is the
two-step return, which closes because the limit's cycle has two steps. -/
theorem self_derivation_target_holds : selfDerivationTarget :=
  ⟨trivial, fun x => ⟨.nil x⟩, fun p => ⟨Nat.add_zero p, Nat.zero_add p⟩, rfl⟩

theorem no_preserving_step : ∀ x y : Form, ¬ DStep x y := by
  intro x y edge
  rcases edge with ⟨rfl, congruent⟩
  cases x <;> simp [Congruent, congruenceClass, f2f] at congruent

theorem every_D_entry_is_empty {x y : Form} (path : DEntry x y) :
    Hypermath.Trace.length path = 0 := by
  cases path with
  | nil => rfl
  | cons edge tail => exact False.elim (no_preserving_step _ _ edge)

theorem no_nonzero_D_entry : ∀ x y : Form,
    ¬ ∃ path : DEntry x y, 0 < Hypermath.Trace.length path := by
  intro x y
  rintro ⟨path, positive⟩
  rw [every_D_entry_is_empty path] at positive
  exact Nat.lt_irrefl 0 positive

/-- Every clause, the original target, and no positive-length `DEntry` anywhere.
This is the pairing `FiniteActionCountermodel` carried under this name before the
deriver's position was declared; it is recovered here at the declared position
rather than restored to the old one. It is a non-refutation of the target by the
clauses, not a derivation of it. -/
theorem full_clauses_and_target_without_nonzero_D :
    FullAxioms ∧ selfDerivationTarget ∧
      (∀ x y : Form, ¬ ∃ path : DEntry x y, 0 < Hypermath.Trace.length path) :=
  ⟨full_axioms_hold, self_derivation_target_holds, no_nonzero_D_entry⟩

-- The typed cycle certificate of L3, under this interpretation.
--
-- `selfDerivationOfWitness` sends the certificate to the target. The converse
-- was recorded as not supplied. It is refutable here, and the refutation needs
-- this model rather than either of the others: it needs the target to hold, and
-- it needs no simulation edge to exist.

/-- A native apply edge retaining simulation at that edge. -/
def SimulationStep (x y : Form) : Prop := y = f2f x ∧ Simulation y x

abbrev SimulationEntry (x y : Form) := Hypermath.Trace SimulationStep x y

/-- Endpoint closure of the deriver's two-step cycle: the certificate's third
field, and the target's fourth conjunct. -/
def driverCycleClaim : Prop := Simulation (f2f (f2f deriver)) deriver

/-- The certificate retains two actual edges as well as endpoint closure. -/
structure DriverCycleWitness where
  path : SimulationEntry deriver (f2f (f2f deriver))
  length_two : Hypermath.Trace.length path = 2
  closes : driverCycleClaim

/-- Simulation is equality here and `f2f` fixes no form, so an edge asking for
both `y = f2f x` and `y = x` asks for a fixed point. -/
theorem no_simulation_step : ∀ x y : Form, ¬ SimulationStep x y := by
  intro x y edge
  rcases edge with ⟨rfl, same⟩
  cases x <;> simp [Simulation, f2f] at same

theorem every_simulation_entry_is_empty {x y : Form} (path : SimulationEntry x y) :
    Hypermath.Trace.length path = 0 := by
  cases path with
  | nil => rfl
  | cons edge tail => exact False.elim (no_simulation_step _ _ edge)

/-- The certificate does not exist here, and what is missing is only its path.
Its closure field is available --- `driverCycleClaim` holds --- and so is the
whole target the closure yields. -/
theorem no_driver_cycle_witness : ¬ Nonempty DriverCycleWitness := by
  rintro ⟨witness⟩
  exact Nat.noConfusion
    (witness.length_two.symm.trans (every_simulation_entry_is_empty witness.path))

/-- Every clause, the target, endpoint closure, and no cycle certificate. So the
target does not yield the certificate: the implication proved in the other
direction has no converse, and a proof of the target leaves the retained edges
still to be supplied. This is what the certificate's own docstring claims when it
calls itself stronger than the target, stated as a separation rather than as a
reading of the definitions. -/
theorem target_does_not_yield_a_cycle_certificate :
    FullAxioms ∧ selfDerivationTarget ∧ driverCycleClaim ∧
      ¬ Nonempty DriverCycleWitness :=
  ⟨full_axioms_hold, self_derivation_target_holds, rfl, no_driver_cycle_witness⟩

/-- The proposed correspondence law without its finiteness restriction, under
this interpretation. It holds here by definition: `ordinalSucc` is `f2f`. -/
def SuccessorAgreement : Prop := ∀ x : Form, ordinalSucc x = f2f x

theorem successor_agreement_holds : SuccessorAgreement := fun _ => rfl

/-- The transport countermodel chooses the opposite, and says so in its own
docstring: its successor "does not assume successor equals primitive forming". -/
theorem transport_successor_disagrees :
    ¬ ∀ x : HypermathTransportCountermodel.Form,
        HypermathTransportCountermodel.ordinalSucc x
          = HypermathTransportCountermodel.f2f x := by
  intro agreement
  exact absurd (agreement .a1) (by decide)

/-- **The certificate's verdict tracks the successor law, in both models.**
`no_driver_cycle_witness_of_successor_agreement` proves in the theory that the
two are incompatible, with no hypothesis about where the deriver sits --- which
is what distinguishes it from the finite obstruction the declared position
evades. The two models realise the two sides: all 44 clauses with apply as
successor and no certificate, and the 39 pre-closure clauses with a successor
that is not apply and a certificate (the transport side violates
`axDiffCongruent`). So the clauses decide neither, and the open question
about the deriver's cycle is the question of what apply means. -/
theorem certificate_tracks_successor_agreement :
    (FullAxioms ∧ SuccessorAgreement ∧ ¬ Nonempty DriverCycleWitness) ∧
    (HypermathTransportCountermodel.FullAxioms ∧
      (¬ ∀ x : HypermathTransportCountermodel.Form,
          HypermathTransportCountermodel.ordinalSucc x
            = HypermathTransportCountermodel.f2f x) ∧
      Nonempty HypermathTransportCountermodel.DriverCycleWitness) :=
  ⟨⟨full_axioms_hold, successor_agreement_holds, no_driver_cycle_witness⟩,
   ⟨HypermathTransportCountermodel.full_axioms_hold, transport_successor_disagrees,
    ⟨HypermathTransportCountermodel.cycleWitness⟩⟩⟩

/-- **The cycle certificate is independent of the 39 pre-closure clauses.**
Whether it is independent of all 44 is open here: both inhabited sides
(`HypermathTransportCountermodel`, `HypermathNondegenerateCycleModel`) read
`=~` as total and so violate `axDiffCongruent`. The transport
countermodel satisfies them with an inhabited certificate; this one satisfies
them with none. So no proof of the certificate can be read off the declared
clauses, and no refutation of it can either --- the question the development
leaves open is open in the strong sense, not merely unanswered.

The pairing is the same idiom as `congruent_symmetry_independent`: two carriers,
each with its own reading of every clause, opposite verdicts on one proposition.
Here the two carriers differ in the length of the cycle at the deriver's
position, which no clause mentions. -/
theorem cycle_certificate_independent :
    (HypermathTransportCountermodel.FullAxioms ∧
      Nonempty HypermathTransportCountermodel.DriverCycleWitness) ∧
    (FullAxioms ∧ ¬ Nonempty DriverCycleWitness) :=
  ⟨⟨HypermathTransportCountermodel.full_axioms_hold,
    ⟨HypermathTransportCountermodel.cycleWitness⟩⟩,
   ⟨full_axioms_hold, no_driver_cycle_witness⟩⟩

/-- Transitivity of this model's `Simulation`, stated here because the theory's
`Hypermath.SimulationTransitive` is about a different carrier. -/
def SimulationTransitive : Prop :=
  ∀ x y z : Form, Simulation x y → Simulation y z → Simulation x z

theorem simulation_is_transitive : SimulationTransitive :=
  fun _ _ _ first second => first.trans second

theorem transport_simulation_is_transitive :
    ∀ x y z : HypermathTransportCountermodel.Form,
      HypermathTransportCountermodel.Simulation x y →
      HypermathTransportCountermodel.Simulation y z →
      HypermathTransportCountermodel.Simulation x z :=
  fun _ _ _ first second =>
    HypermathTransportCountermodel.simulation_is_equivalence.trans first second

/-- **The independence survives adding transitivity to the clauses.** By
`Hypermath.driverCycleWitness_iff_of_transitive` a transitive `Simulation` makes
the certificate equivalent to its two retained edges, the endpoint closure being
free; both models here are transitive, and they still disagree. So the content
the certificate has over the target is the edges, and a reader who hoped the
closure was the hard part can stop hoping: the closure is the part the target
already gives. -/
theorem cycle_certificate_independent_under_transitivity :
    (HypermathTransportCountermodel.FullAxioms ∧
      (∀ x y z : HypermathTransportCountermodel.Form,
        HypermathTransportCountermodel.Simulation x y →
        HypermathTransportCountermodel.Simulation y z →
        HypermathTransportCountermodel.Simulation x z) ∧
      Nonempty HypermathTransportCountermodel.DriverCycleWitness) ∧
    (FullAxioms ∧ SimulationTransitive ∧ ¬ Nonempty DriverCycleWitness) :=
  ⟨⟨HypermathTransportCountermodel.full_axioms_hold, transport_simulation_is_transitive,
    ⟨HypermathTransportCountermodel.cycleWitness⟩⟩,
   ⟨full_axioms_hold, simulation_is_transitive, no_driver_cycle_witness⟩⟩

/-- **The transport countermodel's certificate is at a fixed point.** Apply
fixes its deriver, so by `Hypermath.driverCycleWitness_of_fixed_deriver` its
certificate is available from reflexivity of `Simulation` there and nothing
else: the trace is the deriver standing still twice. For most of this
development that was the only inhabited certificate anywhere, which makes the
independence above true but weaker than it reads --- one side of the pairing
was not exhibiting a cycle at all. -/
theorem transport_cycle_is_degenerate :
    HypermathTransportCountermodel.f2f HypermathTransportCountermodel.deriver
      = HypermathTransportCountermodel.deriver := rfl

/-- Apply moves the deriver here, so this side of the pairing is nondegenerate
already. -/
theorem apply_moves_the_deriver : f2f deriver ≠ deriver := by decide

/-- **The independence survives restricting to cycles that move.** Replacing the
transport countermodel with `HypermathNondegenerateCycleModel`, whose limit sits
on a genuine two-cycle `l0 -> l1 -> l0`, gives two models in which apply moves
the deriver, every one of the 39 pre-closure clauses holds, and the certificate
is inhabited on one side and refuted on the other. The inhabited side violates
`axDiffCongruent`. So the independence is not an artefact of a
fixed point: it is not decided even among the models where the cycle is real. -/
theorem cycle_certificate_independent_nondegenerately :
    (HypermathNondegenerateCycleModel.FullAxioms ∧
      HypermathNondegenerateCycleModel.f2f HypermathNondegenerateCycleModel.deriver
        ≠ HypermathNondegenerateCycleModel.deriver ∧
      Nonempty HypermathNondegenerateCycleModel.DriverCycleWitness) ∧
    (FullAxioms ∧ f2f deriver ≠ deriver ∧ ¬ Nonempty DriverCycleWitness) :=
  ⟨HypermathNondegenerateCycleModel.nondegenerate_cycle_with_all_clauses,
   ⟨full_axioms_hold, apply_moves_the_deriver, no_driver_cycle_witness⟩⟩

/-- The deriver is outside the finite tower, as its declared position requires:
the tower stays in ground's chain and the limit is not in it. -/
theorem deriver_is_not_finite : ¬ ∃ n : Nat, Nat.repeat f2f n ground = deriver := by
  rintro ⟨n, reaches⟩
  have inside := finite_position_in_ground_chain n
  rw [reaches] at inside
  simp [GroundChain, deriver] at inside

#print axioms full_axioms_hold
#print axioms congruence_is_equivalence
#print axioms self_derivation_target_holds
#print axioms no_preserving_step
#print axioms every_D_entry_is_empty
#print axioms no_nonzero_D_entry
#print axioms full_clauses_and_target_without_nonzero_D
#print axioms deriver_is_not_finite
#print axioms no_simulation_step
#print axioms every_simulation_entry_is_empty
#print axioms no_driver_cycle_witness
#print axioms target_does_not_yield_a_cycle_certificate
#print axioms cycle_certificate_independent
#print axioms successor_agreement_holds
#print axioms transport_successor_disagrees
#print axioms certificate_tracks_successor_agreement
#print axioms simulation_is_transitive
#print axioms transport_simulation_is_transitive
#print axioms cycle_certificate_independent_under_transitivity
#print axioms transport_cycle_is_degenerate
#print axioms apply_moves_the_deriver
#print axioms cycle_certificate_independent_nondegenerately

def probe : IO Unit := do
  IO.println "START target-at-limit model: two-step limit cycle with no preserving step"
  unless f2f (f2f deriver) == deriver do
    throw (IO.userError "the limit's cycle stopped closing in two steps")
  unless (List.range 8).all (fun n =>
      let position := Nat.repeat f2f n ground
      position == Form.a0 || position == Form.a1 || position == Form.a2) do
    throw (IO.userError "the finite tower left ground's chain")
  unless [Form.a0, Form.a1, Form.a2, Form.b0, Form.b1].all
      (fun x => congruenceClass (f2f x) != congruenceClass x) do
    throw (IO.userError "an apply edge stopped changing its congruence class")
  unless [Form.a0, Form.a1, Form.a2, Form.b0, Form.b1].all (fun x => f2f x != x) do
    throw (IO.userError "apply acquired a fixed point, so a simulation edge exists")
  IO.println "PASS target-at-limit model: target holds and no apply edge preserves congruence"

#eval probe

end HypermathTargetAtLimitModel
