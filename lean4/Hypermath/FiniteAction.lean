import Hypermath.L3Ordinatics

/-!
# Host-level finite numeral actions

Equal numeral representations can name an exact iteration action only when
they induce the same iteration on every starting value. This module proves
that criterion and its converse using classical choice of a representative.
The all-value criterion concerns generalized action on arbitrary Forms.
On the finite ground orbit itself, iteration and addition respect numeral
equality unconditionally; they do not require the all-value criterion.
Lean reports `Classical.choice`, propositional extensionality (`propext`), and
quotient soundness (`Quot.sound`) for that noncomputable existence construction.
The generic constructions and their native-parameter specializations do not
establish native adequacy or identify an action with opaque `ordinalApply`.
-/

universe u

namespace Hypermath.FiniteAction

variable {α : Type u}

/-- Equality of finite numeral representations at the specified base. -/
def NumeralEq (step : α → α) (base : α) (m n : Nat) : Prop :=
  Nat.repeat step m base = Nat.repeat step n base

theorem numeralEq_refl (step : α → α) (base : α) (n : Nat) :
    NumeralEq step base n n := rfl

theorem numeralEq_symm {step : α → α} {base : α} {m n : Nat}
    (equal : NumeralEq step base m n) : NumeralEq step base n m := equal.symm

theorem numeralEq_trans {step : α → α} {base : α} {m n k : Nat}
    (first : NumeralEq step base m n) (second : NumeralEq step base n k) :
    NumeralEq step base m k := first.trans second

/-- The host-level quotient relation identifies exactly equal numeral values. -/
def numeralSetoid (step : α → α) (base : α) : Setoid Nat where
  r := NumeralEq step base
  iseqv := ⟨numeralEq_refl step base, numeralEq_symm, numeralEq_trans⟩

/-- Host iteration counts add under composition. -/
theorem iteration_add (step : α → α) (m n : Nat) (x : α) :
    Nat.repeat step (m + n) x = Nat.repeat step n (Nat.repeat step m x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

/-- Iterates of the same function commute; no injectivity is needed. -/
theorem iteration_commute (step : α → α) (m n : Nat) (x : α) :
    Nat.repeat step m (Nat.repeat step n x) =
      Nat.repeat step n (Nat.repeat step m x) :=
  (iteration_add step n m x).symm.trans
    ((congrArg (fun count => Nat.repeat step count x) (Nat.add_comm n m)).trans
      (iteration_add step m n x))

/-- Equal numerals always act equally on finite-orbit starting values.
This restricted conclusion requires no all-value compatibility assumption. -/
theorem action_eq_on_finite_orbit {step : α → α} {base : α} {m n : Nat}
    (equal : NumeralEq step base m n) (k : Nat) :
    Nat.repeat step m (Nat.repeat step k base) =
      Nat.repeat step n (Nat.repeat step k base) :=
  (iteration_commute step m k base).trans
    ((congrArg (Nat.repeat step k) equal).trans
      (iteration_commute step n k base).symm)

/-- The numeral-equivalence kernel respects addition in both arguments. -/
theorem numeralEq_add {step : α → α} {base : α} {m n p q : Nat}
    (left : NumeralEq step base m n) (right : NumeralEq step base p q) :
    NumeralEq step base (m + p) (n + q) :=
  (iteration_add step m p base).trans
    ((congrArg (Nat.repeat step p) left).trans
      ((action_eq_on_finite_orbit right n).trans (iteration_add step n q base).symm))

/-- The numeral-equivalence kernel also respects multiplication by a fixed
natural count. Multiplication here is repeated host-level addition. -/
theorem numeralEq_mul_right {step : α → α} {base : α} {m n : Nat}
    (equal : NumeralEq step base m n) (k : Nat) :
    NumeralEq step base (m * k) (n * k) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Nat.mul_succ] using numeralEq_add ih equal

/-- The numeral-equivalence kernel respects multiplication in both arguments. -/
theorem numeralEq_mul {step : α → α} {base : α} {m n p q : Nat}
    (left : NumeralEq step base m n) (right : NumeralEq step base p q) :
    NumeralEq step base (m * p) (n * q) :=
  numeralEq_trans (numeralEq_mul_right left p)
    (by simpa [Nat.mul_comm] using numeralEq_mul_right right n)

/-- Representative independence for an exact action on every starting value. -/
def FiniteActionCompatible (step : α → α) (base : α) : Prop :=
  ∀ m n, NumeralEq step base m n → ∀ x, Nat.repeat step m x = Nat.repeat step n x

/-- An action whose value on every represented numeral is exact iteration. -/
def ExactFiniteAction (step : α → α) (base : α) (action : α → α → α) : Prop :=
  ∀ n x, action (Nat.repeat step n base) x = Nat.repeat step n x

theorem exact_implies_compatible {step : α → α} {base : α} {action : α → α → α}
    (agreement : ExactFiniteAction step base action) : FiniteActionCompatible step base := by
  intro m n equal x
  exact (agreement m x).symm.trans
    ((congrArg (fun numeral => action numeral x) equal).trans (agreement n x))

/-- A host-level choice of finite representative; non-numerals act as identity.
This definition uses classical choice and makes no computability claim. -/
noncomputable def chosenAction (step : α → α) (base : α) (numeral x : α) : α := by
  classical
  exact if member : ∃ n, Nat.repeat step n base = numeral then
    Nat.repeat step (Classical.choose member) x
  else x

theorem chosen_action_exact {step : α → α} {base : α}
    (compatible : FiniteActionCompatible step base) :
    ExactFiniteAction step base (chosenAction step base) := by
  classical
  intro n x
  have member : ∃ m, Nat.repeat step m base = Nat.repeat step n base := ⟨n, rfl⟩
  unfold chosenAction
  rw [dif_pos member]
  exact compatible (Classical.choose member) n (Classical.choose_spec member) x

/-- Host-level existence, with a classically chosen action in the forward direction. -/
theorem compatible_iff_exists_exact (step : α → α) (base : α) :
    FiniteActionCompatible step base ↔ ∃ action, ExactFiniteAction step base action := by
  constructor
  · intro compatible
    exact ⟨chosenAction step base, chosen_action_exact compatible⟩
  · intro ⟨action, agreement⟩
    exact exact_implies_compatible agreement

/-- Representative independence observed through an explicitly supplied relation. -/
def RelationActionCompatible (relation : α → α → Prop) (step : α → α) (base : α) : Prop :=
  ∀ m n, NumeralEq step base m n → ∀ x,
    relation (Nat.repeat step m x) (Nat.repeat step n x)

/-- Host-level action agreement through a supplied relation, which need not be equality. -/
def CongruentActionAgreement (relation : α → α → Prop) (step : α → α)
    (base : α) (action : α → α → α) : Prop :=
  ∀ n x, relation (action (Nat.repeat step n base) x) (Nat.repeat step n x)

/-- Relational agreement implies compatibility when symmetry and transitivity
are provided. No such laws are assumed for native `Hypermath.Congruent`. -/
theorem agreement_implies_relation_compatible
    {relation : α → α → Prop} {step : α → α} {base : α} {action : α → α → α}
    (symmetric : ∀ {x y}, relation x y → relation y x)
    (transitive : ∀ {x y z}, relation x y → relation y z → relation x z)
    (agreement : CongruentActionAgreement relation step base action) :
    RelationActionCompatible relation step base := by
  intro m n equal x
  have shared : relation (action (Nat.repeat step m base) x) (Nat.repeat step n x) :=
    Eq.mpr (congrArg (fun numeral => relation (action numeral x) (Nat.repeat step n x)) equal)
      (agreement n x)
  exact transitive (symmetric (agreement m x)) shared

end Hypermath.FiniteAction

namespace Hypermath

/-- Equality of existing native finite numeral Forms, viewed at the host level. -/
def FiniteNumeralEq (m n : Nat) : Prop := finiteApplyPosition m = finiteApplyPosition n

theorem finiteNumeralEq_iff_generic (m n : Nat) :
    FiniteNumeralEq m n ↔ FiniteAction.NumeralEq f2f ground m n := Iff.rfl

/-- Unconditional host-level agreement on existing finite native starting Forms. -/
theorem finiteNumeralEq_action_on_finite_orbit {m n : Nat}
    (equal : FiniteNumeralEq m n) (k : Nat) :
    Nat.repeat f2f m (finiteApplyPosition k) = Nat.repeat f2f n (finiteApplyPosition k) :=
  FiniteAction.action_eq_on_finite_orbit equal k

/-- Finite numeral addition descends without an all-Form action or injectivity claim. -/
theorem finiteNumeralEq_add {m n p q : Nat}
    (left : FiniteNumeralEq m n) (right : FiniteNumeralEq p q) :
    FiniteNumeralEq (m + p) (n + q) :=
  FiniteAction.numeralEq_add left right

/-- Finite numeral multiplication descends without assuming numeral
injectivity or an action on Forms outside the finite ground orbit. -/
theorem finiteNumeralEq_mul {m n p q : Nat}
    (left : FiniteNumeralEq m n) (right : FiniteNumeralEq p q) :
    FiniteNumeralEq (m * p) (n * q) :=
  FiniteAction.numeralEq_mul left right

/-- The existing finite ground orbit, retaining its finite-generation witness. -/
def FiniteOrbit := {x : Form // finiteApplyFromGround x}

/-- Encode a natural count as its witnessed native finite-orbit position. -/
noncomputable def finiteOrbitEncode (n : Nat) : FiniteOrbit :=
  ⟨finiteApplyPosition n, finiteApplyPositionMember n⟩

/-- Every witnessed finite-orbit Form has at least one host count. -/
theorem finiteOrbitEncode_surjective :
    ∀ x : FiniteOrbit, ∃ n : Nat, finiteOrbitEncode n = x := by
  intro x
  obtain ⟨n, hn⟩ := x.property
  refine ⟨n, Subtype.ext ?_⟩
  exact hn

/-- A classically selected count from the witness carried by a finite-orbit Form. -/
noncomputable def finiteOrbitDecode (x : FiniteOrbit) : Nat :=
  Classical.choose x.property

theorem finiteOrbitDecode_spec (x : FiniteOrbit) :
    finiteApplyPosition (finiteOrbitDecode x) = x.val :=
  Classical.choose_spec x.property

/-- The one additional proposition needed to identify this orbit with Nat. -/
def FiniteOrbitInjective : Prop :=
  ∀ {m n : Nat}, finiteApplyPosition m = finiteApplyPosition n → m = n

/-- A two-sided correspondence between host natural numbers and witnessed
finite-orbit Forms. This local structure avoids importing a larger library. -/
structure FiniteOrbitEquivalence where
  toOrbit : Nat → FiniteOrbit
  toNat : FiniteOrbit → Nat
  toNat_toOrbit : ∀ n : Nat, toNat (toOrbit n) = n
  toOrbit_toNat : ∀ x : FiniteOrbit, toOrbit (toNat x) = x

/-- Under the explicit injectivity obligation, the finite ground orbit has a
set-level two-sided correspondence with the natural numbers. The current source
axioms do not discharge the hypothesis or establish arithmetic preservation. -/
noncomputable def finiteOrbitEquivalence
    (injective : FiniteOrbitInjective) : FiniteOrbitEquivalence where
  toOrbit := finiteOrbitEncode
  toNat := finiteOrbitDecode
  toNat_toOrbit := by
    intro n
    apply injective
    exact finiteOrbitDecode_spec (finiteOrbitEncode n)
  toOrbit_toNat := by
    intro x
    apply Subtype.ext
    exact finiteOrbitDecode_spec x

@[simp] theorem finiteOrbitEquivalence_apply
    (injective : FiniteOrbitInjective) (n : Nat) :
    (finiteOrbitEquivalence injective).toOrbit n = finiteOrbitEncode n := rfl

/-- The conditional correspondence exposes both inverse laws as one reviewed
set-level boundary. -/
theorem finiteOrbitEquivalence_laws (injective : FiniteOrbitInjective) :
    (∀ n : Nat, finiteOrbitDecode (finiteOrbitEncode n) = n) ∧
    (∀ x : FiniteOrbit, finiteOrbitEncode (finiteOrbitDecode x) = x) := by
  constructor
  · exact (finiteOrbitEquivalence injective).toNat_toOrbit
  · exact (finiteOrbitEquivalence injective).toOrbit_toNat

/-- The native-parameter compatibility obligation; it is not assumed or derived here. -/
def FiniteActionCompatible : Prop :=
  ∀ m n, FiniteNumeralEq m n → ∀ x, Nat.repeat f2f m x = Nat.repeat f2f n x

/-- Injective finite numeral representation is sufficient for representative
independence on every starting Form. The current axioms do not prove the premise. -/
theorem finiteOrbitInjective_implies_actionCompatible
    (injective : FiniteOrbitInjective) : FiniteActionCompatible := by
  intro m n equal x
  have indices : m = n := injective equal
  cases indices
  rfl

/-- Exact host action agreement on the existing `finiteApplyPosition` representation. -/
def ExactFiniteAction (action : Form → Form → Form) : Prop :=
  ∀ n x, action (finiteApplyPosition n) x = Nat.repeat f2f n x

theorem exactFiniteAction_implies_compatible {action : Form → Form → Form}
    (agreement : ExactFiniteAction action) : FiniteActionCompatible :=
  FiniteAction.exact_implies_compatible agreement

/-- A classical host construction using native parameters; agreement with
`ordinalApply` and native adequacy remain separate obligations. -/
noncomputable def hostFiniteAction : Form → Form → Form := FiniteAction.chosenAction f2f ground

theorem hostFiniteAction_exact (compatible : FiniteActionCompatible) :
    ExactFiniteAction hostFiniteAction :=
  FiniteAction.chosen_action_exact compatible

theorem finiteActionCompatible_iff_exists_exact :
    FiniteActionCompatible ↔ ∃ action : Form → Form → Form, ExactFiniteAction action :=
  FiniteAction.compatible_iff_exists_exact f2f ground

end Hypermath
