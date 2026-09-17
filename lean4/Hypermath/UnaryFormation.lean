import Hypermath.Sequential

/-!
# What a fixed unary formation term can express

Open terms add two input variables to the ground/apply signature. They do not
add a binary constructor, recursion on inputs, tests, or a rule interpreter.
Every such term ignores at least one input, in every interpretation. Hence a
term-defined operation with a two-sided unit collapses any symmetric,
transitive comparison relation. A term cannot faithfully encode both inputs
on a carrier with two distinct values either.

This is a boundary on fixed terms, not on operations defined by recursion,
relations, retained histories, or a richer next-layer grammar. In particular,
it does not refute the author's proposed compositional layer. The proof is
host-level structural induction and assumes no native Hypermath axiom.
-/

namespace Hypermath.UnaryFormation

/-- Exactly the finite ground/apply signature, with two input placeholders. -/
inductive Term where
  | ground
  | first
  | second
  | apply (argument : Term)
  deriving DecidableEq, Repr

def Term.eval {α : Type} (base : α) (step : α → α) (first second : α) : Term → α
  | .ground => base
  | .first => first
  | .second => second
  | .apply argument => step (argument.eval base step first second)

def IgnoresFirst {α : Type} (operation : α → α → α) : Prop :=
  ∀ first first' second, operation first second = operation first' second

def IgnoresSecond {α : Type} (operation : α → α → α) : Prop :=
  ∀ first second second', operation first second = operation first second'

/-- Unary application cannot combine the two input dependencies. -/
theorem eval_ignores_an_input {α : Type} (base : α) (step : α → α) (term : Term) :
    IgnoresFirst (fun x y => term.eval base step x y) ∨
      IgnoresSecond (fun x y => term.eval base step x y) := by
  induction term with
  | ground => exact Or.inl (fun _ _ _ => rfl)
  | first => exact Or.inr (fun _ _ _ => rfl)
  | second => exact Or.inl (fun _ _ _ => rfl)
  | apply term ih =>
    cases ih with
    | inl ignores => exact Or.inl (fun x x' y => congrArg step (ignores x x' y))
    | inr ignores => exact Or.inr (fun x y y' => congrArg step (ignores x y y'))

/-- No reflexivity or compatibility of `step` with the relation is needed. -/
theorem identity_collapses_relation {α : Type} {related : α → α → Prop}
    {operation : α → α → α} {unit : α}
    (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (ignores : IgnoresFirst operation ∨ IgnoresSecond operation)
    (identity : Sequential.TwoSidedIdentity related operation unit) :
    ∀ x y, related x y := by
  have common : ∀ x, related (operation unit unit) x := by
    intro x
    cases ignores with
    | inl first =>
      rw [← first x unit unit]
      exact (identity x).1
    | inr second =>
      rw [← second unit x unit]
      exact (identity x).2
  exact fun x y => transitive (symmetric (common x)) (common y)

/-- This obstruction uses only the unit laws, not noncommutation or associativity. -/
theorem no_term_identity {α : Type} (base : α) (step : α → α)
    (related : α → α → Prop) (unit : α)
    (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (nontrivial : ∃ x y, ¬ related x y) :
    ¬ ∃ term : Term,
      Sequential.TwoSidedIdentity related (fun x y => term.eval base step x y) unit := by
  rintro ⟨term, identity⟩
  obtain ⟨x, y, different⟩ := nontrivial
  exact different (identity_collapses_relation (related := related) symmetric transitive
    (eval_ignores_an_input base step term) identity x y)

/-- Recovering both inputs from an input-independent result forces equality. -/
theorem pair_recovery_collapses {α : Type} (base : α) {operation : α → α → α}
    (ignores : IgnoresFirst operation ∨ IgnoresSecond operation)
    (decode : α → Option (α × α))
    (recovers : ∀ x y, decode (operation x y) = some (x, y)) : ∀ x y : α, x = y := by
  intro x y
  cases ignores with
  | inl first =>
    exact congrArg Prod.fst (Option.some.inj ((recovers x base).symm.trans
      ((congrArg decode (first x y base)).trans (recovers y base))))
  | inr second =>
    exact congrArg Prod.snd (Option.some.inj ((recovers base x).symm.trans
      ((congrArg decode (second base x y)).trans (recovers base y))))

/-- Even an unrestricted host decoder cannot recover a missing operand. -/
theorem no_term_pair_encoder {α : Type} (base : α) (step : α → α)
    (nontrivial : ∃ x y : α, x ≠ y) :
    ¬ ∃ (term : Term) (decode : α → Option (α × α)),
      ∀ x y, decode (term.eval base step x y) = some (x, y) := by
  rintro ⟨term, decode, recovers⟩
  obtain ⟨x, y, different⟩ := nontrivial
  exact different (pair_recovery_collapses base
    (eval_ignores_an_input base step term) decode recovers x y)

/-- Addition exists by recursion, but no single fixed successor term computes it. -/
theorem natural_add_not_a_term :
    ¬ ∃ term : Term, ∀ x y : Nat, term.eval 0 Nat.succ x y = x + y := by
  rintro ⟨term, computes⟩
  apply no_term_identity 0 Nat.succ Eq 0 Eq.symm Eq.trans
    ⟨0, 1, by decide⟩
  refine ⟨term, fun x => ?_⟩
  exact ⟨(computes x 0).trans (Nat.add_zero x),
    (computes 0 x).trans (Nat.zero_add x)⟩

/-- The nontriviality condition matters: a singleton carrier has no obstruction. -/
theorem singleton_term_identity :
    Sequential.TwoSidedIdentity Eq
      (fun x y : Unit => Term.first.eval () id x y) () := by
  intro x
  cases x
  exact ⟨rfl, rfl⟩

/-- Relation-level collapse is different from equality of the carrier values. -/
theorem universal_relation_term_identity :
    Sequential.TwoSidedIdentity (fun _ _ : Nat => True)
      (fun x y => Term.first.eval 0 Nat.succ x y) 0 :=
  fun _ => ⟨trivial, trivial⟩

end Hypermath.UnaryFormation
