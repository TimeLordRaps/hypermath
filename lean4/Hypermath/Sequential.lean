import Hypermath.RecordMachine

/-!
# Sequencing as a common algebra of composition

The author's revised sequencing interpretation packages one associative
operation with a ground identity. Commutativity and inverses are separate
properties. With equality this is a monoid; with an explicitly proved
equivalence and operation congruence the laws hold modulo that relation.
No equivalence property is imposed on the source's overlap similarity.

L2_operations.hm asks for one binary sequential operation, a two-sided ground
identity modulo congruence, and noncommutation whenever the operands are not
congruent. For symmetric, transitive congruence, those requirements cannot
coexist with any incongruent pair. The existential-witness Lean translation
does not bind its separate witnesses to one such operation.

These statements are explicit conditional consequences, not new source axioms.
Finite instruction concatenation supplies an ordered-sequence example
with identity, associativity and witnessed noncommutation; its
different nonempty powers also commute. This is a concrete finite refinement,
not a native Form realization or an arithmetic-completeness theorem.
-/

namespace Hypermath.Sequential

def TwoSidedIdentity {α : Type} (related : α → α → Prop) (operation : α → α → α)
    (unit : α) : Prop :=
  ∀ x, related (operation x unit) x ∧ related (operation unit x) x

/-- The uniform noncommutation clause written in L2_operations.hm, section III. -/
def UniformSeparation {α : Type} (related : α → α → Prop) (operation : α → α → α) : Prop :=
  ∀ x y, ¬ related x y → ¬ related (operation x y) (operation y x)

/-- Bind all three source requirements to the same binary operation. -/
def SourceOperationExists {α : Type} (similar related : α → α → Prop) (unit : α) : Prop :=
  ∃ operation : α → α → α,
    (∀ x y, similar (operation x y) x ∧ similar (operation x y) y) ∧
    TwoSidedIdentity related operation unit ∧ UniformSeparation related operation

theorem unit_commutes {α : Type} {related : α → α → Prop} {operation : α → α → α}
    {unit : α} (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (identity : TwoSidedIdentity related operation unit) (x : α) :
    related (operation x unit) (operation unit x) :=
  transitive (identity x).1 (symmetric (identity x).2)

theorem uniform_separation_double_negates_unit {α : Type} {related : α → α → Prop}
    {operation : α → α → α} {unit : α}
    (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (identity : TwoSidedIdentity related operation unit)
    (separation : UniformSeparation related operation) (x : α) : ¬¬ related x unit :=
  fun unequal => separation x unit unequal
    (unit_commutes (related := related) symmetric transitive identity x)

/-- No excluded-middle step is needed: double-negated unit relations already
contradict a separated pair, using symmetry and transitivity. -/
theorem no_uniform_separation {α : Type} {related : α → α → Prop}
    {operation : α → α → α} {unit : α}
    (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (identity : TwoSidedIdentity related operation unit)
    (nontrivial : ∃ x y, ¬ related x y) : ¬ UniformSeparation related operation := by
  intro separation
  obtain ⟨x, y, unequal⟩ := nontrivial
  have nx := uniform_separation_double_negates_unit (related := related)
    symmetric transitive identity separation x
  have ny := uniform_separation_double_negates_unit (related := related)
    symmetric transitive identity separation y
  exact nx (fun xu => ny (fun yu => unequal (transitive xu (symmetric yu))))

theorem no_source_operation {α : Type} {similar related : α → α → Prop} {unit : α}
    (symmetric : ∀ {x y}, related x y → related y x)
    (transitive : ∀ {x y z}, related x y → related y z → related x z)
    (nontrivial : ∃ x y, ¬ related x y) : ¬ SourceOperationExists similar related unit := by
  rintro ⟨operation, _, identity, separation⟩
  exact no_uniform_separation (related := related) symmetric transitive identity nontrivial separation

/-- A weaker noncommutativity requirement names an actual witness pair. -/
def Noncommutative {α : Type} (related : α → α → Prop) (operation : α → α → α) : Prop :=
  ∃ x y, ¬ related (operation x y) (operation y x)

/-- One shared operation and identity, with laws under an explicitly justified
equivalence. The relation is not silently identified with native congruence. -/
structure Sequencing (α : Type) (related : α → α → Prop) where
  equivalence : Equivalence related
  operation : α → α → α
  unit : α
  respects : ∀ {x x' y y'}, related x x' → related y y' →
    related (operation x y) (operation x' y')
  identity : TwoSidedIdentity related operation unit
  associative : ∀ x y z,
    related (operation (operation x y) z) (operation x (operation y z))

/-- Commutativity is optional; associativity alone does not imply it. -/
def Commutative {α : Type} {related : α → α → Prop}
    (sequencing : Sequencing α related) : Prop :=
  ∀ x y, related (sequencing.operation x y) (sequencing.operation y x)

/-- A sequencing algebra with inverses is a group modulo its relation.
Inverses are additional data and laws, not a requirement on every sequencing. -/
structure Inverses {α : Type} {related : α → α → Prop}
    (sequencing : Sequencing α related) where
  inverse : α → α
  laws : ∀ x,
    related (sequencing.operation x (inverse x)) sequencing.unit ∧
    related (sequencing.operation (inverse x) x) sequencing.unit

/-- A map that preserves the relation, identity and composition. Faithfulness
(reflecting the relation) is deliberately a separate proof obligation. -/
structure CompositionMap {α β : Type} {sourceRelation : α → α → Prop}
    {targetRelation : β → β → Prop}
    (source : Sequencing α sourceRelation) (target : Sequencing β targetRelation) where
  toFun : α → β
  respects : ∀ {x y}, sourceRelation x y → targetRelation (toFun x) (toFun y)
  preserves_unit : targetRelation (toFun source.unit) target.unit
  preserves_operation : ∀ x y,
    targetRelation (toFun (source.operation x y)) (target.operation (toFun x) (toFun y))

abbrev Program := List RecordMachine.Instruction

theorem program_identity : TwoSidedIdentity Eq (List.append : Program → Program → Program) [] := by
  intro program
  exact ⟨List.append_nil program, rfl⟩

theorem program_associative (first second third : Program) :
    first ++ (second ++ third) = (first ++ second) ++ third :=
  (List.append_assoc first second third).symm

theorem program_composition_executes (first second : Program) (state : RecordMachine.State) :
    RecordMachine.execute (first ++ second) state =
      RecordMachine.execute second (RecordMachine.execute first state) :=
  RecordMachine.execute_append first second state

def firstProgram : Program := [.primitive .groundSelf]
def secondProgram : Program := [.primitive (.diff .ground)]

theorem program_noncommutative : Noncommutative Eq (List.append : Program → Program → Program) := by
  exact ⟨firstProgram, secondProgram, by decide⟩

/-- Noncommutation is observable in the resulting stack, not just the code order. -/
theorem program_order_changes_result :
    RecordMachine.execute (firstProgram ++ secondProgram) (some []) ≠
      RecordMachine.execute (secondProgram ++ firstProgram) (some []) := by
  decide

/-- Excluding the unit from the uniform clause would still be too strong. -/
theorem distinct_nonempty_programs_commute :
    firstProgram ≠ [] ∧ firstProgram ++ firstProgram ≠ [] ∧
    firstProgram ≠ firstProgram ++ firstProgram ∧
    firstProgram ++ (firstProgram ++ firstProgram) =
      (firstProgram ++ firstProgram) ++ firstProgram := by
  exact ⟨by decide, by decide, by decide, program_associative _ _ _⟩

theorem program_uniform_separation_fails :
    ¬ UniformSeparation Eq (List.append : Program → Program → Program) :=
  no_uniform_separation (related := Eq) Eq.symm Eq.trans program_identity
    ⟨firstProgram, [], by decide⟩

/-- Order-sensitive instruction composition, packaged with all of its laws. -/
def programSequencing : Sequencing Program Eq where
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  operation := List.append
  unit := []
  respects := by
    intro x x' y y' hx hy
    cases hx
    cases hy
    rfl
  identity := program_identity
  associative := List.append_assoc

/-- Commutative finite arithmetic is another instance of the same interface. -/
def naturalSequencing : Sequencing Nat Eq where
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  operation := Nat.add
  unit := 0
  respects := by
    intro x x' y y' hx hy
    cases hx
    cases hy
    rfl
  identity := fun n => ⟨Nat.add_zero n, Nat.zero_add n⟩
  associative := Nat.add_assoc

theorem natural_commutative : Commutative naturalSequencing := Nat.add_comm

theorem program_not_commutative : ¬ Commutative programSequencing := by
  intro commutes
  obtain ⟨first, second, unequal⟩ := program_noncommutative
  exact unequal (commutes first second)

/-- Requiring inverses would exclude even the finite arithmetic example. -/
theorem natural_no_inverses : ¬ Nonempty (Inverses naturalSequencing) := by
  rintro ⟨inverses⟩
  have impossible : Nat.succ (inverses.inverse 1) = 0 := by
    simpa [naturalSequencing, Nat.add_comm] using (inverses.laws 1).1
  exact Nat.noConfusion impossible

/-- Counting instructions is a composition-preserving arithmetic interpretation. -/
def programLength : CompositionMap programSequencing naturalSequencing where
  toFun := List.length
  respects := fun h => congrArg List.length h
  preserves_unit := rfl
  preserves_operation := List.length_append

theorem program_length_preserves_composition (first second : Program) :
    programLength.toFun (first ++ second) =
      programLength.toFun first + programLength.toFun second :=
  programLength.preserves_operation first second

/-- Preservation of composition does not imply preservation of order information. -/
theorem program_length_forgets_order (first second : Program) :
    programLength.toFun (first ++ second) = programLength.toFun (second ++ first) := by
  rw [program_length_preserves_composition, program_length_preserves_composition]
  exact Nat.add_comm _ _

theorem program_length_not_faithful :
    ∃ first second : Program, programLength.toFun first = programLength.toFun second ∧
      first ≠ second :=
  ⟨firstProgram, secondProgram, rfl, by decide⟩

end Hypermath.Sequential
