import Hypermath.GroundSyntax

/-!
# Composed derivations for the ground source fragment

The primitive rules come from L0 Section III; the three predicate closes come
from Section VI. Conjunction is the host logical reading already used by the
source's L0 Section IV and L1 ax-diff-in-relation-language derivations.

`Record` retains the rule tree and its explicit premise annotations. `check`
receives no hidden derivation or semantic oracle. Each recursive premise is
checked before a conclusion is accepted. `Derivation` indexes valid rule trees
by their conclusions, and `quote` supplies a record accepted by that checker.

This is a source-derived finite calculus with structured records, not a claim
that those records or the checker have been reified as semantic `Form` values.
No internal acceptance rule, arithmetic translation, or limit rule is added.
-/

namespace Hypermath.GroundDerivation

open GroundSyntax

inductive Formula where
  | structural (statement : Statement)
  | similar (left right : Term)
  | notSimulation (left right : Term)
  | both (left right : Formula)
  deriving DecidableEq, Repr

/-- Precisely the additional source premises for the three predicate closes. -/
structure Model extends GroundSyntax.Model where
  similar : Carrier → Carrier → Prop
  simulation : Carrier → Carrier → Prop
  closeContinues : ∀ x, continues x base ↔ similar x base
  closeDistinct : ∀ x y, distinct x y ↔ ¬ simulation x y
  closeOrbits : ∀ x, orbits (step (step x)) x ↔ similar (step (step x)) x

def Formula.holds (model : Model) : Formula → Prop
  | .structural statement => statement.holds model.toModel
  | .similar left right => model.similar
      (left.interpret model.base model.step) (right.interpret model.base model.step)
  | .notSimulation left right => ¬ model.simulation
      (left.interpret model.base model.step) (right.interpret model.base model.step)
  | .both left right => left.holds model ∧ right.holds model

/-- A typed finite calculus. Every premise is a smaller derivation. -/
inductive Derivation : Formula → Type where
  | primitive (rule : AxiomInstance) : Derivation (.structural rule.conclusion)
  | closeContinues (term : Term)
      (premise : Derivation (.structural (.continues term .ground))) :
      Derivation (.similar term .ground)
  | closeDistinct (left right : Term)
      (premise : Derivation (.structural (.distinct left right))) :
      Derivation (.notSimulation left right)
  | closeOrbits (term : Term)
      (premise : Derivation (.structural (.orbits (.apply (.apply term)) term))) :
      Derivation (.similar (.apply (.apply term)) term)
  | join {left right : Formula} (first : Derivation left) (second : Derivation right) :
      Derivation (.both left right)
  | projectLeft {left right : Formula} (premise : Derivation (.both left right)) : Derivation left
  | projectRight {left right : Formula} (premise : Derivation (.both left right)) : Derivation right

theorem derivation_sound (model : Model) {conclusion : Formula}
    (proof : Derivation conclusion) : conclusion.holds model := by
  induction proof with
  | primitive rule => exact GroundSyntax.instance_sound model.toModel rule
  | closeContinues term _ ih => exact (model.closeContinues _).mp ih
  | closeDistinct left right _ ih => exact (model.closeDistinct _ _).mp ih
  | closeOrbits term _ ih => exact (model.closeOrbits _).mp ih
  | join _ _ first second => exact ⟨first, second⟩
  | projectLeft _ ih => exact ih.1
  | projectRight _ ih => exact ih.2

/-- Untyped input records: annotations are claims to check, not evidence. -/
inductive Record where
  | primitive (rule : AxiomInstance)
  | closeContinues (term : Term) (premise : Record)
  | closeDistinct (left right : Term) (premise : Record)
  | closeOrbits (term : Term) (premise : Record)
  | join (first second : Record)
  | projectLeft (left right : Formula) (premise : Record)
  | projectRight (left right : Formula) (premise : Record)
  deriving DecidableEq, Repr

def Record.conclusion : Record → Formula
  | .primitive rule => .structural rule.conclusion
  | .closeContinues term _ => .similar term .ground
  | .closeDistinct left right _ => .notSimulation left right
  | .closeOrbits term _ => .similar (.apply (.apply term)) term
  | .join first second => .both first.conclusion second.conclusion
  | .projectLeft left _ _ => left
  | .projectRight _ right _ => right

def Record.valid : Record → Bool
  | .primitive _ => true
  | .closeContinues term premise => premise.valid &&
      decide (premise.conclusion = .structural (.continues term .ground))
  | .closeDistinct left right premise => premise.valid &&
      decide (premise.conclusion = .structural (.distinct left right))
  | .closeOrbits term premise => premise.valid &&
      decide (premise.conclusion = .structural (.orbits (.apply (.apply term)) term))
  | .join first second => first.valid && second.valid
  | .projectLeft left right premise => premise.valid &&
      decide (premise.conclusion = .both left right)
  | .projectRight left right premise => premise.valid &&
      decide (premise.conclusion = .both left right)

def check (record : Record) (claimed : Formula) : Bool :=
  record.valid && decide (record.conclusion = claimed)

theorem check_iff (record : Record) (claimed : Formula) :
    check record claimed = true ↔ record.valid = true ∧ record.conclusion = claimed := by
  simp [check]

/-- Reconstruct a typed derivation given the record's computed acceptance. -/
def Record.derive : (record : Record) → record.valid = true → Derivation record.conclusion
  | .primitive rule, _ => .primitive rule
  | .closeContinues term premise, accepted => by
      have premises : premise.valid = true ∧
          premise.conclusion = .structural (.continues term .ground) := by
        simpa [Record.valid] using accepted
      exact .closeContinues term (premises.2 ▸ premise.derive premises.1)
  | .closeDistinct left right premise, accepted => by
      have premises : premise.valid = true ∧
          premise.conclusion = .structural (.distinct left right) := by
        simpa [Record.valid] using accepted
      exact .closeDistinct left right (premises.2 ▸ premise.derive premises.1)
  | .closeOrbits term premise, accepted => by
      have premises : premise.valid = true ∧
          premise.conclusion = .structural (.orbits (.apply (.apply term)) term) := by
        simpa [Record.valid] using accepted
      exact .closeOrbits term (premises.2 ▸ premise.derive premises.1)
  | .join first second, accepted => by
      have premises : first.valid = true ∧ second.valid = true := by
        simpa [Record.valid] using accepted
      exact .join (first.derive premises.1) (second.derive premises.2)
  | .projectLeft left right premise, accepted => by
      have premises : premise.valid = true ∧ premise.conclusion = .both left right := by
        simpa [Record.valid] using accepted
      exact .projectLeft (premises.2 ▸ premise.derive premises.1)
  | .projectRight left right premise, accepted => by
      have premises : premise.valid = true ∧ premise.conclusion = .both left right := by
        simpa [Record.valid] using accepted
      exact .projectRight (premises.2 ▸ premise.derive premises.1)

theorem check_sound (model : Model) (record : Record) (claimed : Formula)
    (accepted : check record claimed = true) : claimed.holds model := by
  obtain ⟨valid, equality⟩ := (check_iff record claimed).mp accepted
  exact equality ▸ derivation_sound model (record.derive valid)

def quote {conclusion : Formula} : Derivation conclusion → Record
  | .primitive rule => .primitive rule
  | .closeContinues term premise => .closeContinues term (quote premise)
  | .closeDistinct left right premise => .closeDistinct left right (quote premise)
  | .closeOrbits term premise => .closeOrbits term (quote premise)
  | .join first second => .join (quote first) (quote second)
  | .projectLeft (left := left) (right := right) premise => .projectLeft left right (quote premise)
  | .projectRight (left := left) (right := right) premise => .projectRight left right (quote premise)

theorem conclusion_quote {conclusion : Formula} (proof : Derivation conclusion) :
    (quote proof).conclusion = conclusion := by
  induction proof with
  | primitive => rfl
  | closeContinues => rfl
  | closeDistinct => rfl
  | closeOrbits => rfl
  | join first second ihFirst ihSecond =>
      simp [quote, Record.conclusion, ihFirst, ihSecond]
  | projectLeft => rfl
  | projectRight => rfl

theorem valid_quote {conclusion : Formula} (proof : Derivation conclusion) :
    (quote proof).valid = true := by
  induction proof <;> simp_all [quote, Record.valid, conclusion_quote]

theorem check_quote {conclusion : Formula} (proof : Derivation conclusion) :
    check (quote proof) conclusion = true :=
  (check_iff _ _).mpr ⟨valid_quote proof, conclusion_quote proof⟩

private theorem quote_transport {first second : Formula} (equality : first = second)
    (proof : Derivation first) : quote (equality ▸ proof) = quote proof := by
  cases equality
  rfl

/-- Typed reconstruction retains the entire accepted rule tree, not just its result. -/
theorem quote_derive (record : Record) (accepted : record.valid = true) :
    quote (record.derive accepted) = record := by
  induction record with
  | primitive rule => rfl
  | closeContinues term premise ih =>
      simp [Record.derive, quote, quote_transport, ih]
  | closeDistinct left right premise ih =>
      simp [Record.derive, quote, quote_transport, ih]
  | closeOrbits term premise ih =>
      simp [Record.derive, quote, quote_transport, ih]
  | join first second ihFirst ihSecond =>
      simp [Record.derive, quote, ihFirst, ihSecond]
  | projectLeft left right premise ih =>
      simp [Record.derive, Record.conclusion, quote, quote_transport, ih]
  | projectRight left right premise ih =>
      simp [Record.derive, Record.conclusion, quote, quote_transport, ih]

/-- Every declared observation of an accepted record survives typed reconstruction. -/
theorem observe_derive {β : Type} (query : Record → β) (record : Record)
    (accepted : record.valid = true) :
    query (quote (record.derive accepted)) = query record :=
  congrArg query (quote_derive record accepted)

/-- Executable entry point: the Boolean check supplies its own acceptance evidence. -/
def reconstruct (record : Record) : Option (Sigma Derivation) :=
  if accepted : record.valid = true then
    some ⟨record.conclusion, record.derive accepted⟩
  else none

theorem reconstruct_retains_record (record : Record) (accepted : record.valid = true) :
    (reconstruct record).map (fun proof => quote proof.2) = some record := by
  simp [reconstruct, accepted, quote_derive]

/-- Completeness for this explicitly finite calculus, not arithmetic completeness. -/
theorem represented_iff_derivable (conclusion : Formula) :
    (∃ record, check record conclusion = true) ↔ Nonempty (Derivation conclusion) := by
  constructor
  · rintro ⟨record, accepted⟩
    obtain ⟨valid, equality⟩ := (check_iff record conclusion).mp accepted
    exact ⟨equality ▸ record.derive valid⟩
  · rintro ⟨proof⟩
    exact ⟨quote proof, check_quote proof⟩

/-- Reuse two already checked records without replacing their retained evidence. -/
theorem check_join_iff (first second : Record) :
    check (.join first second) (.both first.conclusion second.conclusion) = true ↔
      first.valid = true ∧ second.valid = true := by
  simp [check, Record.conclusion, Record.valid]

/-- The source's ax-diff-in-relation-language derivation, with both premises retained. -/
def separation (term : Term) :
    Derivation (.both (.similar (.apply term) .ground)
      (.notSimulation (.apply term) .ground)) :=
  .join (.closeContinues (.apply term) (.primitive (.sim term)))
    (.closeDistinct (.apply term) .ground (.primitive (.diff term)))

/-- The same six ground parameters and four rules, plus two relation parameters
and the three already declared predicate closes. No additional native clause. -/
noncomputable def nativeModel : Model where
  toModel := GroundSyntax.nativeModel
  similar := Hypermath.Similar
  simulation := Hypermath.Simulation
  closeContinues := Hypermath.closeStructContinues
  closeDistinct := Hypermath.closeStructDistinct
  closeOrbits := Hypermath.closeStructOrbits

theorem native_check_sound (record : Record) (claimed : Formula)
    (accepted : check record claimed = true) : claimed.holds nativeModel :=
  check_sound nativeModel record claimed accepted

end Hypermath.GroundDerivation
