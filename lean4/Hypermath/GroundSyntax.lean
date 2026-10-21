import Hypermath.L0Ground

/-!
# Finite source syntax and a checker for the four primitive ground rules

`Term` is the free finite syntax of `ground` and `apply` in L0_ground.hm,
Section I. It is not identified with the semantic `Hypermath.Form` parameter.
The syntax constructors retain formation history even when interpretation
identifies different terms. `AxiomInstance` names exactly the four rules in
Section III. Its record is again a `Term`, decoded without an external proof
argument. The checker is sound in every interpretation satisfying those rules.

This is a finite source fragment. Lists, recursion, pattern matching, and the
checker metatheorems use Lean's host infrastructure. No internal acceptance
rule, native Form decoder, arithmetic completeness, or limit construction is
introduced or assumed by this module.
-/

namespace Hypermath.GroundSyntax

/-- Free formation syntax; constructor equality is syntactic equality. -/
inductive Term where
  | ground
  | apply (argument : Term)
  deriving DecidableEq, Repr

/-- Interpret formation syntax in any unary ground structure. -/
def Term.interpret {α : Type} (base : α) (step : α → α) : Term → α
  | .ground => base
  | .apply term => step (interpret base step term)

/-- Count retained constructor applications; this is an observation of syntax. -/
def Term.depth : Term → Nat
  | .ground => 0
  | .apply term => term.depth + 1

def Term.ofDepth : Nat → Term
  | 0 => .ground
  | n + 1 => .apply (ofDepth n)

theorem Term.depth_ofDepth (n : Nat) : (ofDepth n).depth = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem Term.ofDepth_depth (term : Term) : ofDepth term.depth = term := by
  induction term with
  | ground => rfl
  | apply term ih => exact congrArg Term.apply ih

theorem Term.interpret_ofDepth {α : Type} (base : α) (step : α → α) (n : Nat) :
    (ofDepth n).interpret base step = Nat.repeat step n base := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

/-- Only the three primitive binary assertions in the source fragment. -/
inductive Statement where
  | distinct (left right : Term)
  | continues (left right : Term)
  | orbits (left right : Term)
  deriving DecidableEq, Repr

/-- A derivation by one of the four explicitly declared primitive rules. -/
inductive AxiomInstance where
  | groundSelf
  | diff (argument : Term)
  | sim (argument : Term)
  | box (argument : Term)
  deriving DecidableEq, Repr

def AxiomInstance.conclusion : AxiomInstance → Statement
  | .groundSelf => .continues .ground .ground
  | .diff term => .distinct (.apply term) .ground
  | .sim term => .continues (.apply term) .ground
  | .box term => .orbits (.apply (.apply term)) term

private def four (term : Term) : Term :=
  .apply (.apply (.apply (.apply term)))

/-- Retain a rule tag at depths 1, 2, or 3 and four applications per argument step.
The ground-self instance uses depth zero; positive multiples of four are invalid.
This is a deliberately unary finite code, not a compression bound. -/
private def tagged (tag : Term) : Term → Term
  | .ground => tag
  | .apply term => four (tagged tag term)

def encode : AxiomInstance → Term
  | .groundSelf => .ground
  | .diff term => tagged (.apply .ground) term
  | .sim term => tagged (.apply (.apply .ground)) term
  | .box term => tagged (.apply (.apply (.apply .ground))) term

private def advance : AxiomInstance → Option AxiomInstance
  | .groundSelf => none
  | .diff term => some (.diff (.apply term))
  | .sim term => some (.sim (.apply term))
  | .box term => some (.box (.apply term))

/-- Decode the record alone. Malformed records remain rejected. -/
def decode : Term → Option AxiomInstance
  | .ground => some .groundSelf
  | .apply .ground => some (.diff .ground)
  | .apply (.apply .ground) => some (.sim .ground)
  | .apply (.apply (.apply .ground)) => some (.box .ground)
  | .apply (.apply (.apply (.apply term))) => (decode term).bind advance

private theorem decode_diff (term : Term) :
    decode (tagged (.apply .ground) term) = some (.diff term) := by
  induction term with
  | ground => rfl
  | apply term ih => simp [tagged, four, decode, ih, advance]

private theorem decode_sim (term : Term) :
    decode (tagged (.apply (.apply .ground)) term) = some (.sim term) := by
  induction term with
  | ground => rfl
  | apply term ih => simp [tagged, four, decode, ih, advance]

private theorem decode_box (term : Term) :
    decode (tagged (.apply (.apply (.apply .ground))) term) = some (.box term) := by
  induction term with
  | ground => rfl
  | apply term ih => simp [tagged, four, decode, ih, advance]

theorem decode_encode (proof : AxiomInstance) :
    decode (encode proof) = some proof := by
  cases proof with
  | groundSelf => rfl
  | diff term => exact decode_diff term
  | sim term => exact decode_sim term
  | box term => exact decode_box term

theorem encode_injective {first second : AxiomInstance}
    (same : encode first = encode second) : first = second :=
  Option.some.inj ((decode_encode first).symm.trans
    ((congrArg decode same).trans (decode_encode second)))

/-- Every observation of the retained rule instance survives its syntactic code. -/
def observe {β : Type} (query : AxiomInstance → β) (record : Term) : Option β :=
  (decode record).map query

theorem observe_encode {β : Type} (query : AxiomInstance → β)
    (proof : AxiomInstance) : observe query (encode proof) = some (query proof) := by
  simp [observe, decode_encode]

/-- Check both record well-formedness and the exact claimed syntactic conclusion. -/
def check (record : Term) (claimed : Statement) : Bool :=
  match decode record with
  | none => false
  | some proof => decide (proof.conclusion = claimed)

theorem check_encode (proof : AxiomInstance) :
    check (encode proof) proof.conclusion = true := by
  simp [check, decode_encode]

/-- Reinstantiate the same primitive rule at the next generated argument.
The argument-free ground-self rule remains itself. -/
def nextArgument : AxiomInstance → AxiomInstance
  | .groundSelf => .groundSelf
  | .diff term => .diff (.apply term)
  | .sim term => .sim (.apply term)
  | .box term => .box (.apply term)

/-- A concrete record-to-record reuse operation using no hidden proof input. -/
def reuse (record : Term) : Option Term :=
  (decode record).map (fun proof => encode (nextArgument proof))

theorem reuse_encode (proof : AxiomInstance) :
    reuse (encode proof) = some (encode (nextArgument proof)) := by
  simp [reuse, decode_encode]

def reuseMany : Nat → Term → Option Term
  | 0, record => some record
  | n + 1, record => (reuseMany n record).bind reuse

theorem reuse_many_encode (n : Nat) (proof : AxiomInstance) :
    reuseMany n (encode proof) = some (encode (Nat.repeat nextArgument n proof)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reuseMany, ih, reuse_encode, Nat.repeat]

theorem check_iff (record : Term) (claimed : Statement) :
    check record claimed = true ↔
      ∃ proof, decode record = some proof ∧ proof.conclusion = claimed := by
  cases decoded : decode record with
  | none => simp [check, decoded]
  | some proof => simp [check, decoded]

/-- An interpretation of exactly L0 Section III, supplied as explicit premises. -/
structure Model where
  Carrier : Type
  base : Carrier
  step : Carrier → Carrier
  distinct : Carrier → Carrier → Prop
  continues : Carrier → Carrier → Prop
  orbits : Carrier → Carrier → Prop
  diffRule : ∀ x, distinct (step x) base
  simRule : ∀ x, continues (step x) base
  boxRule : ∀ x, orbits (step (step x)) x
  groundRule : continues base base

def Statement.holds (model : Model) : Statement → Prop
  | .distinct left right => model.distinct
      (left.interpret model.base model.step) (right.interpret model.base model.step)
  | .continues left right => model.continues
      (left.interpret model.base model.step) (right.interpret model.base model.step)
  | .orbits left right => model.orbits
      (left.interpret model.base model.step) (right.interpret model.base model.step)

theorem instance_sound (model : Model) (proof : AxiomInstance) :
    proof.conclusion.holds model := by
  cases proof with
  | groundSelf => exact model.groundRule
  | diff term => exact model.diffRule _
  | sim term => exact model.simRule _
  | box term => exact model.boxRule _

theorem check_sound (model : Model) (record : Term) (claimed : Statement)
    (accepted : check record claimed = true) : claimed.holds model := by
  obtain ⟨proof, _, conclusion⟩ := (check_iff record claimed).mp accepted
  rw [← conclusion]
  exact instance_sound model proof

/-- Interpret this finite source syntax through the current native parameters.
No additional logical clause or semantic freeness premise is introduced. -/
noncomputable def nativeModel : Model where
  Carrier := Hypermath.Form
  base := Hypermath.ground
  step := Hypermath.f2f
  distinct := Hypermath.structDistinct
  continues := Hypermath.structContinues
  orbits := Hypermath.structOrbits
  diffRule := Hypermath.axDiff
  simRule := Hypermath.axSim
  boxRule := Hypermath.axBox
  groundRule := Hypermath.axGroundSelf

theorem native_check_sound (record : Term) (claimed : Statement)
    (accepted : check record claimed = true) : claimed.holds nativeModel :=
  check_sound nativeModel record claimed accepted

end Hypermath.GroundSyntax
