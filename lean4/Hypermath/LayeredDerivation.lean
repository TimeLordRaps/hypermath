import Hypermath.Sequential

/-!
# Composition and passage between finite representation layers

Layer zero contains exact records and claimed formulas of the source-derived
ground calculus. A successor layer contains expressions whose atoms hold
complete encoded lower-layer surfaces. Decoding and checking remain executable
host operations. No native formation, acceptance, ordinal-limit, or truth axiom
is introduced by this construction.

The representation retains grouping and all embedded lower-layer trees.
Composition is associative modulo its expanded, checked record sequence;
that observation relation is explicit and is not native congruence.
-/

namespace Hypermath.LayeredDerivation

open GroundCode GroundDerivation RecordEncoding

abbrev Evidence := Record × Formula

inductive Expression where
  | empty
  | atom (lowerCode : Tree)
  | seq (first second : Expression)
  deriving DecidableEq, Repr

def Expression.tree : Expression → Tree
  | .empty => tag 0 .leaf
  | .atom code => tag 1 code
  | .seq first second => tag 2 (.fork first.tree second.tree)

def readExpression : Tree → Option Expression
  | .fork marker payload =>
      match readTag marker, payload with
      | some 0, .leaf => some .empty
      | some 1, code => some (.atom code)
      | some 2, .fork first second => do
          return .seq (← readExpression first) (← readExpression second)
      | _, _ => none
  | _ => none

theorem readExpression_tree (expression : Expression) :
    readExpression expression.tree = some expression := by
  induction expression <;> simp_all [Expression.tree, readExpression, tag, readTag_number]

/-- The layer parameter controls both the grammar and subsequent decoding. -/
def Surface : Nat → Type
  | 0 => Evidence
  | _ + 1 => Expression

instance (layer : Nat) : DecidableEq (Surface layer) :=
  match layer with
  | 0 => inferInstanceAs (DecidableEq Evidence)
  | _ + 1 => inferInstanceAs (DecidableEq Expression)

def payload : (layer : Nat) → Surface layer → Tree
  | 0, (record, claim) => .fork (recordTree record) (formulaTree claim)
  | _ + 1, expression => expression.tree

def readPayload : (layer : Nat) → Tree → Option (Surface layer)
  | 0, .fork record claim => do
      return (← readRecord record, ← readFormula claim)
  | 0, _ => none
  | _ + 1, tree => readExpression tree

theorem readPayload_payload (layer : Nat) (surface : Surface layer) :
    readPayload layer (payload layer surface) = some surface := by
  cases layer with
  | zero =>
      cases surface
      simp [payload, readPayload, readRecord_recordTree, readFormula_formulaTree]
  | succ layer => exact readExpression_tree surface

/-- Envelope 12 identifies this format; the nested tag binds the actual layer. -/
def encode (layer : Nat) (surface : Surface layer) : Tree :=
  tag 12 (tag layer (payload layer surface))

def decode (layer : Nat) (tree : Tree) : Option (Surface layer) := do
  let framed ← unwrap 12 tree
  let contents ← unwrap layer framed
  readPayload layer contents

theorem decode_encode (layer : Nat) (surface : Surface layer) :
    decode layer (encode layer surface) = some surface := by
  simp [decode, encode, unwrap_tag, readPayload_payload]

theorem wrong_layer_rejected (first second : Nat) (different : first ≠ second)
    (surface : Surface first) : decode second (encode first surface) = none := by
  simp [decode, encode, unwrap_tag, unwrap, tag, readTag_number, different]

theorem encode_injective (layer : Nat) {first second : Surface layer}
    (same : encode layer first = encode layer second) : first = second :=
  Option.some.inj ((decode_encode layer first).symm.trans
    ((congrArg (decode layer) same).trans (decode_encode layer second)))

def combine {α : Type} (first second : Option (List α)) : Option (List α) := do
  return (← first) ++ (← second)

theorem combine_left_identity {α : Type} (value : Option (List α)) :
    combine (some []) value = value := by
  cases value <;> rfl

theorem combine_right_identity {α : Type} (value : Option (List α)) :
    combine value (some []) = value := by
  cases value <;> simp [combine]

theorem combine_associative {α : Type} (a b c : Option (List α)) :
    combine (combine a b) c = combine a (combine b c) := by
  cases a <;> cases b <;> cases c <;> simp [combine, List.append_assoc]

def Expression.run {α : Type} (atom : Tree → Option (List α)) :
    Expression → Option (List α)
  | .empty => some []
  | .atom code => atom code
  | .seq first second => combine (first.run atom) (second.run atom)

theorem Expression.run_sound {α : Type} (good : α → Prop)
    (atom : Tree → Option (List α))
    (atom_sound : ∀ code values, atom code = some values → ∀ value ∈ values, good value)
    (expression : Expression) (values : List α) (accepted : expression.run atom = some values) :
    ∀ value ∈ values, good value := by
  induction expression generalizing values with
  | empty =>
      have empty : values = [] := (Option.some.inj accepted).symm
      subst values
      simp
  | atom code => exact atom_sound code values accepted
  | seq first second ihFirst ihSecond =>
      cases hf : first.run atom with
      | none => simp [Expression.run, combine, hf] at accepted
      | some left =>
          cases hs : second.run atom with
          | none => simp [Expression.run, combine, hf, hs] at accepted
          | some right =>
              have joined : left ++ right = values := by
                simpa [Expression.run, combine, hf, hs] using accepted
              subst values
              intro value member
              rcases List.mem_append.mp member with member | member
              · exact ihFirst left hf value member
              · exact ihSecond right hs value member

/-- Every layer checks encoded atoms at the strictly lower layer. An invalid
record, false claim, malformed code or wrong layer produces `none`. -/
def unfold : (layer : Nat) → Surface layer → Option (List Evidence)
  | 0, evidence => if RecordMachine.check evidence.1 evidence.2 then some [evidence] else none
  | layer + 1, expression => expression.run (fun code => do
      let lower ← decode layer code
      unfold layer lower)

def valid (layer : Nat) (surface : Surface layer) : Bool := (unfold layer surface).isSome

/-- Claims are an ordered list. Order and multiplicity are not replaced by a set. -/
def check (layer : Nat) (surface : Surface layer) (claims : List Formula) : Bool :=
  decide ((unfold layer surface).map (List.map Prod.snd) = some claims)

theorem check_iff (layer : Nat) (surface : Surface layer) (claims : List Formula) :
    check layer surface claims = true ↔
      ∃ evidence, unfold layer surface = some evidence ∧ evidence.map Prod.snd = claims := by
  cases observed : unfold layer surface <;> simp [check, observed]

def lift (layer : Nat) (surface : Surface layer) : Surface (layer + 1) :=
  .atom (encode layer surface)

def lowerAtom (layer : Nat) : Surface (layer + 1) → Option (Surface layer)
  | .atom code => decode layer code
  | _ => none

theorem lowerAtom_lift (layer : Nat) (surface : Surface layer) :
    lowerAtom layer (lift layer surface) = some surface := decode_encode layer surface

theorem unfold_lift (layer : Nat) (surface : Surface layer) :
    unfold (layer + 1) (lift layer surface) = unfold layer surface := by
  simp [unfold, lift, Expression.run, decode_encode]

theorem lift_injective (layer : Nat) {first second : Surface layer}
    (same : lift layer first = lift layer second) : first = second :=
  Option.some.inj ((lowerAtom_lift layer first).symm.trans
    ((congrArg (lowerAtom layer) same).trans (lowerAtom_lift layer second)))

theorem valid_lift (layer : Nat) (surface : Surface layer) :
    valid (layer + 1) (lift layer surface) = valid layer surface := by
  simp [valid, unfold_lift]

theorem check_lift (layer : Nat) (surface : Surface layer) (claims : List Formula) :
    check (layer + 1) (lift layer surface) claims = check layer surface claims := by
  simp [check, unfold_lift]

theorem unfold_seq (layer : Nat) (first second : Surface (layer + 1)) :
    unfold (layer + 1) (.seq first second) =
      combine (unfold (layer + 1) first) (unfold (layer + 1) second) := rfl

theorem valid_seq (layer : Nat) (first second : Surface (layer + 1)) :
    valid (layer + 1) (.seq first second) =
      (valid (layer + 1) first && valid (layer + 1) second) := by
  simp only [valid, unfold_seq]
  cases unfold (layer + 1) first <;> cases unfold (layer + 1) second <;> rfl

theorem check_seq (layer : Nat) (first second : Surface (layer + 1))
    (firstClaims secondClaims : List Formula)
    (firstAccepted : check (layer + 1) first firstClaims = true)
    (secondAccepted : check (layer + 1) second secondClaims = true) :
    check (layer + 1) (.seq first second) (firstClaims ++ secondClaims) = true := by
  obtain ⟨left, hLeft, claimsLeft⟩ := (check_iff _ _ _).mp firstAccepted
  obtain ⟨right, hRight, claimsRight⟩ := (check_iff _ _ _).mp secondAccepted
  apply (check_iff _ _ _).mpr
  exact ⟨left ++ right, by simp [unfold_seq, combine, hLeft, hRight],
    by simp [List.map_append, claimsLeft, claimsRight]⟩

/-- Reifying a composition and composing reified inputs have the same checked
expansion. The encodings still retain their different grouping boundaries. -/
theorem lift_preserves_composition (layer : Nat) (first second : Surface (layer + 1)) :
    unfold (layer + 2) (lift (layer + 1) (.seq first second)) =
      unfold (layer + 2) (.seq (lift (layer + 1) first) (lift (layer + 1) second)) := by
  rw [unfold_lift, unfold_seq, unfold_seq, unfold_lift, unfold_lift]

def iterateLift : (count layer : Nat) → Surface layer → Surface (layer + count)
  | 0, _, surface => surface
  | count + 1, layer, surface => lift (layer + count) (iterateLift count layer surface)

def recoverThrough : (count layer : Nat) → Surface (layer + count) → Option (Surface layer)
  | 0, _, surface => some surface
  | count + 1, layer, surface => do
      let lower ← lowerAtom (layer + count) surface
      recoverThrough count layer lower

theorem recoverThrough_iterateLift (count layer : Nat) (surface : Surface layer) :
    recoverThrough count layer (iterateLift count layer surface) = some surface := by
  induction count with
  | zero => rfl
  | succ count ih => simp [iterateLift, recoverThrough, lowerAtom_lift, ih]

theorem unfold_iterateLift (count layer : Nat) (surface : Surface layer) :
    unfold (layer + count) (iterateLift count layer surface) = unfold layer surface := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change unfold ((layer + count) + 1)
        (lift (layer + count) (iterateLift count layer surface)) = unfold layer surface
      rw [unfold_lift]
      exact ih

theorem check_iterateLift (count layer : Nat) (surface : Surface layer) (claims : List Formula) :
    check (layer + count) (iterateLift count layer surface) claims = check layer surface claims := by
  simp [check, unfold_iterateLift]

/-- Every observation of the original representation survives any finite
number of lifts, including exact grouping, invalid inputs and premise data. -/
theorem observe_iterateLift {β : Type} (count layer : Nat)
    (query : Surface layer → β) (surface : Surface layer) :
    (recoverThrough count layer (iterateLift count layer surface)).map query =
      some (query surface) := by
  rw [recoverThrough_iterateLift]
  rfl

/-- Exact composition history and its checked expansion both survive any
finite number of passages to the next layer. No acceptance premise hides
invalid inputs: if either expansion fails, the composed expansion fails. -/
theorem composition_lift_preserves (count layer : Nat)
    (first second : Surface (layer + 1)) :
    recoverThrough count (layer + 1)
        (iterateLift count (layer + 1) (.seq first second)) = some (.seq first second) ∧
    unfold ((layer + 1) + count)
        (iterateLift count (layer + 1) (.seq first second)) =
      combine (unfold (layer + 1) first) (unfold (layer + 1) second) :=
  ⟨recoverThrough_iterateLift _ _ _, (unfold_iterateLift _ _ _).trans (unfold_seq _ _ _)⟩

theorem unfold_sound (layer : Nat) (surface : Surface layer) (evidence : List Evidence)
    (accepted : unfold layer surface = some evidence) :
    ∀ pair ∈ evidence, GroundDerivation.check pair.1 pair.2 = true := by
  induction layer generalizing evidence with
  | zero =>
      simp only [unfold] at accepted
      split at accepted
      next valid =>
        have equality : [surface] = evidence := Option.some.inj accepted
        subst evidence
        intro pair member
        have equality := List.mem_singleton.mp member
        subst pair
        exact (RecordMachine.check_agrees _ _) ▸ valid
      next => contradiction
  | succ layer ih =>
      apply Expression.run_sound (fun pair : Evidence =>
        GroundDerivation.check pair.1 pair.2 = true) _ _ surface evidence accepted
      intro code records passed
      cases decoded : decode layer code with
      | none => simp [decoded] at passed
      | some lower => exact ih lower records (by simpa [decoded] using passed)

theorem unfolded_claims_sound (model : GroundDerivation.Model) (layer : Nat)
    (surface : Surface layer) (evidence : List Evidence)
    (accepted : unfold layer surface = some evidence) :
    ∀ pair ∈ evidence, pair.2.holds model := by
  intro pair member
  exact GroundDerivation.check_sound model pair.1 pair.2
    (unfold_sound layer surface evidence accepted pair member)

theorem check_sound (model : GroundDerivation.Model) (layer : Nat)
    (surface : Surface layer) (claims : List Formula)
    (accepted : check layer surface claims = true) : ∀ claim ∈ claims, claim.holds model := by
  obtain ⟨evidence, expanded, claimEquality⟩ := (check_iff _ _ _).mp accepted
  intro claim member
  rw [← claimEquality] at member
  obtain ⟨pair, present, equality⟩ := List.mem_map.mp member
  exact equality ▸ unfolded_claims_sound model layer surface evidence expanded pair present

/-- This relation observes the complete expanded checked sequence. It is not
equality of encoded surface syntax and is not the source's native congruence. -/
def SameExpansion (layer : Nat) (first second : Surface (layer + 1)) : Prop :=
  unfold (layer + 1) first = unfold (layer + 1) second

def sequencing (layer : Nat) : Sequential.Sequencing (Surface (layer + 1)) (SameExpansion layer) where
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  operation := Expression.seq
  unit := Expression.empty
  respects := by
    intro x x' y y' hx hy
    change unfold (layer + 1) x = unfold (layer + 1) x' at hx
    change unfold (layer + 1) y = unfold (layer + 1) y' at hy
    change combine (unfold (layer + 1) x) (unfold (layer + 1) y) =
      combine (unfold (layer + 1) x') (unfold (layer + 1) y')
    rw [hx, hy]
  identity := fun value => ⟨combine_right_identity _, combine_left_identity _⟩
  associative := fun x y z => combine_associative _ _ _

/-- The layer lift preserves monoid composition under the declared observation. -/
def liftMap (layer : Nat) : Sequential.CompositionMap (sequencing layer) (sequencing (layer + 1)) where
  toFun := lift (layer + 1)
  respects := by
    intro first second same
    change unfold _ (lift _ first) = unfold _ (lift _ second)
    simpa only [unfold_lift] using same
  preserves_unit := unfold_lift (layer + 1) .empty
  preserves_operation := fun first second => lift_preserves_composition layer first second

theorem lift_reflects_expansion (layer : Nat) (first second : Surface (layer + 1)) :
    SameExpansion (layer + 1) (lift (layer + 1) first) (lift (layer + 1) second) ↔
      SameExpansion layer first second := by
  simp [SameExpansion, unfold_lift]

/-- The existing free-ground syntax can retain an entire layer surface. -/
def groundTerm (layer : Nat) (surface : Surface layer) : GroundSyntax.Term :=
  (encode layer surface).toTerm

def readGroundTerm (layer : Nat) (term : GroundSyntax.Term) : Option (Surface layer) :=
  (GroundCode.decodeTerm term).bind (decode layer)

theorem readGroundTerm_groundTerm (layer : Nat) (surface : Surface layer) :
    readGroundTerm layer (groundTerm layer surface) = some surface := by
  simp [readGroundTerm, groundTerm, decode_toTerm, decode_encode]

theorem observe_groundTerm {β : Type} (layer : Nat) (query : Surface layer → β)
    (surface : Surface layer) :
    (readGroundTerm layer (groundTerm layer surface)).map query = some (query surface) := by
  rw [readGroundTerm_groundTerm]
  rfl

/-- Decode before checking. A malformed ground representation never supplies a
typed derivation or an acceptance oracle to the checker. -/
def checkDecodedSurface (layer : Nat) (decoded : Option (Surface layer))
    (claims : List Formula) : Bool :=
  match decoded with
  | some surface => check layer surface claims
  | none => false

def checkGroundTerm (layer : Nat) (term : GroundSyntax.Term) (claims : List Formula) : Bool :=
  checkDecodedSurface layer (readGroundTerm layer term) claims

theorem checkGroundTerm_groundTerm (layer : Nat) (surface : Surface layer)
    (claims : List Formula) :
    checkGroundTerm layer (groundTerm layer surface) claims = check layer surface claims :=
  congrArg (fun decoded => checkDecodedSurface layer decoded claims)
    (readGroundTerm_groundTerm layer surface)

end Hypermath.LayeredDerivation
