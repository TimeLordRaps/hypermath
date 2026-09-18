import Hypermath.GroundCode
import Hypermath.GroundDerivation

/-!
# Ground-term encodings of composed records and formulas

The tree grammar is host serialization infrastructure. Distinct envelopes
identify a record and a formula. Packed numbers denote depths in the existing
free ground syntax; checking need not materialize the potentially enormous
unary terms. Every represented premise remains subject to the composed checker.

No native `Form` freeness, internal checker, or arithmetic truth rule is assumed.
-/

namespace Hypermath.RecordEncoding

open GroundSyntax GroundDerivation GroundCode

def termTree : Term → Tree
  | .ground => .leaf
  | .apply term => .fork .leaf (termTree term)

def readTerm : Tree → Option Term
  | .leaf => some .ground
  | .fork .leaf tail => (readTerm tail).map Term.apply
  | _ => none

theorem readTerm_termTree (term : Term) : readTerm (termTree term) = some term := by
  induction term <;> simp_all [termTree, readTerm]

def tag (number : Nat) (payload : Tree) : Tree :=
  .fork (termTree (Term.ofDepth number)) payload

def readTag (tree : Tree) : Option Nat := (readTerm tree).map Term.depth

theorem readTag_number (number : Nat) :
    readTag (termTree (Term.ofDepth number)) = some number := by
  simp [readTag, readTerm_termTree, Term.depth_ofDepth]

def statementTree : Statement → Tree
  | .distinct left right => tag 0 (.fork (termTree left) (termTree right))
  | .continues left right => tag 1 (.fork (termTree left) (termTree right))
  | .orbits left right => tag 2 (.fork (termTree left) (termTree right))

def readStatement : Tree → Option Statement
  | .fork marker (.fork left right) => do
      let kind ← readTag marker
      let a ← readTerm left
      let b ← readTerm right
      match kind with
      | 0 => some (.distinct a b)
      | 1 => some (.continues a b)
      | 2 => some (.orbits a b)
      | _ => none
  | _ => none

theorem readStatement_statementTree (statement : Statement) :
    readStatement (statementTree statement) = some statement := by
  cases statement <;> simp [statementTree, tag, readStatement,
    readTag_number, readTerm_termTree]

def formulaTree : Formula → Tree
  | .structural statement => tag 0 (statementTree statement)
  | .similar left right => tag 1 (.fork (termTree left) (termTree right))
  | .notSimulation left right => tag 2 (.fork (termTree left) (termTree right))
  | .both left right => tag 3 (.fork (formulaTree left) (formulaTree right))

def readFormula : Tree → Option Formula
  | .fork marker payload =>
      match readTag marker, payload with
      | some 0, contents => (readStatement contents).map Formula.structural
      | some 1, .fork left right => do
          return .similar (← readTerm left) (← readTerm right)
      | some 2, .fork left right => do
          return .notSimulation (← readTerm left) (← readTerm right)
      | some 3, .fork left right => do
          return .both (← readFormula left) (← readFormula right)
      | _, _ => none
  | _ => none

theorem readFormula_formulaTree (formula : Formula) :
    readFormula (formulaTree formula) = some formula := by
  induction formula <;> simp_all [formulaTree, tag, readFormula,
    readTag_number, readTerm_termTree, readStatement_statementTree]

def recordTree : Record → Tree
  | .primitive rule => tag 0 (termTree (GroundSyntax.encode rule))
  | .closeContinues term premise => tag 1 (.fork (termTree term) (recordTree premise))
  | .closeDistinct left right premise =>
      tag 2 (.fork (termTree left) (.fork (termTree right) (recordTree premise)))
  | .closeOrbits term premise => tag 3 (.fork (termTree term) (recordTree premise))
  | .join first second => tag 4 (.fork (recordTree first) (recordTree second))
  | .projectLeft left right premise =>
      tag 5 (.fork (formulaTree left) (.fork (formulaTree right) (recordTree premise)))
  | .projectRight left right premise =>
      tag 6 (.fork (formulaTree left) (.fork (formulaTree right) (recordTree premise)))

def readRecord : Tree → Option Record
  | .fork marker payload =>
      match readTag marker, payload with
      | some 0, contents => do
          return .primitive (← GroundSyntax.decode (← readTerm contents))
      | some 1, .fork term premise => do
          return .closeContinues (← readTerm term) (← readRecord premise)
      | some 2, .fork left (.fork right premise) => do
          return .closeDistinct (← readTerm left) (← readTerm right) (← readRecord premise)
      | some 3, .fork term premise => do
          return .closeOrbits (← readTerm term) (← readRecord premise)
      | some 4, .fork first second => do
          return .join (← readRecord first) (← readRecord second)
      | some 5, .fork left (.fork right premise) => do
          return .projectLeft (← readFormula left) (← readFormula right) (← readRecord premise)
      | some 6, .fork left (.fork right premise) => do
          return .projectRight (← readFormula left) (← readFormula right) (← readRecord premise)
      | _, _ => none
  | _ => none

theorem readRecord_recordTree (record : Record) :
    readRecord (recordTree record) = some record := by
  induction record <;> simp_all [recordTree, tag, readRecord,
    readTag_number, readTerm_termTree, readFormula_formulaTree, GroundSyntax.decode_encode]

def unwrap (expected : Nat) : Tree → Option Tree
  | .fork marker payload => if readTag marker = some expected then some payload else none
  | _ => none

theorem unwrap_tag (number : Nat) (payload : Tree) :
    unwrap number (tag number payload) = some payload := by
  simp [unwrap, tag, readTag_number]

/-- The envelope values are format tags, not truth or representation ranks. -/
def recordCode (record : Record) : Nat := (tag 8 (recordTree record)).code
def formulaCode (formula : Formula) : Nat := (tag 9 (formulaTree formula)).code

def decodeRecord (code : Nat) : Option Record :=
  (GroundCode.decodeNumber code).bind (fun tree => (unwrap 8 tree).bind readRecord)

def decodeFormula (code : Nat) : Option Formula :=
  (GroundCode.decodeNumber code).bind (fun tree => (unwrap 9 tree).bind readFormula)

theorem decode_recordCode (record : Record) : decodeRecord (recordCode record) = some record := by
  simp [decodeRecord, recordCode, decode_code, unwrap_tag, readRecord_recordTree]

theorem decode_formulaCode (formula : Formula) :
    decodeFormula (formulaCode formula) = some formula := by
  simp [decodeFormula, formulaCode, decode_code, unwrap_tag, readFormula_formulaTree]

theorem decodeFormula_recordCode (record : Record) :
    decodeFormula (recordCode record) = none := by
  simp [decodeFormula, recordCode, decode_code, unwrap, tag, readTag_number]

theorem decodeRecord_formulaCode (formula : Formula) :
    decodeRecord (formulaCode formula) = none := by
  simp [decodeRecord, formulaCode, decode_code, unwrap, tag, readTag_number]

theorem recordCode_injective {first second : Record}
    (same : recordCode first = recordCode second) : first = second :=
  Option.some.inj ((decode_recordCode first).symm.trans
    ((congrArg decodeRecord same).trans (decode_recordCode second)))

theorem observe_recordCode {β : Type} (query : Record → β) (record : Record) :
    (decodeRecord (recordCode record)).map query = some (query record) := by
  rw [decode_recordCode]
  rfl

def recordTerm (record : Record) : Term := Term.ofDepth (recordCode record)
def formulaTerm (formula : Formula) : Term := Term.ofDepth (formulaCode formula)

theorem decode_recordTerm (record : Record) :
    decodeRecord (recordTerm record).depth = some record := by
  simp [recordTerm, Term.depth_ofDepth, decode_recordCode]

theorem decode_formulaTerm (formula : Formula) :
    decodeFormula (formulaTerm formula).depth = some formula := by
  simp [formulaTerm, Term.depth_ofDepth, decode_formulaCode]

def checkDecoded (record : Option Record) (formula : Option Formula) : Bool :=
  match record, formula with
  | some proof, some claim => GroundDerivation.check proof claim
  | _, _ => false

/-- Both inputs are encoded data; successful decoding alone is not proof acceptance. -/
def checkNumbers (record formula : Nat) : Bool :=
  checkDecoded (decodeRecord record) (decodeFormula formula)

def checkTerms (record formula : Term) : Bool := checkNumbers record.depth formula.depth

theorem checkNumbers_codes (record : Record) (formula : Formula) :
    checkNumbers (recordCode record) (formulaCode formula) =
      GroundDerivation.check record formula :=
  (congrArg (fun proof => checkDecoded proof (decodeFormula (formulaCode formula)))
    (decode_recordCode record)).trans
      (congrArg (checkDecoded (some record)) (decode_formulaCode formula))

theorem checkTerms_terms (record : Record) (formula : Formula) :
    checkTerms (recordTerm record) (formulaTerm formula) =
      GroundDerivation.check record formula := by
  simp [checkTerms, recordTerm, formulaTerm, Term.depth_ofDepth, checkNumbers_codes]

theorem checkNumbers_sound (model : GroundDerivation.Model) (record formula : Nat)
    (accepted : checkNumbers record formula = true) :
    ∃ claim, decodeFormula formula = some claim ∧ claim.holds model := by
  cases r : decodeRecord record with
  | none => simp [checkNumbers, checkDecoded, r] at accepted
  | some proof =>
      cases f : decodeFormula formula with
      | none => simp [checkNumbers, checkDecoded, r, f] at accepted
      | some claim =>
          exact ⟨claim, rfl, GroundDerivation.check_sound model proof claim
            (by simpa [checkNumbers, checkDecoded, r, f] using accepted)⟩

theorem checkTerms_quote {claim : Formula} (proof : Derivation claim) :
    checkTerms (recordTerm (quote proof)) (formulaTerm claim) = true := by
  rw [checkTerms_terms]
  exact check_quote proof

theorem recordTerm_injective {first second : Record}
    (same : recordTerm first = recordTerm second) : first = second :=
  Option.some.inj ((decode_recordTerm first).symm.trans
    ((congrArg (fun term => decodeRecord term.depth) same).trans (decode_recordTerm second)))

theorem observe_recordTerm {β : Type} (query : Record → β) (record : Record) :
    (decodeRecord (recordTerm record).depth).map query = some (query record) := by
  simp [decode_recordTerm]

def joinCodes (first second : Nat) : Option Nat := do
  let left ← decodeRecord first
  let right ← decodeRecord second
  return recordCode (.join left right)

theorem joinCodes_recordCode (first second : Record) :
    joinCodes (recordCode first) (recordCode second) = some (recordCode (.join first second)) := by
  simp [joinCodes, decode_recordCode]

/-- Preservation through an interpretation requires an actual recovery map. -/
theorem semantic_record_recovery {α : Type} (base : α) (step : α → α)
    (recover : α → Nat) (record : Record)
    (faithful : recover ((recordTerm record).interpret base step) = recordCode record) :
    decodeRecord (recover ((recordTerm record).interpret base step)) = some record := by
  rw [faithful]
  exact decode_recordCode record

end Hypermath.RecordEncoding
