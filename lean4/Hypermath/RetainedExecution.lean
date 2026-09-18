import Hypermath.TerminalRetention

/-!
# Retaining submitted execution frames through composition and finite layers

The payload contains the actual submitted frame, including its history. A
decoder never substitutes the canonical execution for that history. Thus an
altered or incomplete frame remains recoverable and remains rejected.
This is an executable host representation, not a native formation rule.
-/

namespace Hypermath.RetainedExecution

open GroundCode GroundDerivation RecordEncoding RecordMachine
open OperationalCorrespondence
open RuleSubstitution (listTree readList readList_listTree stateTree readState readState_stateTree)
open LayeredDerivation (Expression combine)

def instructionTree : Instruction → Tree
  | .primitive rule => tag 0 (recordTree (.primitive rule))
  | .closeContinues term => tag 1 (termTree term)
  | .closeDistinct left right => tag 2 (.fork (termTree left) (termTree right))
  | .closeOrbits term => tag 3 (termTree term)
  | .join => tag 4 .leaf
  | .projectLeft left right => tag 5 (.fork (formulaTree left) (formulaTree right))
  | .projectRight left right => tag 6 (.fork (formulaTree left) (formulaTree right))

def readInstruction : Tree → Option Instruction
  | .fork marker payload =>
    match readTag marker, payload with
    | some 0, tree => do
        match ← readRecord tree with
        | .primitive rule => return .primitive rule
        | _ => none
    | some 1, tree => (readTerm tree).map Instruction.closeContinues
    | some 2, .fork left right => do return .closeDistinct (← readTerm left) (← readTerm right)
    | some 3, tree => (readTerm tree).map Instruction.closeOrbits
    | some 4, .leaf => some .join
    | some 5, .fork left right => do return .projectLeft (← readFormula left) (← readFormula right)
    | some 6, .fork left right => do return .projectRight (← readFormula left) (← readFormula right)
    | _, _ => none
  | _ => none

theorem readInstruction_instructionTree (instruction : Instruction) :
    readInstruction (instructionTree instruction) = some instruction := by
  cases instruction <;> simp [instructionTree, readInstruction, tag, readTag_number,
    readRecord_recordTree, readTerm_termTree, readFormula_formulaTree]

/-- Envelope 13 retains all five fields, even when the frame is invalid. -/
def frameTree (frame : Frame) : Tree :=
  tag 13 (.fork (recordTree frame.record) (.fork (formulaTree frame.claim)
    (.fork (listTree instructionTree frame.todo)
      (.fork (stateTree frame.state) (listTree stateTree frame.history)))))

def readFrame (tree : Tree) : Option Frame := do
  let payload ← unwrap 13 tree
  match payload with
  | .fork record (.fork claim (.fork todo (.fork state history))) => do
      return ⟨← readRecord record, ← readFormula claim, ← readList readInstruction todo,
        ← readState state, ← readList readState history⟩
  | _ => none

theorem readFrame_frameTree (frame : Frame) : readFrame (frameTree frame) = some frame := by
  cases frame
  simp [readFrame, frameTree, unwrap_tag, readRecord_recordTree, readFormula_formulaTree,
    readState_stateTree, readList_listTree _ _ readInstruction_instructionTree,
    readList_listTree _ _ readState_stateTree]

theorem frameTree_injective {first second : Frame} (same : frameTree first = frameTree second) :
    first = second :=
  Option.some.inj ((readFrame_frameTree first).symm.trans
    ((congrArg readFrame same).trans (readFrame_frameTree second)))

def Surface : Nat → Type
  | 0 => Frame
  | _ + 1 => Expression

def payload : (layer : Nat) → Surface layer → Tree
  | 0, frame => frameTree frame
  | _ + 1, expression => expression.tree

def readPayload : (layer : Nat) → Tree → Option (Surface layer)
  | 0, tree => readFrame tree
  | _ + 1, tree => LayeredDerivation.readExpression tree

theorem readPayload_payload (layer : Nat) (surface : Surface layer) :
    readPayload layer (payload layer surface) = some surface := by
  cases layer with
  | zero => exact readFrame_frameTree surface
  | succ layer => exact LayeredDerivation.readExpression_tree surface

/-- Envelope 14 separates this frame-retaining protocol from record-only layers. -/
def encode (layer : Nat) (surface : Surface layer) : Tree :=
  tag 14 (tag layer (payload layer surface))

def decode (layer : Nat) (tree : Tree) : Option (Surface layer) := do
  let framed ← unwrap 14 tree
  let contents ← unwrap layer framed
  readPayload layer contents

theorem decode_encode (layer : Nat) (surface : Surface layer) :
    decode layer (encode layer surface) = some surface := by
  simp [decode, encode, unwrap_tag, readPayload_payload]

theorem wrong_layer_rejected (first second : Nat) (different : first ≠ second)
    (surface : Surface first) : decode second (encode first surface) = none := by
  simp [decode, encode, unwrap_tag, unwrap, tag, readTag_number, different]

theorem record_only_protocol_rejected (layer : Nat) (surface : LayeredDerivation.Surface layer) :
    decode layer (LayeredDerivation.encode layer surface) = none := by
  simp [decode, LayeredDerivation.encode, unwrap, tag, readTag_number]

/-- This inspection retains rejected frames too; `none` means malformed syntax.
Checking is a separate observation of the returned frames. -/
def inspect : (layer : Nat) → Surface layer → Option (List Frame)
  | 0, frame => some [frame]
  | layer + 1, expression => expression.run (fun code => do
      let lower ← decode layer code
      inspect layer lower)

def accepted (frames : Option (List Frame)) : Bool :=
  match frames with
  | none => false
  | some values => values.all Frame.accept

def check (layer : Nat) (surface : Surface layer) : Bool := accepted (inspect layer surface)

theorem accepted_combine (first second : Option (List Frame)) :
    accepted (combine first second) = (accepted first && accepted second) := by
  cases first <;> cases second <;> simp [accepted, combine, List.all_append]

def lift (layer : Nat) (surface : Surface layer) : Surface (layer + 1) :=
  .atom (encode layer surface)

def lowerAtom (layer : Nat) : Surface (layer + 1) → Option (Surface layer)
  | .atom code => decode layer code
  | _ => none

theorem lowerAtom_lift (layer : Nat) (surface : Surface layer) :
    lowerAtom layer (lift layer surface) = some surface := decode_encode layer surface

theorem inspect_lift (layer : Nat) (surface : Surface layer) :
    inspect (layer + 1) (lift layer surface) = inspect layer surface := by
  simp [inspect, lift, Expression.run, decode_encode]

theorem check_lift (layer : Nat) (surface : Surface layer) :
    check (layer + 1) (lift layer surface) = check layer surface := by
  simp [check, inspect_lift]

theorem inspect_seq (layer : Nat) (first second : Surface (layer + 1)) :
    inspect (layer + 1) (.seq first second) =
      combine (inspect (layer + 1) first) (inspect (layer + 1) second) := rfl

theorem check_seq (layer : Nat) (first second : Surface (layer + 1)) :
    check (layer + 1) (.seq first second) =
      (check (layer + 1) first && check (layer + 1) second) :=
  accepted_combine _ _

theorem lift_preserves_composition (layer : Nat) (first second : Surface (layer + 1)) :
    inspect (layer + 2) (lift (layer + 1) (.seq first second)) =
      inspect (layer + 2) (.seq (lift (layer + 1) first) (lift (layer + 1) second)) := by
  rw [inspect_lift, inspect_seq, inspect_seq, inspect_lift, inspect_lift]

/-- The common sequencing interface observes every submitted frame in order.
It does not identify this equality with a native Hypermath relation. -/
def sequencing (layer : Nat) : Sequential.Sequencing (Surface (layer + 1))
    (fun first second => inspect (layer + 1) first = inspect (layer + 1) second) where
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  operation := Expression.seq
  unit := Expression.empty
  respects := by
    intro x x' y y' hx hy
    change combine (inspect _ x) (inspect _ y) = combine (inspect _ x') (inspect _ y')
    rw [hx, hy]
  identity := fun value =>
    ⟨LayeredDerivation.combine_right_identity _, LayeredDerivation.combine_left_identity _⟩
  associative := fun x y z => LayeredDerivation.combine_associative _ _ _

def liftMap (layer : Nat) : Sequential.CompositionMap (sequencing layer) (sequencing (layer + 1)) where
  toFun := lift (layer + 1)
  respects := by
    intro first second same
    change inspect _ (lift _ first) = inspect _ (lift _ second)
    simpa only [inspect_lift] using same
  preserves_unit := inspect_lift (layer + 1) .empty
  preserves_operation := fun first second => lift_preserves_composition layer first second

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

theorem inspect_iterateLift (count layer : Nat) (surface : Surface layer) :
    inspect (layer + count) (iterateLift count layer surface) = inspect layer surface := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change inspect ((layer + count) + 1)
        (lift (layer + count) (iterateLift count layer surface)) = inspect layer surface
      rw [inspect_lift]
      exact ih

theorem check_iterateLift (count layer : Nat) (surface : Surface layer) :
    check (layer + count) (iterateLift count layer surface) = check layer surface := by
  simp [check, inspect_iterateLift]

/-- No acceptance premise: the complete operands and their rejection behavior survive. -/
theorem composition_lift_preserves (count layer : Nat)
    (first second : Surface (layer + 1)) :
    recoverThrough count (layer + 1)
        (iterateLift count (layer + 1) (.seq first second)) = some (.seq first second) ∧
    inspect ((layer + 1) + count)
        (iterateLift count (layer + 1) (.seq first second)) =
      combine (inspect (layer + 1) first) (inspect (layer + 1) second) ∧
    check ((layer + 1) + count)
        (iterateLift count (layer + 1) (.seq first second)) =
      (check (layer + 1) first && check (layer + 1) second) :=
  ⟨recoverThrough_iterateLift _ _ _, (inspect_iterateLift _ _ _).trans (inspect_seq _ _ _),
    (check_iterateLift _ _ _).trans (check_seq _ _ _)⟩

/-- Every field of the submitted frame survives, without replacing its history. -/
theorem submitted_frame_recovered (count : Nat) (frame : Frame) :
    recoverThrough count 0 (iterateLift count 0 frame) = some frame :=
  recoverThrough_iterateLift _ _ _

theorem submitted_frame_check (count : Nat) (frame : Frame) :
    check (0 + count) (iterateLift count 0 frame) = frame.accept := by
  rw [check_iterateLift]
  simp [check, inspect, accepted]

/-- A completed execution may become a new atom; lower execution is not continued. -/
theorem finished_frame_check (count : Nat) (record : Record) (claim : Formula) :
    check (0 + count) (iterateLift count 0 (TerminalRetention.finished record claim)) =
      GroundDerivation.check record claim := by
  rw [submitted_frame_check, TerminalRetention.finished_check]

theorem accepted_frame_sound (model : GroundDerivation.Model) (frame : Frame)
    (passes : frame.accept = true) : frame.claim.holds model := by
  have tracePass : checkTrace frame.record frame.claim frame.history = true := by
    simp only [Frame.accept, Bool.and_eq_true] at passes
    exact passes.1.2
  exact checkTrace_sound model frame.record frame.claim frame.history tracePass

theorem checked_surface_sound (model : GroundDerivation.Model) (layer : Nat)
    (surface : Surface layer) (frames : List Frame)
    (decoded : inspect layer surface = some frames) (passes : check layer surface = true) :
    ∀ frame ∈ frames, frame.claim.holds model := by
  have each : ∀ frame ∈ frames, frame.accept = true := by
    simpa [check, decoded, accepted, List.all_eq_true] using passes
  intro frame member
  exact accepted_frame_sound model frame (each frame member)

namespace Checks

def firstRecord : Record := .primitive .groundSelf
def secondRecord : Record := .primitive (.diff .ground)
def first : Frame := TerminalRetention.finished firstRecord firstRecord.conclusion
def second : Frame := TerminalRetention.finished secondRecord secondRecord.conclusion
def erased : Frame := { first with history := [] }
def wrongState : Frame := { first with state := none }
def incomplete : Frame := { first with todo := [.join] }
def composed : Surface 1 := .seq (lift 0 first) (lift 0 second)

theorem erased_record_still_valid : GroundDerivation.check erased.record erased.claim = true := by decide
theorem erased_frame_rejected : erased.accept = false := by decide
theorem wrong_state_rejected : wrongState.accept = false := by decide
theorem incomplete_frame_rejected : incomplete.accept = false := by decide

theorem erased_history_retained (count : Nat) :
    (recoverThrough count 0 (iterateLift count 0 erased)).map Frame.history = some [] := by
  rw [submitted_frame_recovered]
  rfl

theorem erased_history_rejected (count : Nat) :
    check (0 + count) (iterateLift count 0 erased) = false := by
  rw [submitted_frame_check, erased_frame_rejected]

theorem composed_frames_retained (count : Nat) :
    inspect (1 + count) (iterateLift count 1 composed) = some [first, second] := by
  rw [inspect_iterateLift]
  change inspect 1 (.seq (lift 0 first) (lift 0 second)) = some [first, second]
  rw [inspect_seq, inspect_lift, inspect_lift]
  rfl

theorem composed_frames_accepted (count : Nat) :
    check (1 + count) (iterateLift count 1 composed) = true := by
  rw [check_iterateLift]
  decide

theorem erased_composition_rejected (count : Nat) :
    check (1 + count) (iterateLift count 1 (.seq (lift 0 first) (lift 0 erased))) = false := by
  rw [check_iterateLift, check_seq, check_lift, check_lift]
  decide

theorem repeated_frames_retained :
    inspect 1 (.seq (lift 0 first) (lift 0 first)) = some [first, first] := by
  rw [inspect_seq, inspect_lift]
  rfl

theorem encoded_erasure_still_decodes : readFrame (frameTree erased) = some erased :=
  readFrame_frameTree erased

def probe : IO Unit := do
  IO.println "START retained executions: exact frames, erased history, endpoint and completion checks"
  unless check 3 (iterateLift 2 1 composed) do
    throw (IO.userError "valid retained composition failed")
  for frame in [erased, wrongState, incomplete] do
    unless readFrame (frameTree frame) == some frame do
      throw (IO.userError "invalid submitted frame was not retained exactly")
    if check 3 (iterateLift 3 0 frame) then
      throw (IO.userError "invalid execution frame became accepted after lifting")
  IO.println "PASS retained executions: valid composition accepted; altered frames retained and rejected"

end Checks

end Hypermath.RetainedExecution
