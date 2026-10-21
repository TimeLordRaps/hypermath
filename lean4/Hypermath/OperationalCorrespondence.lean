import Hypermath.ContextualComposition

/-!
# Local correspondence sufficient for repeated checking and layer passage

These theorems state a sufficient interface for a native realization; they
do not supply one for the opaque source `Form` or `f2f`. The one-step law
applies to every state that decodes, not only freshly encoded states. Thus
its output stays in the domain on which subsequent steps are justified.
-/

namespace Hypermath.OperationalCorrespondence

universe u v w z

structure Representation (Config : Type u) (Native : Type v) where
  encode : Config → Native
  decode : Native → Option Config
  recover : ∀ config, decode (encode config) = some config

/-- A sufficient, decode-domain-closed simulation law. No condition is imposed
on native states outside that domain. This is stronger than an image-only law. -/
def Respects {C : Type u} {N : Type v} (view : Representation C N)
    (abstract : C → C) (concrete : N → N) : Prop :=
  ∀ state config, view.decode state = some config →
    view.decode (concrete state) = some (abstract config)

def run {C : Type u} (step : C → C) : Nat → C → C
  | 0, state => state
  | count + 1, state => run step count (step state)

theorem run_append {C : Type u} (step : C → C) (first second : Nat) (state : C) :
    run step (first + second) state = run step second (run step first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simpa [Nat.succ_add, run] using ih (step state)

theorem run_decodes {C : Type u} {N : Type v} (view : Representation C N)
    (abstract : C → C) (concrete : N → N) (correct : Respects view abstract concrete)
    (count : Nat) (state : N) (config : C) (decoded : view.decode state = some config) :
    view.decode (run concrete count state) = some (run abstract count config) := by
  induction count generalizing state config with
  | zero => exact decoded
  | succ count ih => exact ih (concrete state) (abstract config) (correct _ _ decoded)

theorem run_encoded {C : Type u} {N : Type v} (view : Representation C N)
    (abstract : C → C) (concrete : N → N) (correct : Respects view abstract concrete)
    (count : Nat) (config : C) :
    view.decode (run concrete count (view.encode config)) = some (run abstract count config) :=
  run_decodes view abstract concrete correct count _ config (view.recover config)

/-- A layer passage preserves every decoded configuration, including rejected
ones and noncanonical representations reached by preceding native steps. -/
def LiftRespects {C : Type u} {N : Type v} {M : Type w}
    (lower : Representation C N) (upper : Representation C M) (lift : N → M) : Prop :=
  ∀ state config, lower.decode state = some config → upper.decode (lift state) = some config

/-- Adjacent layer correspondences compose without a canonicalization premise. -/
theorem lift_compose {C : Type u} {N : Type v} {M : Type w} {P : Type z}
    (first : Representation C N) (middle : Representation C M) (last : Representation C P)
    (liftFirst : N → M) (liftSecond : M → P)
    (correctFirst : LiftRespects first middle liftFirst)
    (correctSecond : LiftRespects middle last liftSecond) :
    LiftRespects first last (fun state => liftSecond (liftFirst state)) := by
  intro state config decoded
  exact correctSecond _ _ (correctFirst _ _ decoded)

theorem lift_run_decodes {C : Type u} {N : Type v} {M : Type w}
    (lower : Representation C N) (upper : Representation C M)
    (abstract : C → C) (concrete : N → N) (correct : Respects lower abstract concrete)
    (lift : N → M) (liftCorrect : LiftRespects lower upper lift)
    (count : Nat) (state : N) (config : C) (decoded : lower.decode state = some config) :
    upper.decode (lift (run concrete count state)) = some (run abstract count config) :=
  liftCorrect _ _ (run_decodes lower abstract concrete correct count state config decoded)

/-- Execute before or after the layer passage: decoded configurations agree.
The native values need not have identical encodings. -/
theorem run_lift_commutes {C : Type u} {N : Type v} {M : Type w}
    (lower : Representation C N) (upper : Representation C M)
    (abstract : C → C) (lowerStep : N → N) (upperStep : M → M)
    (lowerCorrect : Respects lower abstract lowerStep)
    (upperCorrect : Respects upper abstract upperStep)
    (lift : N → M) (liftCorrect : LiftRespects lower upper lift)
    (count : Nat) (state : N) (config : C) (decoded : lower.decode state = some config) :
    upper.decode (lift (run lowerStep count state)) =
      upper.decode (run upperStep count (lift state)) :=
  (lift_run_decodes lower upper abstract lowerStep lowerCorrect lift liftCorrect
    count state config decoded).trans
    (run_decodes upper abstract upperStep upperCorrect count (lift state) config
      (liftCorrect _ _ decoded)).symm

open GroundDerivation RecordMachine

/-- The original derivation and claim remain present throughout execution.
Remaining instructions, current state and full canonical history are data. -/
structure Frame where
  record : Record
  claim : Formula
  todo : List Instruction
  state : State
  history : List State
  deriving DecidableEq, Repr

def Frame.initial (record : Record) (claim : Formula) : Frame :=
  ⟨record, claim, program record, some [], []⟩

def Frame.advance (frame : Frame) : Frame :=
  match frame.todo with
  | [] => frame
  | instruction :: rest =>
      let next := RecordMachine.step instruction frame.state
      { frame with todo := rest, state := next, history := frame.history ++ [next] }

theorem run_frame (record : Record) (claim : Formula) (todo : List Instruction)
    (state : State) (history : List State) :
    run Frame.advance todo.length ⟨record, claim, todo, state, history⟩ =
      ⟨record, claim, [], execute todo state, history ++ trace todo state⟩ := by
  induction todo generalizing state history with
  | nil => simp [run, execute, trace]
  | cons instruction rest ih =>
      simp [run, Frame.advance, ih, execute, trace, List.append_assoc]

def Frame.accept (frame : Frame) : Bool :=
  frame.todo.isEmpty && checkTrace frame.record frame.claim frame.history &&
    decide (frame.state = endpoint (some []) frame.history)

/-- The entry point supplies its own empty context; acceptance replays every
transition, checks the final claim and binds the retained endpoint. -/
theorem accept_run_initial (record : Record) (claim : Formula) :
    (run Frame.advance (program record).length (Frame.initial record claim)).accept =
      GroundDerivation.check record claim := by
  rw [Frame.initial, run_frame]
  simp [Frame.accept, endpoint_trace, checkTrace_trace, RecordMachine.check_agrees]

/-- A local native step correspondence would suffice for exact recovery of
the original record, claim, and canonical execution history after checking. -/
theorem represented_run (N : Type v) (view : Representation Frame N)
    (concrete : N → N) (correct : Respects view Frame.advance concrete)
    (record : Record) (claim : Formula) :
    view.decode (run concrete (program record).length (view.encode (Frame.initial record claim))) =
      some ⟨record, claim, [], execute (program record) (some []), trace (program record) (some [])⟩ := by
  rw [run_encoded view Frame.advance concrete correct, Frame.initial, run_frame]
  rfl

/-- Includes rejection: a false check is represented as `some false`, not
silently dropped as a missing decode. This remains conditional on local laws. -/
theorem represented_check (N : Type v) (view : Representation Frame N)
    (concrete : N → N) (correct : Respects view Frame.advance concrete)
    (record : Record) (claim : Formula) :
    (view.decode (run concrete (program record).length
      (view.encode (Frame.initial record claim)))).map Frame.accept =
      some (GroundDerivation.check record claim) := by
  rw [run_encoded view Frame.advance concrete correct]
  exact congrArg some (accept_run_initial record claim)

/-- Specialization to the retained-premise join from the preceding construction. -/
theorem represented_composition_check (N : Type v) (view : Representation Frame N)
    (concrete : N → N) (correct : Respects view Frame.advance concrete)
    (first second : LayeredDerivation.Evidence) :
    let joint := ContextualComposition.compose first second
    (view.decode (run concrete (program joint.1).length
      (view.encode (Frame.initial joint.1 joint.2)))).map Frame.accept =
      some (GroundDerivation.check first.1 first.2 && GroundDerivation.check second.1 second.2) := by
  dsimp only
  rw [represented_check N view concrete correct, ContextualComposition.check_compose]

end Hypermath.OperationalCorrespondence
