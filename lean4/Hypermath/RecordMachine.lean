import Hypermath.RecordEncoding

/-!
# Explicit execution of the finite record checker

Each instruction performs one primitive introduction, predicate close, join,
or projection. A failed premise poisons the state. The compiler retains each
record node as one instruction, and the machine agrees with the existing
recursive checker on every record, including invalid records.

This is host execution infrastructure to be represented and related to native
Hypermath rules. It is not a native execution axiom or an acceptance rule.
-/

namespace Hypermath.RecordMachine

open GroundSyntax GroundDerivation

inductive Instruction where
  | primitive (rule : AxiomInstance)
  | closeContinues (term : Term)
  | closeDistinct (left right : Term)
  | closeOrbits (term : Term)
  | join
  | projectLeft (left right : Formula)
  | projectRight (left right : Formula)
  deriving DecidableEq, Repr

/-- `none` is a failed run; `some []` is a successful empty stack. -/
abbrev State := Option (List Formula)

def replace (expected result : Formula) : State → State
  | some (actual :: rest) => if actual = expected then some (result :: rest) else none
  | _ => none

/-- No call to `Record.valid`, `check`, or a typed proof object occurs here. -/
def step : Instruction → State → State
  | .primitive rule, some stack => some (.structural rule.conclusion :: stack)
  | .closeContinues term, state =>
      replace (.structural (.continues term .ground)) (.similar term .ground) state
  | .closeDistinct left right, state =>
      replace (.structural (.distinct left right)) (.notSimulation left right) state
  | .closeOrbits term, state =>
      replace (.structural (.orbits (.apply (.apply term)) term))
        (.similar (.apply (.apply term)) term) state
  | .join, some (right :: left :: rest) => some (.both left right :: rest)
  | .projectLeft left right, state => replace (.both left right) left state
  | .projectRight left right, state => replace (.both left right) right state
  | _, _ => none

@[simp] theorem step_failed (instruction : Instruction) : step instruction none = none := by
  cases instruction <;> rfl

def execute : List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => execute rest (step instruction state)

@[simp] theorem execute_failed (program : List Instruction) : execute program none = none := by
  induction program with
  | nil => rfl
  | cons instruction rest ih => simpa [execute] using ih

theorem execute_append (first second : List Instruction) (state : State) :
    execute (first ++ second) state = execute second (execute first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [execute] using ih (step instruction state)

/-- Premises precede the instruction that consumes them; both join branches run. -/
def program : Record → List Instruction
  | .primitive rule => [.primitive rule]
  | .closeContinues term premise => program premise ++ [.closeContinues term]
  | .closeDistinct left right premise => program premise ++ [.closeDistinct left right]
  | .closeOrbits term premise => program premise ++ [.closeOrbits term]
  | .join first second => program first ++ program second ++ [.join]
  | .projectLeft left right premise => program premise ++ [.projectLeft left right]
  | .projectRight left right premise => program premise ++ [.projectRight left right]

/-- Exact stack effect, for valid and invalid input, in every stack context. -/
theorem execute_program (record : Record) (stack : List Formula) :
    execute (program record) (some stack) =
      if record.valid then some (record.conclusion :: stack) else none := by
  induction record generalizing stack with
  | primitive rule => rfl
  | closeContinues term premise ih =>
      simp only [program, execute_append, ih]
      cases h : premise.valid <;>
        simp [h, Record.valid, Record.conclusion, execute, step, replace]
  | closeDistinct left right premise ih =>
      simp only [program, execute_append, ih]
      cases h : premise.valid <;>
        simp [h, Record.valid, Record.conclusion, execute, step, replace]
  | closeOrbits term premise ih =>
      simp only [program, execute_append, ih]
      cases h : premise.valid <;>
        simp [h, Record.valid, Record.conclusion, execute, step, replace]
  | join first second ihFirst ihSecond =>
      simp only [program, execute_append, ihFirst]
      cases firstValid : first.valid <;> cases secondValid : second.valid <;>
        simp [firstValid, secondValid, ihSecond, Record.valid, Record.conclusion, execute, step]
  | projectLeft left right premise ih =>
      simp only [program, execute_append, ih]
      cases h : premise.valid <;>
        simp [h, Record.valid, Record.conclusion, execute, step, replace]
  | projectRight left right premise ih =>
      simp only [program, execute_append, ih]
      cases h : premise.valid <;>
        simp [h, Record.valid, Record.conclusion, execute, step, replace]

def check (record : Record) (claimed : Formula) : Bool :=
  decide (execute (program record) (some []) = some [claimed])

theorem check_agrees (record : Record) (claimed : Formula) :
    check record claimed = GroundDerivation.check record claimed := by
  simp only [check, execute_program]
  cases h : record.valid <;> simp [h, GroundDerivation.check]

theorem check_sound (model : GroundDerivation.Model) (record : Record) (claimed : Formula)
    (accepted : check record claimed = true) : claimed.holds model :=
  GroundDerivation.check_sound model record claimed ((check_agrees record claimed) ▸ accepted)

theorem check_quote {claimed : Formula} (proof : Derivation claimed) :
    check (quote proof) claimed = true := by
  rw [check_agrees]
  exact GroundDerivation.check_quote proof

def checkDecoded : Option Record → Option Formula → Bool
  | some record, some formula => check record formula
  | _, _ => false

/-- Same packed input protocol, now executing individual rule instructions. -/
def checkNumbers (record formula : Nat) : Bool :=
  checkDecoded (RecordEncoding.decodeRecord record) (RecordEncoding.decodeFormula formula)

theorem checkNumbers_agrees (record formula : Nat) :
    checkNumbers record formula = RecordEncoding.checkNumbers record formula := by
  unfold checkNumbers RecordEncoding.checkNumbers
  cases RecordEncoding.decodeRecord record <;> cases RecordEncoding.decodeFormula formula <;>
    simp [checkDecoded, RecordEncoding.checkDecoded, check_agrees]

theorem checkNumbers_codes (record : Record) (formula : Formula) :
    checkNumbers (RecordEncoding.recordCode record) (RecordEncoding.formulaCode formula) =
      GroundDerivation.check record formula :=
  (checkNumbers_agrees _ _).trans (RecordEncoding.checkNumbers_codes record formula)

theorem checkNumbers_sound (model : GroundDerivation.Model) (record formula : Nat)
    (accepted : checkNumbers record formula = true) :
    ∃ decoded, RecordEncoding.decodeFormula formula = some decoded ∧ decoded.holds model := by
  exact RecordEncoding.checkNumbers_sound model record formula
    ((checkNumbers_agrees record formula) ▸ accepted)

/-- One recorded state after every instruction, including failed states. -/
def trace : List Instruction → State → List State
  | [], _ => []
  | instruction :: rest, state =>
      let next := step instruction state
      next :: trace rest next

/-- Checks every transition and requires the exact number of recorded states. -/
def replay : List Instruction → State → List State → Bool
  | [], _, [] => true
  | instruction :: rest, state, claimed :: tail =>
      decide (claimed = step instruction state) && replay rest claimed tail
  | _, _, _ => false

theorem replay_iff (instructions : List Instruction) (state : State) (recorded : List State) :
    replay instructions state recorded = true ↔ recorded = trace instructions state := by
  induction instructions generalizing state recorded with
  | nil => cases recorded <;> simp [replay, trace]
  | cons instruction rest ih =>
      cases recorded with
      | nil => simp [replay, trace]
      | cons claimed tail =>
          simp only [replay, Bool.and_eq_true, decide_eq_true_eq, ih, trace, List.cons.injEq]
          constructor
          · rintro ⟨rfl, h⟩
            exact ⟨rfl, h⟩
          · rintro ⟨rfl, h⟩
            exact ⟨rfl, h⟩

theorem replay_trace (instructions : List Instruction) (state : State) :
    replay instructions state (trace instructions state) = true :=
  (replay_iff instructions state _).mpr rfl

theorem replay_unique (instructions : List Instruction) (state : State)
    (first second : List State) (hFirst : replay instructions state first = true)
    (hSecond : replay instructions state second = true) : first = second :=
  ((replay_iff instructions state first).mp hFirst).trans
    ((replay_iff instructions state second).mp hSecond).symm

/-- The final recorded state, or the supplied initial state for an empty trace. -/
def endpoint : State → List State → State
  | state, [] => state
  | _, next :: rest => endpoint next rest

theorem endpoint_trace (instructions : List Instruction) (state : State) :
    endpoint state (trace instructions state) = execute instructions state := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih => simpa [trace, endpoint, execute] using ih (step instruction state)

/-- A submitted trace is data. Both its steps and final claim are checked. -/
def checkTrace (record : Record) (claimed : Formula) (recorded : List State) : Bool :=
  replay (program record) (some []) recorded &&
    decide (endpoint (some []) recorded = some [claimed])

theorem checkTrace_trace (record : Record) (claimed : Formula) :
    checkTrace record claimed (trace (program record) (some [])) = check record claimed := by
  simp [checkTrace, replay_trace, endpoint_trace, check]

theorem checkTrace_iff (record : Record) (claimed : Formula) (recorded : List State) :
    checkTrace record claimed recorded = true ↔
      recorded = trace (program record) (some []) ∧
        GroundDerivation.check record claimed = true := by
  constructor
  · intro accepted
    have parts : replay (program record) (some []) recorded = true ∧
        endpoint (some []) recorded = some [claimed] := by
      simpa [checkTrace] using accepted
    have exactTrace := (replay_iff (program record) (some []) recorded).mp parts.1
    refine ⟨exactTrace, ?_⟩
    rw [exactTrace, checkTrace_trace, check_agrees] at accepted
    exact accepted
  · rintro ⟨rfl, accepted⟩
    simpa [checkTrace_trace, check_agrees] using accepted

theorem checkTrace_sound (model : GroundDerivation.Model) (record : Record)
    (claimed : Formula) (recorded : List State)
    (accepted : checkTrace record claimed recorded = true) : claimed.holds model :=
  GroundDerivation.check_sound model record claimed ((checkTrace_iff record claimed recorded).mp accepted).2

theorem checkTrace_quote {claimed : Formula} (proof : Derivation claimed) :
    checkTrace (quote proof) claimed (trace (program (quote proof)) (some [])) = true := by
  rw [checkTrace_trace]
  exact check_quote proof

def nodeCount : Record → Nat
  | .primitive _ => 1
  | .closeContinues _ premise | .closeDistinct _ _ premise | .closeOrbits _ premise
    | .projectLeft _ _ premise | .projectRight _ _ premise => nodeCount premise + 1
  | .join first second => nodeCount first + nodeCount second + 1

theorem program_length (record : Record) : (program record).length = nodeCount record := by
  induction record <;> simp_all [program, nodeCount, List.length_append, Nat.add_assoc]

theorem trace_length (instructions : List Instruction) (state : State) :
    (trace instructions state).length = instructions.length := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih => simp [trace, ih]

theorem compiled_trace_length (record : Record) (state : State) :
    (trace (program record) state).length = nodeCount record :=
  (trace_length (program record) state).trans (program_length record)

end Hypermath.RecordMachine
