import Hypermath.RecordMachine

namespace Hypermath.RecordMachineChecks

open GroundSyntax GroundDerivation
open RecordMachine (Instruction State)

def exampleRecord : Record := quote (separation .ground)
def groundClaim : Formula := .structural (.continues .ground .ground)
def validGroundRecord : Record := .primitive .groundSelf
def invalidGroundRecord : Record := .projectLeft groundClaim groundClaim validGroundRecord

theorem example_accepted : RecordMachine.check exampleRecord exampleRecord.conclusion = true := rfl

theorem invalid_projection_rejected :
    RecordMachine.check invalidGroundRecord groundClaim = false := rfl

theorem same_conclusion_different_execution :
    validGroundRecord.conclusion = invalidGroundRecord.conclusion ∧
    RecordMachine.check validGroundRecord groundClaim = true ∧
    RecordMachine.check invalidGroundRecord groundClaim = false := by
  exact ⟨rfl, rfl, rfl⟩

def hiddenFailure : Record := .projectLeft groundClaim (.similar (.apply .ground) .ground)
  (.join validGroundRecord (.closeContinues (.apply .ground) (.primitive (.diff .ground))))

theorem projection_cannot_hide_failed_premise :
    RecordMachine.check hiddenFailure groundClaim = false := rfl

theorem stack_underflow_rejected : RecordMachine.step .join (some []) = none := rfl

theorem wrong_predicate_rejected :
    RecordMachine.check (.closeContinues (.apply .ground) (.primitive (.diff .ground)))
      (.similar (.apply .ground) .ground) = false := rfl

theorem wrong_argument_rejected :
    RecordMachine.check (.closeOrbits (.apply .ground) (.primitive (.box .ground)))
      (.similar (.apply (.apply (.apply .ground))) (.apply .ground)) = false := rfl

theorem later_primitive_cannot_restore_failure :
    RecordMachine.execute [.join, .primitive .groundSelf] (some []) = none := rfl

theorem correct_trace_accepted :
    RecordMachine.checkTrace validGroundRecord groundClaim [some [groundClaim]] = true := rfl

theorem omitted_step_rejected :
    RecordMachine.checkTrace validGroundRecord groundClaim [] = false := rfl

theorem extra_step_rejected :
    RecordMachine.checkTrace validGroundRecord groundClaim
      [some [groundClaim], some [groundClaim]] = false := rfl

theorem forged_state_rejected :
    RecordMachine.checkTrace validGroundRecord groundClaim [some []] = false := rfl

theorem wrong_trace_claim_rejected :
    RecordMachine.checkTrace validGroundRecord (.similar .ground .ground)
      [some [groundClaim]] = false := rfl

theorem trace_for_other_record_rejected :
    RecordMachine.checkTrace invalidGroundRecord groundClaim [some [groundClaim]] = false := rfl

/-- A faithful trace of a rejected record is replayable, but is not acceptance. -/
theorem accurate_failure_trace_not_acceptance :
    RecordMachine.replay (RecordMachine.program invalidGroundRecord) (some [])
      (RecordMachine.trace (RecordMachine.program invalidGroundRecord) (some [])) = true ∧
    RecordMachine.checkTrace invalidGroundRecord groundClaim
      (RecordMachine.trace (RecordMachine.program invalidGroundRecord) (some [])) = false := by
  exact ⟨rfl, rfl⟩

theorem five_instructions_for_separation : (RecordMachine.program exampleRecord).length = 5 := rfl

theorem packed_example_accepted :
    RecordMachine.checkNumbers (RecordEncoding.recordCode exampleRecord)
      (RecordEncoding.formulaCode exampleRecord.conclusion) = true := by
  rw [RecordMachine.checkNumbers_codes]
  rfl

theorem packed_wrong_sort_rejected :
    RecordMachine.checkNumbers (RecordEncoding.formulaCode groundClaim)
      (RecordEncoding.formulaCode groundClaim) = false := by
  unfold RecordMachine.checkNumbers
  rw [RecordEncoding.decodeRecord_formulaCode]
  rfl

theorem empty_packed_input_rejected : RecordMachine.checkNumbers 0 0 = false := by
  simp [RecordMachine.checkNumbers, RecordMachine.checkDecoded, RecordEncoding.decodeRecord,
    RecordEncoding.decodeFormula, GroundCode.decodeNumber, GroundCode.unpack, GroundCode.parse]

def main : IO Unit := do
  let accepted := RecordMachine.checkNumbers (RecordEncoding.recordCode exampleRecord)
    (RecordEncoding.formulaCode exampleRecord.conclusion)
  let rejected := RecordMachine.check hiddenFailure groundClaim
  let traceRejected := RecordMachine.checkTrace invalidGroundRecord groundClaim
    [some [groundClaim]]
  if !accepted || rejected || traceRejected then
    throw (IO.userError "record-machine execution probe failed")
  IO.println "record-machine execution: encoded acceptance, failed premise, and forged trace checked"

end Hypermath.RecordMachineChecks

#eval Hypermath.RecordMachineChecks.main

#print axioms Hypermath.RecordMachine.step_failed
#print axioms Hypermath.RecordMachine.execute_failed
#print axioms Hypermath.RecordMachine.execute_append
#print axioms Hypermath.RecordMachine.execute_program
#print axioms Hypermath.RecordMachine.check_agrees
#print axioms Hypermath.RecordMachine.check_sound
#print axioms Hypermath.RecordMachine.check_quote
#print axioms Hypermath.RecordMachine.checkNumbers_agrees
#print axioms Hypermath.RecordMachine.checkNumbers_codes
#print axioms Hypermath.RecordMachine.checkNumbers_sound
#print axioms Hypermath.RecordMachine.replay_iff
#print axioms Hypermath.RecordMachine.replay_trace
#print axioms Hypermath.RecordMachine.replay_unique
#print axioms Hypermath.RecordMachine.endpoint_trace
#print axioms Hypermath.RecordMachine.checkTrace_trace
#print axioms Hypermath.RecordMachine.checkTrace_iff
#print axioms Hypermath.RecordMachine.checkTrace_sound
#print axioms Hypermath.RecordMachine.checkTrace_quote
#print axioms Hypermath.RecordMachine.program_length
#print axioms Hypermath.RecordMachine.trace_length
#print axioms Hypermath.RecordMachine.compiled_trace_length
#print axioms Hypermath.RecordMachineChecks.example_accepted
#print axioms Hypermath.RecordMachineChecks.invalid_projection_rejected
#print axioms Hypermath.RecordMachineChecks.same_conclusion_different_execution
#print axioms Hypermath.RecordMachineChecks.projection_cannot_hide_failed_premise
#print axioms Hypermath.RecordMachineChecks.stack_underflow_rejected
#print axioms Hypermath.RecordMachineChecks.wrong_predicate_rejected
#print axioms Hypermath.RecordMachineChecks.wrong_argument_rejected
#print axioms Hypermath.RecordMachineChecks.later_primitive_cannot_restore_failure
#print axioms Hypermath.RecordMachineChecks.correct_trace_accepted
#print axioms Hypermath.RecordMachineChecks.omitted_step_rejected
#print axioms Hypermath.RecordMachineChecks.extra_step_rejected
#print axioms Hypermath.RecordMachineChecks.forged_state_rejected
#print axioms Hypermath.RecordMachineChecks.wrong_trace_claim_rejected
#print axioms Hypermath.RecordMachineChecks.trace_for_other_record_rejected
#print axioms Hypermath.RecordMachineChecks.accurate_failure_trace_not_acceptance
#print axioms Hypermath.RecordMachineChecks.five_instructions_for_separation
#print axioms Hypermath.RecordMachineChecks.packed_example_accepted
#print axioms Hypermath.RecordMachineChecks.packed_wrong_sort_rejected
#print axioms Hypermath.RecordMachineChecks.empty_packed_input_rejected
