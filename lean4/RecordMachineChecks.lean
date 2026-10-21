import Hypermath.RecordMachine
import Hypermath.RuleSubstitution

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

namespace Hypermath.RuleSubstitutionChecks

open GroundSyntax GroundDerivation RuleSubstitution

def groundClaim : Formula := .structural (.continues .ground .ground)
def otherClaim : Formula := .structural (.distinct (.apply .ground) .ground)

theorem missing_substitution_rejected :
    (Application.mk .diff ⟨[], []⟩).run (some []) = none := rfl

theorem surplus_substitution_rejected :
    (Application.mk .diff ⟨[.ground, .ground], []⟩).run (some []) = none := rfl

theorem wrong_substitution_sort_rejected :
    (Application.mk .diff ⟨[], [groundClaim]⟩).run (some []) = none := rfl

theorem unused_formula_argument_rejected :
    (Application.mk .groundSelf ⟨[], [groundClaim]⟩).run (some []) = none := rfl

theorem unbound_term_variable_rejected :
    (TermPattern.variable 1).instantiate ⟨[.ground], []⟩ = none := rfl

theorem unbound_formula_variable_rejected :
    (FormulaPattern.variable 1).instantiate ⟨[], [groundClaim]⟩ = none := rfl

theorem substituted_rule_checks_premise :
    (Application.mk .closeContinues ⟨[.ground], []⟩).run (some [otherClaim]) = none := rfl

theorem join_premise_order_matters :
    (Application.mk .join ⟨[], [groundClaim, otherClaim]⟩).run
      (some [otherClaim, groundClaim]) = some [.both groundClaim otherClaim] ∧
    (Application.mk .join ⟨[], [groundClaim, otherClaim]⟩).run
      (some [groundClaim, otherClaim]) = none := by
  exact ⟨rfl, rfl⟩

theorem untouched_stack_is_retained :
    (Application.mk .projectLeft ⟨[], [groundClaim, otherClaim]⟩).run
      (some [.both groundClaim otherClaim, otherClaim]) = some [groundClaim, otherClaim] := rfl

theorem poisoned_input_remains_failed :
    (Application.mk .groundSelf ⟨[], []⟩).run none = none := rfl

theorem unknown_rule_rejected : readRule 10 = none := rfl

theorem malformed_state_rejected : readState (.fork (.fork .leaf .leaf) .leaf) = none := rfl

theorem failed_and_empty_state_distinct : stateTree none ≠ stateTree (some []) := by
  intro equality
  cases equality

def correctCall : Call :=
  ⟨⟨.projectLeft, ⟨[], [groundClaim, otherClaim]⟩⟩, some [.both groundClaim otherClaim]⟩
def forgedCall : Call :=
  ⟨⟨.projectLeft, ⟨[], [groundClaim, otherClaim]⟩⟩, some [groundClaim]⟩

theorem encoded_call_checks_retained_premise :
    runCallNumber correctCall.code = some [groundClaim] ∧
    runCallNumber forgedCall.code = none := by
  simp only [runCallNumber_code]
  exact ⟨rfl, rfl⟩

theorem distinct_premises_have_distinct_call_terms : correctCall.toTerm ≠ forgedCall.toTerm := by
  intro equality
  have same := call_toTerm_injective equality
  cases same

theorem encoded_hidden_failure_rejected :
    encodedCheck RecordMachineChecks.hiddenFailure groundClaim = false := by
  rw [encodedCheck_agrees]
  rfl

theorem encoded_example_accepted :
    encodedCheck RecordMachineChecks.exampleRecord RecordMachineChecks.exampleRecord.conclusion = true := by
  rw [encodedCheck_agrees]
  rfl

def main : IO Unit := do
  let accepted := encodedCheck RecordMachineChecks.exampleRecord
    RecordMachineChecks.exampleRecord.conclusion
  let rejected := encodedCheck RecordMachineChecks.hiddenFailure groundClaim
  let first := runCallNumber correctCall.code
  let second := runCallNumber forgedCall.code
  if !accepted || rejected || first != some [groundClaim] || second != none then
    throw (IO.userError "schema substitution and retained-call execution probe failed")
  IO.println "schema execution: encoded proof accepted; hidden failure and forged premise rejected"
  IO.println s!"retained correct-call representation: {correctCall.tree.size} prefix bits"

end Hypermath.RuleSubstitutionChecks

#eval Hypermath.RuleSubstitutionChecks.main

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

#print axioms Hypermath.RuleSubstitution.step_agrees
#print axioms Hypermath.RuleSubstitution.execute_agrees
#print axioms Hypermath.RuleSubstitution.execute_program
#print axioms Hypermath.RuleSubstitution.check_agrees
#print axioms Hypermath.RuleSubstitution.check_sound
#print axioms Hypermath.RuleSubstitution.check_quote
#print axioms Hypermath.RuleSubstitution.readList_listTree
#print axioms Hypermath.RuleSubstitution.readRule_index
#print axioms Hypermath.RuleSubstitution.readApplication_tree
#print axioms Hypermath.RuleSubstitution.decode_code
#print axioms Hypermath.RuleSubstitution.decode_toTerm
#print axioms Hypermath.RuleSubstitution.toTerm_injective
#print axioms Hypermath.RuleSubstitution.runNumber_code
#print axioms Hypermath.RuleSubstitution.runTerm_toTerm
#print axioms Hypermath.RuleSubstitution.formula_code_rejected
#print axioms Hypermath.RuleSubstitution.record_code_rejected
#print axioms Hypermath.RuleSubstitution.no_rule_only_instantiation
#print axioms Hypermath.RuleSubstitution.readState_stateTree
#print axioms Hypermath.RuleSubstitution.readCall_tree
#print axioms Hypermath.RuleSubstitution.decodeCall_code
#print axioms Hypermath.RuleSubstitution.decodeCall_toTerm
#print axioms Hypermath.RuleSubstitution.call_toTerm_injective
#print axioms Hypermath.RuleSubstitution.runCallNumber_code
#print axioms Hypermath.RuleSubstitution.runCallTerm_toTerm
#print axioms Hypermath.RuleSubstitution.encodedStep_agrees
#print axioms Hypermath.RuleSubstitution.encodedExecute_agrees
#print axioms Hypermath.RuleSubstitution.encodedExecute_program
#print axioms Hypermath.RuleSubstitution.encodedCheck_agrees
#print axioms Hypermath.RuleSubstitution.encodedCheck_sound
#print axioms Hypermath.RuleSubstitution.encodedCheck_quote
#print axioms Hypermath.RuleSubstitutionChecks.missing_substitution_rejected
#print axioms Hypermath.RuleSubstitutionChecks.surplus_substitution_rejected
#print axioms Hypermath.RuleSubstitutionChecks.wrong_substitution_sort_rejected
#print axioms Hypermath.RuleSubstitutionChecks.unused_formula_argument_rejected
#print axioms Hypermath.RuleSubstitutionChecks.unbound_term_variable_rejected
#print axioms Hypermath.RuleSubstitutionChecks.unbound_formula_variable_rejected
#print axioms Hypermath.RuleSubstitutionChecks.substituted_rule_checks_premise
#print axioms Hypermath.RuleSubstitutionChecks.join_premise_order_matters
#print axioms Hypermath.RuleSubstitutionChecks.untouched_stack_is_retained
#print axioms Hypermath.RuleSubstitutionChecks.poisoned_input_remains_failed
#print axioms Hypermath.RuleSubstitutionChecks.unknown_rule_rejected
#print axioms Hypermath.RuleSubstitutionChecks.malformed_state_rejected
#print axioms Hypermath.RuleSubstitutionChecks.failed_and_empty_state_distinct
#print axioms Hypermath.RuleSubstitutionChecks.encoded_call_checks_retained_premise
#print axioms Hypermath.RuleSubstitutionChecks.distinct_premises_have_distinct_call_terms
#print axioms Hypermath.RuleSubstitutionChecks.encoded_hidden_failure_rejected
#print axioms Hypermath.RuleSubstitutionChecks.encoded_example_accepted
