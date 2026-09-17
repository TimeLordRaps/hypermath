import Hypermath.LayeredDerivation
import Hypermath.RuleSubstitution

/-!
# Composition through retained premise context

This construction connects the existing finite ground calculus, retained
rule/substitution calls, execution traces, and finite representation lifts.
The context is computed by executing both premise records. A supplied context
alone is not evidence of those premises. These are host definitions and proofs;
no identification of their evaluator with native `f2f` is assumed.
-/

namespace Hypermath.ContextualComposition

open GroundSyntax GroundDerivation
open RecordMachine (State Instruction program execute trace)
open LayeredDerivation (Evidence Surface iterateLift recoverThrough)

/-- The second derivation runs over the conclusion retained by the first.
Failure of either branch remains failure, in every initial stack context. -/
theorem joint_state (first second : Record) (context : List Formula) :
    RuleSubstitution.encodedExecute (program first ++ program second) (some context) =
      if first.valid && second.valid then
        some (second.conclusion :: first.conclusion :: context) else none := by
  rw [RuleSubstitution.encodedExecute_agrees, RecordMachine.execute_append,
    RecordMachine.execute_program]
  cases hfirst : first.valid <;> cases hsecond : second.valid <;>
    simp [hfirst, hsecond, RecordMachine.execute_program]

/-- Full execution histories concatenate at the actual intermediate state. -/
theorem trace_append (first second : List Instruction) (state : State) :
    trace (first ++ second) state =
      trace first state ++ trace second (execute first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp [trace, execute, ih]

/-- Both histories survive joining, including failed intermediate states. -/
theorem join_history (first second : Record) (state : State) :
    trace (program (.join first second)) state =
      trace (program first) state ++
      trace (program second) (execute (program first) state) ++
      trace [.join] (execute (program second) (execute (program first) state)) := by
  simp only [program, trace_append, RecordMachine.execute_append]

/-- A unary invocation carries a structured context and both substitutions.
Its serialized input is one value; its contents are not a single bare rule. -/
def joinCall (left right : Formula) (context : List Formula) : RuleSubstitution.Call :=
  ⟨⟨.join, ⟨[], [left, right]⟩⟩, some (right :: left :: context)⟩

theorem join_call_runs (left right : Formula) (context : List Formula) :
    RuleSubstitution.runCallNumber (joinCall left right context).code =
      some (.both left right :: context) := by
  rw [RuleSubstitution.runCallNumber_code]
  simp [joinCall, RuleSubstitution.Application.run, RuleSubstitution.Application.instantiate,
    RuleSubstitution.schema, RuleSubstitution.instantiateAll,
    RuleSubstitution.FormulaPattern.instantiate, RuleSubstitution.consume]

/-- Accepted premise records supply exactly the retained call's input state.
No premise stack or acceptance of a joined record is postulated. -/
theorem checked_context (first second : Evidence) (context : List Formula)
    (hfirst : GroundDerivation.check first.1 first.2 = true)
    (hsecond : GroundDerivation.check second.1 second.2 = true) :
    RuleSubstitution.encodedExecute (program first.1 ++ program second.1) (some context) =
      (joinCall first.2 second.2 context).state := by
  obtain ⟨validFirst, claimFirst⟩ := (GroundDerivation.check_iff _ _).mp hfirst
  obtain ⟨validSecond, claimSecond⟩ := (GroundDerivation.check_iff _ _).mp hsecond
  simp [joint_state, validFirst, validSecond, claimFirst, claimSecond, joinCall]

/-- Logical conjunction retains both complete input records and both claims.
This is the existing ground join rule, distinct from evidence-list sequencing. -/
def compose (first second : Evidence) : Evidence :=
  (.join first.1 second.1, .both first.2 second.2)

/-- Includes incorrect claims as well as invalid records; no validity premise. -/
theorem check_compose (first second : Evidence) :
    GroundDerivation.check (compose first second).1 (compose first second).2 =
      (GroundDerivation.check first.1 first.2 && GroundDerivation.check second.1 second.2) := by
  simp [compose, GroundDerivation.check, Record.valid, Record.conclusion,
    Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

theorem base_check (evidence : Evidence) :
    LayeredDerivation.check 0 evidence [evidence.2] =
      GroundDerivation.check evidence.1 evidence.2 := by
  simp only [LayeredDerivation.check, LayeredDerivation.unfold, RecordMachine.check_agrees]
  cases h : GroundDerivation.check evidence.1 evidence.2 <;> simp [h]

/-- Conjunction checking remains exactly both premise checks after any finite
number of lifts. Lifting cannot conceal either an invalid record or a bad claim. -/
theorem lifted_check (count : Nat) (first second : Evidence) :
    LayeredDerivation.check (0 + count) (iterateLift count 0 (compose first second))
        [(compose first second).2] =
      (GroundDerivation.check first.1 first.2 && GroundDerivation.check second.1 second.2) := by
  rw [LayeredDerivation.check_iterateLift, base_check, check_compose]

/-- Recover the submitted premise records and claims, without flattening them. -/
theorem lifted_recovery (count : Nat) (first second : Evidence) :
    recoverThrough count 0 (iterateLift count 0 (compose first second)) =
      some (compose first second) :=
  LayeredDerivation.recoverThrough_iterateLift _ _ _

/-- Replay data is reconstructed canonically from the recovered record, not
accepted as an externally supplied trajectory or an endpoint summary. -/
theorem lifted_history (count : Nat) (first second : Evidence) (context : List Formula) :
    (recoverThrough count 0 (iterateLift count 0 (compose first second))).map
        (fun evidence => trace (program evidence.1) (some context)) =
      some (trace (program first.1) (some context) ++
        trace (program second.1) (execute (program first.1) (some context)) ++
        trace [.join] (execute (program second.1) (execute (program first.1) (some context)))) := by
  rw [lifted_recovery]
  exact congrArg some (join_history first.1 second.1 (some context))

/-- The recovered canonical history passes transition and conclusion checking
exactly when both submitted premises pass, even for invalid input records. -/
theorem joined_trace_check (first second : Evidence) :
    RecordMachine.checkTrace (compose first second).1 (compose first second).2
        (trace (program (compose first second).1) (some [])) =
      (GroundDerivation.check first.1 first.2 && GroundDerivation.check second.1 second.2) := by
  rw [RecordMachine.checkTrace_trace, RecordMachine.check_agrees, check_compose]

end Hypermath.ContextualComposition
