import Hypermath.PathLayers
import Hypermath.PathTransport
import Hypermath.TransportCountermodel
import Hypermath.RetainedExecution
import Hypermath.ContextualComposition
import Hypermath.OperationalCorrespondence

namespace Hypermath.LayeredDerivationChecks

open GroundDerivation GroundCode LayeredDerivation

def first : Surface 0 :=
  let record := Record.primitive .groundSelf
  (record, record.conclusion)

def second : Surface 0 :=
  let record := Record.primitive (.diff .ground)
  (record, record.conclusion)

def invalid : Surface 0 :=
  (.projectLeft first.2 first.2 first.1, first.2)

def composed : Surface 1 := .seq (lift 0 first) (lift 0 second)

theorem composed_accepted : check 1 composed [first.2, second.2] = true := by decide

theorem arbitrary_lifts_accepted (count : Nat) :
    check (1 + count) (iterateLift count 1 composed) [first.2, second.2] = true := by
  rw [check_iterateLift]
  exact composed_accepted

theorem invalid_base_rejected : check 0 invalid [first.2] = false := by decide

theorem arbitrary_lifts_reject_invalid (count : Nat) :
    check (0 + count) (iterateLift count 0 invalid) [first.2] = false := by
  have agreement := check_iterateLift count 0 invalid [first.2]
  simpa using agreement.trans invalid_base_rejected

theorem invalid_composition_rejected :
    valid 1 (.seq (lift 0 first) (lift 0 invalid)) = false := by decide

theorem reversed_claims_rejected : check 1 composed [second.2, first.2] = false := by decide

theorem lost_repetition_rejected :
    check 1 (.seq (lift 0 first) (lift 0 first)) [first.2] = false := by decide

theorem malformed_atom_rejected (layer : Nat) :
    valid (layer + 1) (.atom .leaf) = false := by
  simp [valid, unfold, Expression.run, decode, RecordEncoding.unwrap]

theorem wrong_layer_atom_rejected : valid 2 (.atom (encode 0 first)) = false := by decide

theorem grouping_retained :
    encode 1 (.seq (.seq (lift 0 first) (lift 0 first)) (lift 0 second)) ≠
      encode 1 (.seq (lift 0 first) (.seq (lift 0 first) (lift 0 second))) := by decide

theorem layer_boundary_retained :
    lift 1 composed ≠ Expression.seq (lift 1 (lift 0 first)) (lift 1 (lift 0 second)) := by
  intro impossible
  cases impossible

theorem layer_boundary_preserves_expansion :
    SameExpansion 1 (lift 1 composed)
      (.seq (lift 1 (lift 0 first)) (lift 1 (lift 0 second))) :=
  lift_preserves_composition 0 (lift 0 first) (lift 0 second)

theorem isolated_trace_splice_rejected :
    RecordMachine.replay (RecordMachine.program first.1 ++ RecordMachine.program second.1)
      (some []) (RecordMachine.trace (RecordMachine.program first.1) (some []) ++
        RecordMachine.trace (RecordMachine.program second.1) (some [])) = false := by decide

theorem contextual_trace_accepted :
    RecordMachine.replay (RecordMachine.program first.1 ++ RecordMachine.program second.1)
      (some []) (RecordMachine.trace (RecordMachine.program first.1) (some []) ++
        RecordMachine.trace (RecordMachine.program second.1) (some [first.2])) = true := by decide

/-- A caller-asserted premise can make the local join step execute. That does
not establish a derivation of the asserted premise from the empty context. -/
def unsupportedClaim : Formula := .structural (.distinct .ground .ground)

theorem asserted_context_can_execute :
    RuleSubstitution.runCallNumber
        (ContextualComposition.joinCall first.2 unsupportedClaim []).code =
      some [.both first.2 unsupportedClaim] :=
  ContextualComposition.join_call_runs _ _ _

theorem unsupported_premise_rejected (count : Nat) :
    check (0 + count)
      (iterateLift count 0 (ContextualComposition.compose first (second.1, unsupportedClaim)))
      [.both first.2 unsupportedClaim] = false := by
  exact (ContextualComposition.lifted_check count first (second.1, unsupportedClaim)).trans
    (by decide)

theorem invalid_join_lifts_rejected (count : Nat) :
    check (0 + count) (iterateLift count 0 (ContextualComposition.compose first invalid))
      [.both first.2 invalid.2] = false := by
  exact (ContextualComposition.lifted_check count first invalid).trans (by decide)

theorem joined_claim_order_checked :
    check 0 (ContextualComposition.compose first second) [.both second.2 first.2] = false := by decide

open OperationalCorrespondence

/-- Both canonical encodings pass a one-step check, but a reached alias does
not have the same behavior. The example concerns correspondence, not arithmetic. -/
def aliasView : Representation Bool Nat where
  encode value := if value then 1 else 0
  decode
    | 0 => some false
    | 1 => some true
    | 2 => some true
    | 3 => some false
    | _ => none
  recover value := by cases value <;> rfl

def aliasStep : Nat → Nat
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | value => value

theorem canonical_step_check_passes (value : Bool) :
    aliasView.decode (aliasStep (aliasView.encode value)) = some true := by
  cases value <;> rfl

theorem canonical_check_does_not_iterate :
    aliasView.decode (run aliasStep 2 (aliasView.encode false)) ≠
      some (run (fun _ : Bool => true) 2 false) := by decide

theorem alias_step_not_closed :
    ¬ Respects aliasView (fun _ : Bool => true) aliasStep := by
  intro correct
  have impossible := correct 2 true rfl
  cases impossible

def boolView : Representation Bool Bool where
  encode := id
  decode := some
  recover _ := rfl

def canonicalLift (state : Nat) : Bool := state == 1

theorem canonical_lift_check_passes (value : Bool) :
    boolView.decode (canonicalLift (aliasView.encode value)) = some value := by
  cases value <;> rfl

theorem reached_alias_lift_loses_information :
    boolView.decode (canonicalLift (aliasStep (aliasView.encode false))) ≠
      aliasView.decode (aliasStep (aliasView.encode false)) := by decide

def directView : Representation Frame Frame where
  encode := id
  decode := some
  recover _ := rfl

theorem direct_step_corresponds : Respects directView Frame.advance Frame.advance := by
  intro state config decoded
  cases Option.some.inj decoded
  rfl

theorem tampered_endpoint_rejected :
    ({ run Frame.advance (RecordMachine.program first.1).length
        (Frame.initial first.1 first.2) with state := none }).accept = false := by decide

def main : IO Unit := do
  let claims := [first.2, second.2]
  for depth in [0, 1, 2, 4] do
    IO.println s!"START layer lift depth {depth}"
    unless check (1 + depth) (iterateLift depth 1 composed) claims do
      throw (IO.userError "valid composed surface was lost during lifting")
    unless decide (recoverThrough depth 1 (iterateLift depth 1 composed) = some composed) do
      throw (IO.userError "exact composition history was lost during lifting")
    if check (0 + depth) (iterateLift depth 0 invalid) [first.2] then
      throw (IO.userError "lifting restored an invalid derivation")
    IO.println s!"PASS layer lift depth {depth}: accepted, recovered, invalid record rejected"
  if check 1 composed [second.2, first.2] then
    throw (IO.userError "claim order was not checked")
  if check 1 (.seq (lift 0 first) (lift 0 first)) [first.2] then
    throw (IO.userError "claim multiplicity was not checked")
  if valid 2 (.atom (encode 0 first)) then
    throw (IO.userError "incorrect layer tag was accepted")
  IO.println "PASS layered checking: order, multiplicity and layer mismatch rejected"
  IO.println "START contextual composition: premise retention and trace boundaries"
  let joint := ContextualComposition.compose first second
  unless check 0 joint [joint.2] do
    throw (IO.userError "joined premise records were rejected")
  if RecordMachine.replay (RecordMachine.program first.1 ++ RecordMachine.program second.1)
      (some []) (RecordMachine.trace (RecordMachine.program first.1) (some []) ++
        RecordMachine.trace (RecordMachine.program second.1) (some [])) then
    throw (IO.userError "independently checked histories were spliced across incompatible contexts")
  for depth in [0, 1, 2, 4] do
    let unsupported := ContextualComposition.compose first (second.1, unsupportedClaim)
    unless check (0 + depth) (iterateLift depth 0 joint) [joint.2] do
      throw (IO.userError "joined inference was lost during lifting")
    if check (0 + depth) (iterateLift depth 0 unsupported) [unsupported.2] then
      throw (IO.userError "an unsupported premise claim became accepted")
    IO.println s!"PASS contextual composition depth {depth}: joint inference retained, unsupported premise rejected"
  IO.println "START operational correspondence: reachable aliases and retained checking state"
  for value in [false, true] do
    unless decide (aliasView.decode (aliasStep (aliasView.encode value)) = some true) do
      throw (IO.userError "canonical one-step premise did not hold")
  unless decide (aliasView.decode (run aliasStep 2 (aliasView.encode false)) = some false) do
    throw (IO.userError "noncanonical two-step counterexample did not reproduce")
  unless decide (boolView.decode (canonicalLift (aliasStep (aliasView.encode false))) !=
      aliasView.decode (aliasStep (aliasView.encode false))) do
    throw (IO.userError "canonical-only layer passage did not expose the reached-alias mismatch")
  for evidence in [first, second, invalid, (second.1, unsupportedClaim), joint] do
    let frame := run Frame.advance (RecordMachine.program evidence.1).length
      (Frame.initial evidence.1 evidence.2)
    unless frame.accept == GroundDerivation.check evidence.1 evidence.2 do
      throw (IO.userError "retained execution frame disagrees with the ground checker")
  IO.println "PASS operational correspondence: canonical-only law fails on repetition; complete frames retain check outcomes"

end Hypermath.LayeredDerivationChecks

#eval Hypermath.LayeredDerivationChecks.main

#print axioms Hypermath.LayeredDerivation.readExpression_tree
#print axioms Hypermath.LayeredDerivation.readPayload_payload
#print axioms Hypermath.LayeredDerivation.decode_encode
#print axioms Hypermath.LayeredDerivation.wrong_layer_rejected
#print axioms Hypermath.LayeredDerivation.encode_injective
#print axioms Hypermath.LayeredDerivation.combine_left_identity
#print axioms Hypermath.LayeredDerivation.combine_right_identity
#print axioms Hypermath.LayeredDerivation.combine_associative
#print axioms Hypermath.LayeredDerivation.Expression.run_sound
#print axioms Hypermath.LayeredDerivation.check_iff
#print axioms Hypermath.LayeredDerivation.lowerAtom_lift
#print axioms Hypermath.LayeredDerivation.unfold_lift
#print axioms Hypermath.LayeredDerivation.lift_injective
#print axioms Hypermath.LayeredDerivation.valid_lift
#print axioms Hypermath.LayeredDerivation.check_lift
#print axioms Hypermath.LayeredDerivation.unfold_seq
#print axioms Hypermath.LayeredDerivation.valid_seq
#print axioms Hypermath.LayeredDerivation.check_seq
#print axioms Hypermath.LayeredDerivation.lift_preserves_composition
#print axioms Hypermath.LayeredDerivation.recoverThrough_iterateLift
#print axioms Hypermath.LayeredDerivation.unfold_iterateLift
#print axioms Hypermath.LayeredDerivation.check_iterateLift
#print axioms Hypermath.LayeredDerivation.observe_iterateLift
#print axioms Hypermath.LayeredDerivation.composition_lift_preserves
#print axioms Hypermath.LayeredDerivation.unfold_sound
#print axioms Hypermath.LayeredDerivation.unfolded_claims_sound
#print axioms Hypermath.LayeredDerivation.check_sound
#print axioms Hypermath.LayeredDerivation.sequencing
#print axioms Hypermath.LayeredDerivation.liftMap
#print axioms Hypermath.LayeredDerivation.lift_reflects_expansion
#print axioms Hypermath.LayeredDerivation.readGroundTerm_groundTerm
#print axioms Hypermath.LayeredDerivation.observe_groundTerm
#print axioms Hypermath.LayeredDerivation.checkGroundTerm_groundTerm
#print axioms Hypermath.LayeredDerivationChecks.composed_accepted
#print axioms Hypermath.LayeredDerivationChecks.arbitrary_lifts_accepted
#print axioms Hypermath.LayeredDerivationChecks.invalid_base_rejected
#print axioms Hypermath.LayeredDerivationChecks.arbitrary_lifts_reject_invalid
#print axioms Hypermath.LayeredDerivationChecks.invalid_composition_rejected
#print axioms Hypermath.LayeredDerivationChecks.reversed_claims_rejected
#print axioms Hypermath.LayeredDerivationChecks.lost_repetition_rejected
#print axioms Hypermath.LayeredDerivationChecks.malformed_atom_rejected
#print axioms Hypermath.LayeredDerivationChecks.wrong_layer_atom_rejected
#print axioms Hypermath.LayeredDerivationChecks.grouping_retained
#print axioms Hypermath.LayeredDerivationChecks.layer_boundary_retained
#print axioms Hypermath.LayeredDerivationChecks.layer_boundary_preserves_expansion

#print axioms Hypermath.ContextualComposition.joint_state
#print axioms Hypermath.ContextualComposition.trace_append
#print axioms Hypermath.ContextualComposition.join_history
#print axioms Hypermath.ContextualComposition.join_call_runs
#print axioms Hypermath.ContextualComposition.checked_context
#print axioms Hypermath.ContextualComposition.check_compose
#print axioms Hypermath.ContextualComposition.base_check
#print axioms Hypermath.ContextualComposition.lifted_check
#print axioms Hypermath.ContextualComposition.lifted_recovery
#print axioms Hypermath.ContextualComposition.lifted_history
#print axioms Hypermath.ContextualComposition.joined_trace_check
#print axioms Hypermath.LayeredDerivationChecks.isolated_trace_splice_rejected
#print axioms Hypermath.LayeredDerivationChecks.contextual_trace_accepted
#print axioms Hypermath.LayeredDerivationChecks.asserted_context_can_execute
#print axioms Hypermath.LayeredDerivationChecks.unsupported_premise_rejected
#print axioms Hypermath.LayeredDerivationChecks.invalid_join_lifts_rejected
#print axioms Hypermath.LayeredDerivationChecks.joined_claim_order_checked

#print axioms Hypermath.OperationalCorrespondence.run_append
#print axioms Hypermath.OperationalCorrespondence.run_decodes
#print axioms Hypermath.OperationalCorrespondence.run_encoded
#print axioms Hypermath.OperationalCorrespondence.lift_compose
#print axioms Hypermath.OperationalCorrespondence.lift_run_decodes
#print axioms Hypermath.OperationalCorrespondence.run_lift_commutes
#print axioms Hypermath.OperationalCorrespondence.run_frame
#print axioms Hypermath.OperationalCorrespondence.accept_run_initial
#print axioms Hypermath.OperationalCorrespondence.represented_run
#print axioms Hypermath.OperationalCorrespondence.represented_check
#print axioms Hypermath.OperationalCorrespondence.represented_composition_check
#print axioms Hypermath.LayeredDerivationChecks.canonical_step_check_passes
#print axioms Hypermath.LayeredDerivationChecks.canonical_check_does_not_iterate
#print axioms Hypermath.LayeredDerivationChecks.alias_step_not_closed
#print axioms Hypermath.LayeredDerivationChecks.canonical_lift_check_passes
#print axioms Hypermath.LayeredDerivationChecks.reached_alias_lift_loses_information
#print axioms Hypermath.LayeredDerivationChecks.direct_step_corresponds
#print axioms Hypermath.LayeredDerivationChecks.tampered_endpoint_rejected

#eval Hypermath.RetainedExecution.Checks.probe

#print axioms Hypermath.RetainedExecution.readInstruction_instructionTree
#print axioms Hypermath.RetainedExecution.readFrame_frameTree
#print axioms Hypermath.RetainedExecution.frameTree_injective
#print axioms Hypermath.RetainedExecution.readPayload_payload
#print axioms Hypermath.RetainedExecution.decode_encode
#print axioms Hypermath.RetainedExecution.wrong_layer_rejected
#print axioms Hypermath.RetainedExecution.record_only_protocol_rejected
#print axioms Hypermath.RetainedExecution.accepted_combine
#print axioms Hypermath.RetainedExecution.lowerAtom_lift
#print axioms Hypermath.RetainedExecution.inspect_lift
#print axioms Hypermath.RetainedExecution.check_lift
#print axioms Hypermath.RetainedExecution.inspect_seq
#print axioms Hypermath.RetainedExecution.check_seq
#print axioms Hypermath.RetainedExecution.lift_preserves_composition
#print axioms Hypermath.RetainedExecution.recoverThrough_iterateLift
#print axioms Hypermath.RetainedExecution.inspect_iterateLift
#print axioms Hypermath.RetainedExecution.check_iterateLift
#print axioms Hypermath.RetainedExecution.composition_lift_preserves
#print axioms Hypermath.RetainedExecution.submitted_frame_recovered
#print axioms Hypermath.RetainedExecution.submitted_frame_check
#print axioms Hypermath.RetainedExecution.finished_frame_check
#print axioms Hypermath.RetainedExecution.accepted_frame_sound
#print axioms Hypermath.RetainedExecution.checked_surface_sound
#print axioms Hypermath.RetainedExecution.sequencing
#print axioms Hypermath.RetainedExecution.liftMap
#print axioms Hypermath.RetainedExecution.Checks.erased_record_still_valid
#print axioms Hypermath.RetainedExecution.Checks.erased_frame_rejected
#print axioms Hypermath.RetainedExecution.Checks.wrong_state_rejected
#print axioms Hypermath.RetainedExecution.Checks.incomplete_frame_rejected
#print axioms Hypermath.RetainedExecution.Checks.erased_history_retained
#print axioms Hypermath.RetainedExecution.Checks.erased_history_rejected
#print axioms Hypermath.RetainedExecution.Checks.composed_frames_retained
#print axioms Hypermath.RetainedExecution.Checks.composed_frames_accepted
#print axioms Hypermath.RetainedExecution.Checks.erased_composition_rejected
#print axioms Hypermath.RetainedExecution.Checks.repeated_frames_retained
#print axioms Hypermath.RetainedExecution.Checks.encoded_erasure_still_decodes

#eval Hypermath.PathLayers.Checks.probe

#print axioms Hypermath.PathLayers.expand_identity
#print axioms Hypermath.PathLayers.expand_compose
#print axioms Hypermath.PathLayers.lowerAtom_lift
#print axioms Hypermath.PathLayers.expand_lift
#print axioms Hypermath.PathLayers.recoverThrough_iterateLift
#print axioms Hypermath.PathLayers.expand_iterateLift
#print axioms Hypermath.PathLayers.composition_lift_preserves
#print axioms Hypermath.PathLayers.composed_edges_preserved
#print axioms Hypermath.PathLayers.composed_length_preserved
#print axioms Hypermath.PathLayers.expand_promote
#print axioms Hypermath.PathLayers.nonempty_iff_base
#print axioms Hypermath.PathLayers.no_steps_remains_empty
#print axioms Hypermath.PathLayers.native_reachability_iff
#print axioms Hypermath.PathLayers.native_endpoint_preserved
#print axioms Hypermath.PathLayers.native_composition_lift_preserves
#print axioms Hypermath.PathLayers.native_without_steps
#print axioms Hypermath.PathLayers.cycle_witness_length_preserved
#print axioms Hypermath.PathLayers.recoverCycle_reifyCycle
#print axioms Hypermath.PathLayers.cycle_surface_iff_witness
#print axioms Hypermath.PathLayers.loopSequencing
#print axioms Hypermath.PathLayers.loopLiftMap
#print axioms Hypermath.PathLayers.reifyCycle
#print axioms Hypermath.PathLayers.recoverCycle
#print axioms Hypermath.PathLayers.Checks.two_steps_retained
#print axioms Hypermath.PathLayers.Checks.nested_paths_recovered
#print axioms Hypermath.PathLayers.Checks.grouping_remains_distinct
#print axioms Hypermath.PathLayers.Checks.grouping_has_same_path

#eval Hypermath.PathTransport.Checks.probe

#print axioms Hypermath.PathTransport.Alignment.starts
#print axioms Hypermath.PathTransport.Alignment.ends
#print axioms Hypermath.PathTransport.Alignment.length_eq
#print axioms Hypermath.PathTransport.Alignment.compose
#print axioms Hypermath.PathTransport.reproduce_compose
#print axioms Hypermath.PathTransport.composed_length
#print axioms Hypermath.PathTransport.composed_endpoint_related
#print axioms Hypermath.PathTransport.composed_edges
#print axioms Hypermath.PathTransport.raise_retains_certificate
#print axioms Hypermath.PathTransport.raise_recovers_surface
#print axioms Hypermath.PathTransport.raise_preserves_path
#print axioms Hypermath.PathTransport.native_law_iff_transfer
#print axioms Hypermath.PathTransport.Reproduction.append
#print axioms Hypermath.PathTransport.reproduce
#print axioms Hypermath.PathTransport.composeAcross
#print axioms Hypermath.PathTransport.atLayer
#print axioms Hypermath.PathTransport.raise
#print axioms Hypermath.PathTransport.nativeTransfer
#print axioms Hypermath.PathTransport.Checks.reproduced_copy_changes_endpoint
#print axioms Hypermath.PathTransport.Checks.original_and_copy_retained
#print axioms Hypermath.PathTransport.Checks.path_preserves_component
#print axioms Hypermath.PathTransport.Checks.related_without_connector
#print axioms Hypermath.PathTransport.Checks.relation_alone_insufficient

#eval HypermathTransportCountermodel.probe

#print axioms HypermathTransportCountermodel.simulation_is_equivalence
#print axioms HypermathTransportCountermodel.forming_preserves_not_limit
#print axioms HypermathTransportCountermodel.finite_position_not_limit
#print axioms HypermathTransportCountermodel.simulation_limit_iff
#print axioms HypermathTransportCountermodel.full_axioms_hold
#print axioms HypermathTransportCountermodel.self_derivation_holds
#print axioms HypermathTransportCountermodel.cycle_has_two_steps
#print axioms HypermathTransportCountermodel.related_starts_are_ground_generated
#print axioms HypermathTransportCountermodel.step_stays_in_cycle
#print axioms HypermathTransportCountermodel.path_stays_in_cycle
#print axioms HypermathTransportCountermodel.no_finite_reproduction
#print axioms HypermathTransportCountermodel.native_one_step_law_fails
#print axioms HypermathTransportCountermodel.no_step_transfer
#print axioms HypermathTransportCountermodel.full_model_with_cycle_without_reproduction
#print axioms HypermathTransportCountermodel.cycleWitness
