"""Parse the expected Lean reports; missing or duplicate records are invalid."""

from __future__ import annotations

import hashlib
import json
import re

from ._baseline import (
    ACTION_COUNTERMODEL_SOURCE_SHA256,
    AUDIT_SOURCE_SHA256,
    AXIOM_DECLARATIONS,
    CONTEXTUAL_COMPOSITION_SOURCE_SHA256,
    COUNTERMODEL_SOURCE_SHA256,
    DEFINITION_DECLARATIONS,
    FINITE_ACTION_SOURCE_SHA256,
    FULL_MODEL_SOURCE_SHA256,
    GROUND_CODE_SOURCE_SHA256,
    GROUND_DERIVATION_CHECKS_SOURCE_SHA256,
    GROUND_DERIVATION_SOURCE_SHA256,
    GROUND_SYNTAX_CHECKS_SOURCE_SHA256,
    GROUND_SYNTAX_SOURCE_SHA256,
    LAYERED_DERIVATION_CHECKS_SOURCE_SHA256,
    LAYERED_DERIVATION_SOURCE_SHA256,
    LEAN_BUILTINS,
    OBSERVATION_CHECKS_SOURCE_SHA256,
    OBSERVATION_SOURCE_SHA256,
    OPERATIONAL_CORRESPONDENCE_SOURCE_SHA256,
    PATH_LAYERS_SOURCE_SHA256,
    PATH_TRANSPORT_SOURCE_SHA256,
    PROVED_DECLARATIONS,
    PROVED_DEPENDENCIES,
    RECORD_ENCODING_CHECKS_SOURCE_SHA256,
    RECORD_ENCODING_SOURCE_SHA256,
    RECORD_MACHINE_CHECKS_SOURCE_SHA256,
    RECORD_MACHINE_SOURCE_SHA256,
    RETAINED_EXECUTION_SOURCE_SHA256,
    RULE_SUBSTITUTION_SOURCE_SHA256,
    SEQUENTIAL_SOURCE_SHA256,
    SURFACE_BRIDGE_SOURCE_SHA256,
    TARGET_CLAIM,
    TARGET_STATEMENT,
    TERMINAL_RETENTION_SOURCE_SHA256,
    TRACE_CHECKS_SOURCE_SHA256,
    TRACE_SOURCE_SHA256,
    TRANSPORT_COUNTERMODEL_SOURCE_SHA256,
    UNARY_FORMATION_SOURCE_SHA256,
)

FORMAT = "hypermath-audit-1"
REPOSITORY = "https://github.com/TimeLordRaps/hypermath"
TARGET = "Hypermath.selfDerivation"
DEPENDENCY_TARGETS = (
    "Hypermath.applyGroundIsDistinct", "Hypermath.groundIsFormClosed",
    "Hypermath.orbitStructure", "Hypermath.similarReflexive",
    "Hypermath.derivesIsDirectional", "Hypermath.dIsReflexive",
    "Hypermath.plusAndAdditionallyAreDistinct", "Hypermath.pathGroundIsIdentity",
    "Hypermath.simulationPairExistsClaim",
    "Hypermath.driverCycleClaim", TARGET,
    *[name for name in PROVED_DECLARATIONS if name != "Hypermath.dIsReflexive"],
)
COUNTERMODEL_TARGETS = tuple("HypermathCountermodel." + name for name in (
    "prefixAxioms_hold", "reverse_filtration_fails", "directionality_claim_fails",
    "driver_cycle_claim_fails", "preserving_prefix_axioms_hold",
    "d_spans_ground_claim_fails", "driver_endpoint_cycle_without_positive_trace",
))
TRACE_CHECK_TARGETS = ('Hypermath.Trace.nil_compose',
 'Hypermath.Trace.compose_nil',
 'Hypermath.Trace.compose_assoc',
 'Hypermath.Trace.length_nil',
 'Hypermath.Trace.length_cons',
 'Hypermath.Trace.length_compose',
 'Hypermath.Trace.edges_compose',
 'Hypermath.Trace.edges_length',
 'Hypermath.Trace.map_nil',
 'Hypermath.Trace.map_compose',
 'Hypermath.Trace.length_map',
 'Hypermath.Trace.edges_map',
 'Hypermath.TraceExpr.expand_atom',
 'Hypermath.TraceExpr.expand_self',
 'Hypermath.TraceExpr.expand_seq',
 'Hypermath.TraceExpr.length_expand',
 'Hypermath.TraceExpr.edges_expand_seq',
 'Hypermath.TraceChecks.twoSteps_length',
 'Hypermath.TraceChecks.twoSteps_edges',
 'Hypermath.TraceChecks.composed_length',
 'Hypermath.TraceChecks.composed_edges',
 'Hypermath.TraceChecks.mapped_length',
 'Hypermath.TraceChecks.mapped_edges',
 'Hypermath.TraceChecks.reused_length',
 'Hypermath.TraceChecks.reused_edges',
 'Hypermath.TraceChecks.absent_edge_rejected',
 'Hypermath.TraceChecks.successor_trace_monotone',
 'Hypermath.TraceChecks.missing_return_rejected')
OBSERVATION_TARGETS = ('Hypermath.Observation.endpoints_eq_of_step',
 'Hypermath.Observation.endpoint_decoder_cannot_recover_distinct_lengths',
 'Hypermath.Observation.no_endpoint_length_decoder',
 'Hypermath.ObservationChecks.observation_preserved',
 'Hypermath.ObservationChecks.empty_length',
 'Hypermath.ObservationChecks.closed_length',
 'Hypermath.ObservationChecks.closed_positive',
 'Hypermath.ObservationChecks.distinct_lengths',
 'Hypermath.ObservationChecks.pair_decoder_rejected',
 'Hypermath.ObservationChecks.universal_decoder_rejected',
 'Hypermath.ObservationChecks.whole_trace_retains_lengths',
 'Hypermath.ObservationChecks.reused_length',
 'Hypermath.ObservationChecks.reused_preserves_length',
 'Hypermath.Observation.decoder_implies_compatible',
 'Hypermath.Observation.chosenDecoder_correct',
 'Hypermath.Observation.compatible_iff_decoder',
 'Hypermath.Observation.decoder_unique_on_image',
 'Hypermath.Observation.reuse_respects_encoding',
 'Hypermath.Observation.reuse_preserves_observations',
 'Hypermath.Observation.equality_queries_iff_injective',
 'Hypermath.ObservationChecks.first_bit_exact',
 'Hypermath.ObservationChecks.flip_respects_encoding',
 'Hypermath.ObservationChecks.first_bit_reuse_exact',
 'Hypermath.ObservationChecks.swap_exposes_lost_bit')
OBSERVATION_DEPENDENCIES = {
    name: (["Classical.choice"] if name in {
        "Hypermath.Observation.chosenDecoder_correct",
        "Hypermath.Observation.compatible_iff_decoder",
    } else [])
    for name in OBSERVATION_TARGETS
}
CLAIMS = ("self_derivation", "source_adequacy", "recursive_arithmetic_completeness")
GROUND_SYNTAX_DEPENDENCIES = {
    **{"Hypermath.GroundSyntax." + name: [] for name in (
        "Term.depth_ofDepth", "Term.ofDepth_depth", "Term.interpret_ofDepth", "instance_sound",
    )},
    **{"Hypermath.GroundSyntax." + name: ["propext"] for name in (
        "decode_encode", "encode_injective", "observe_encode", "check_encode",
        "reuse_encode", "reuse_many_encode",
    )},
    **{"Hypermath.GroundSyntax." + name: ["Quot.sound", "propext"] for name in (
        "check_iff", "check_sound",
    )},
    "Hypermath.GroundSyntax.native_check_sound": sorted([
        "Hypermath.Form", "Hypermath.ground", "Hypermath.f2f",
        "Hypermath.structDistinct", "Hypermath.structContinues", "Hypermath.structOrbits",
        "Hypermath.axDiff", "Hypermath.axSim", "Hypermath.axBox", "Hypermath.axGroundSelf",
        "propext", "Quot.sound",
    ]),
    **{"Hypermath.GroundSyntaxChecks." + name: [] for name in (
        "concrete_record_roundtrip", "concrete_conclusion_checked", "wrong_claim_rejected",
        "wrong_argument_rejected", "wrong_rule_rejected", "malformed_record_rejected",
        "longer_malformed_record_rejected", "reused_record_checked", "malformed_reuse_rejected",
    )},
    "Hypermath.GroundSyntaxChecks.distinct_records_retained": ["propext"],
}
GROUND_SYNTAX_TARGETS = tuple(GROUND_SYNTAX_DEPENDENCIES)
GROUND_DERIVATION_DEPENDENCIES = {
    **{"Hypermath.GroundDerivation." + name: [] for name in (
        "derivation_sound", "separation",
    )},
    **{"Hypermath.GroundDerivation." + name: ["propext"] for name in (
        "check_iff", "Record.derive", "check_sound", "conclusion_quote", "valid_quote",
        "check_quote", "quote_derive", "observe_derive", "reconstruct",
        "reconstruct_retains_record", "represented_iff_derivable", "check_join_iff",
    )},
    "Hypermath.GroundDerivation.native_check_sound": sorted([
        "Hypermath.Form", "Hypermath.ground", "Hypermath.f2f",
        "Hypermath.structDistinct", "Hypermath.structContinues", "Hypermath.structOrbits",
        "Hypermath.Similar", "Hypermath.Simulation",
        "Hypermath.axDiff", "Hypermath.axSim", "Hypermath.axBox", "Hypermath.axGroundSelf",
        "Hypermath.closeStructContinues", "Hypermath.closeStructDistinct",
        "Hypermath.closeStructOrbits", "propext",
    ]),
    **{"Hypermath.GroundDerivationChecks." + name: ["propext"] for name in (
        "separation_checked", "invalid_record_not_reconstructed",
    )},
    **{"Hypermath.GroundDerivationChecks." + name: [] for name in (
        "composed_example_checked", "wrong_claim_rejected", "wrong_predicate_premise_rejected",
        "wrong_argument_rejected", "nonconjunction_projection_rejected",
        "projection_cannot_hide_failed_premise", "wrong_projection_annotation_rejected",
        "repeated_record_can_be_joined", "good_projection_checked",
    )},
}
GROUND_DERIVATION_TARGETS = tuple(GROUND_DERIVATION_DEPENDENCIES)
RECORD_ENCODING_DEPENDENCIES = {
    **{"Hypermath.GroundCode." + name: ["Quot.sound", "propext"] for name in (
        "unpack_pack", "parse_bits", "decode_code", "decode_toTerm",
        "code_injective", "toTerm_injective",
    )},
    "Hypermath.GroundCode.pack_bounds": ["Classical.choice", "Quot.sound", "propext"],
    "Hypermath.GroundCode.Tree.bits_length": ["propext"],
    **{"Hypermath.RecordEncoding." + name: ["propext"] for name in (
        "readTerm_termTree", "readTag_number",
    )},
    **{"Hypermath.RecordEncoding." + name: ["Quot.sound", "propext"] for name in (
        "readStatement_statementTree", "readFormula_formulaTree", "readRecord_recordTree",
        "decode_recordCode", "decode_formulaCode", "decodeFormula_recordCode",
        "decodeRecord_formulaCode", "recordCode_injective", "observe_recordCode",
        "decode_recordTerm", "decode_formulaTerm", "checkNumbers_codes", "checkTerms_terms",
        "checkNumbers_sound", "checkTerms_quote", "recordTerm_injective", "observe_recordTerm",
        "joinCodes_recordCode", "semantic_record_recovery",
    )},
    **{"Hypermath.RecordEncodingChecks." + name: ["Quot.sound", "propext"] for name in (
        "packed_separation_checked", "wrong_claim_rejected",
        "encoded_projection_cannot_hide_failure", "repeated_record_checked",
        "empty_code_rejected", "incomplete_tree_rejected", "trailing_bits_rejected",
        "invalid_inputs_rejected", "invalid_join_rejected",
    )},
    **{"Hypermath.RecordEncodingChecks." + name: [] for name in (
        "no_parse_fuel", "unknown_formula_tag_rejected", "unknown_record_tag_rejected",
        "wrong_formula_arity_rejected", "wrong_record_arity_rejected",
        "malformed_primitive_rejected", "malformed_tag_rejected",
    )},
}
RECORD_ENCODING_TARGETS = tuple(RECORD_ENCODING_DEPENDENCIES)
RECORD_MACHINE_DEPENDENCIES = {
    **{"Hypermath.RecordMachine." + name: [] for name in (
        "step_failed", "execute_failed", "execute_append", "endpoint_trace",
    )},
    **{"Hypermath.RecordMachine." + name: ["propext"] for name in (
        "execute_program", "check_agrees", "check_sound", "check_quote",
        "replay_iff", "replay_trace", "replay_unique", "checkTrace_trace",
        "checkTrace_iff", "checkTrace_sound", "checkTrace_quote", "program_length",
        "trace_length", "compiled_trace_length",
    )},
    **{"Hypermath.RecordMachine." + name: ["Quot.sound", "propext"] for name in (
        "checkNumbers_agrees", "checkNumbers_codes", "checkNumbers_sound",
    )},
    **{"Hypermath.RecordMachineChecks." + name: [] for name in (
        "example_accepted", "invalid_projection_rejected", "same_conclusion_different_execution",
        "projection_cannot_hide_failed_premise", "stack_underflow_rejected",
        "wrong_predicate_rejected", "wrong_argument_rejected",
        "later_primitive_cannot_restore_failure", "correct_trace_accepted",
        "omitted_step_rejected", "extra_step_rejected", "forged_state_rejected",
        "wrong_trace_claim_rejected", "trace_for_other_record_rejected",
        "accurate_failure_trace_not_acceptance", "five_instructions_for_separation",
    )},
    **{"Hypermath.RecordMachineChecks." + name: ["Quot.sound", "propext"] for name in (
        "packed_example_accepted", "packed_wrong_sort_rejected", "empty_packed_input_rejected",
    )},
}
RECORD_MACHINE_DEPENDENCIES.update({'Hypermath.RuleSubstitution.step_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.execute_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.execute_program': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.check_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.check_sound': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.check_quote': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.readList_listTree': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.readRule_index': [],
 'Hypermath.RuleSubstitution.readApplication_tree': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.decode_code': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.decode_toTerm': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.toTerm_injective': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.runNumber_code': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.runTerm_toTerm': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.formula_code_rejected': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.record_code_rejected': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.no_rule_only_instantiation': [],
 'Hypermath.RuleSubstitution.readState_stateTree': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.readCall_tree': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.decodeCall_code': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.decodeCall_toTerm': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.call_toTerm_injective': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.runCallNumber_code': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.runCallTerm_toTerm': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedStep_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedExecute_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedExecute_program': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedCheck_agrees': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedCheck_sound': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitution.encodedCheck_quote': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitutionChecks.missing_substitution_rejected': [],
 'Hypermath.RuleSubstitutionChecks.surplus_substitution_rejected': [],
 'Hypermath.RuleSubstitutionChecks.wrong_substitution_sort_rejected': [],
 'Hypermath.RuleSubstitutionChecks.unused_formula_argument_rejected': [],
 'Hypermath.RuleSubstitutionChecks.unbound_term_variable_rejected': [],
 'Hypermath.RuleSubstitutionChecks.unbound_formula_variable_rejected': [],
 'Hypermath.RuleSubstitutionChecks.substituted_rule_checks_premise': [],
 'Hypermath.RuleSubstitutionChecks.join_premise_order_matters': [],
 'Hypermath.RuleSubstitutionChecks.untouched_stack_is_retained': [],
 'Hypermath.RuleSubstitutionChecks.poisoned_input_remains_failed': [],
 'Hypermath.RuleSubstitutionChecks.unknown_rule_rejected': [],
 'Hypermath.RuleSubstitutionChecks.malformed_state_rejected': [],
 'Hypermath.RuleSubstitutionChecks.failed_and_empty_state_distinct': [],
 'Hypermath.RuleSubstitutionChecks.encoded_call_checks_retained_premise': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitutionChecks.distinct_premises_have_distinct_call_terms': ['Quot.sound',
                                                                                 'propext'],
 'Hypermath.RuleSubstitutionChecks.encoded_hidden_failure_rejected': ['Quot.sound', 'propext'],
 'Hypermath.RuleSubstitutionChecks.encoded_example_accepted': ['Quot.sound', 'propext']})
RECORD_MACHINE_TARGETS = tuple(RECORD_MACHINE_DEPENDENCIES)
FULL_MODEL_DEPENDENCIES = {
    "Hypermath.TerminalRetention.run_fixed": [],
    "Hypermath.TerminalRetention.merged_fixed_states": [],
    "Hypermath.TerminalRetention.finished_record": ["propext"],
    "Hypermath.TerminalRetention.finished_fixed": ["propext"],
    "Hypermath.TerminalRetention.finished_check": ["propext"],
    "HypermathFullAxiomModel.primitive_run_value": ["propext"],
    "HypermathFullAxiomModel.same_chain_orbits_meet": ["propext"],
    "HypermathFullAxiomModel.same_chain_terminal_records_equal": ["propext"],
    "HypermathFullAxiomModel.no_primitive_frame_checker": ["propext"],
    "HypermathFullAxiomModel.full_clauses_without_primitive_frame_checker": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.terminal_witnesses_accepted": [],
    **{"Hypermath.UnaryFormation." + name: [] for name in (
        "eval_ignores_an_input", "identity_collapses_relation", "no_term_identity",
        "pair_recovery_collapses", "no_term_pair_encoder", "natural_add_not_a_term",
        "singleton_term_identity", "universal_relation_term_identity",
    )},
    "HypermathFullAxiomModel.no_fixed_term_identity": [],
    "HypermathFullAxiomModel.no_fixed_term_pair_encoder": [],
    "HypermathFullAxiomModel.full_clauses_without_fixed_term_composition": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    **{"Hypermath.Sequential." + name: [] for name in (
        "unit_commutes", "uniform_separation_double_negates_unit", "no_uniform_separation",
        "no_source_operation", "program_composition_executes", "program_noncommutative",
        "program_order_changes_result",
        "naturalSequencing", "natural_commutative",
    )},
    **{"Hypermath.Sequential." + name: ["propext"] for name in (
        "program_identity", "program_associative", "distinct_nonempty_programs_commute",
        "program_uniform_separation_fails",
        "programSequencing", "program_not_commutative", "natural_no_inverses",
        "programLength", "program_length_preserves_composition",
        "program_length_forgets_order", "program_length_not_faithful",
    )},
    "HypermathFullAxiomModel.no_coherent_source_sequence": [],
    "HypermathFullAxiomModel.full_clauses_without_coherent_source_sequence": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    **{"HypermathFullAxiomModel." + name: [] for name in (
        "same_conclusion_opposite_acceptance", "no_conclusion_only_record_checker",
        "driver_cycle_claim_fails", "nontrivial_simulation_claim_fails",
        "self_derivation_target_fails",
    )},
    **{"HypermathFullAxiomModel." + name: ["propext"] for name in (
        "finite_numerals_injective", "recordValue_is_interpretation",
        "formulaValue_is_interpretation", "record_native_ready",
    )},
    **{"HypermathFullAxiomModel." + name: ["Classical.choice", "Quot.sound", "propext"]
       for name in (
           "full_axioms_hold", "boundary_probe", "full_clauses_with_faithful_records",
           "no_preserving_record_to_formula", "full_clauses_with_rejected_closed_record",
           "full_clauses_without_cycle_or_nontrivial_simulation",
       )},
    **{"HypermathFullAxiomModel." + name: ["Quot.sound", "propext"] for name in (
        "readRecordValue_recordValue", "readFormulaValue_formulaValue",
        "interpreted_record_recovered", "interpreted_observation_preserved",
        "recordValue_injective", "checkValues_values", "checkValues_sound",
        "other_chain_not_a_record", "other_chain_not_a_formula", "record_formula_values_disjoint",
        "interpreted_separation_checked", "interpreted_wrong_claim_rejected", "other_chain_rejected",
        "rejected_record_has_native_closure", "native_closure_is_not_record_acceptance",
    )},
}
FULL_MODEL_TARGETS = tuple(FULL_MODEL_DEPENDENCIES)
ACTION_COUNTERMODEL_TARGETS = tuple("HypermathFiniteActionCountermodel." + name for name in (
    "full_axioms_hold", "numeral_collision", "action_disagreement",
    "finite_action_incompatible", "no_exact_finite_action", "congruence_is_equivalence",
    "relation_action_incompatible", "no_congruent_finite_action",
    "ordinal_zero_identity_claim_fails", "ordinal_successor_action_claim_fails",
    "path_length_arithmetic_claim_fails", "self_derivation_target_holds",
    "self_derivation_without_arithmetic_bridge",
    "numeral_equality_observation_fails", "no_numeral_equality_decoder",
    "primitive_records_collide", "primitive_conclusions_differ",
    "no_semantic_primitive_record_decoder",
    "no_preserving_step", "every_D_entry_is_empty", "no_nonzero_D_entry",
    "full_clauses_and_target_without_nonzero_D",
))
ACTION_COUNTERMODEL_DEPENDENCIES = {
    name: (
        ["Quot.sound", "propext"]
        if name.endswith((".full_axioms_hold", ".self_derivation_without_arithmetic_bridge",
                          ".full_clauses_and_target_without_nonzero_D"))
        else ["propext"] if name.endswith((".self_derivation_target_holds", ".no_preserving_step",
                                           ".every_D_entry_is_empty", ".no_nonzero_D_entry")) else []
    )
    for name in ACTION_COUNTERMODEL_TARGETS
}
# Reviewed exact dependencies of the finite layer-preservation construction.
LAYERED_DERIVATION_DEPENDENCIES = {'Hypermath.LayeredDerivation.Expression.run_sound': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.checkGroundTerm_groundTerm': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.check_iff': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.check_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.check_lift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.check_seq': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.check_sound': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.combine_associative': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.combine_left_identity': [],
 'Hypermath.LayeredDerivation.combine_right_identity': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.composition_lift_preserves': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.decode_encode': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.encode_injective': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.liftMap': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.lift_injective': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.lift_preserves_composition': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.lift_reflects_expansion': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.lowerAtom_lift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.observe_groundTerm': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.observe_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.readExpression_tree': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.readGroundTerm_groundTerm': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.readPayload_payload': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.recoverThrough_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.sequencing': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.unfold_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.unfold_lift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.unfold_seq': [],
 'Hypermath.LayeredDerivation.unfold_sound': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.unfolded_claims_sound': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.valid_lift': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivation.valid_seq': [],
 'Hypermath.LayeredDerivation.wrong_layer_rejected': ['propext'],
 'Hypermath.LayeredDerivationChecks.arbitrary_lifts_accepted': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivationChecks.arbitrary_lifts_reject_invalid': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivationChecks.composed_accepted': [],
 'Hypermath.LayeredDerivationChecks.grouping_retained': [],
 'Hypermath.LayeredDerivationChecks.invalid_base_rejected': [],
 'Hypermath.LayeredDerivationChecks.invalid_composition_rejected': [],
 'Hypermath.LayeredDerivationChecks.layer_boundary_preserves_expansion': ['Quot.sound', 'propext'],
 'Hypermath.LayeredDerivationChecks.layer_boundary_retained': [],
 'Hypermath.LayeredDerivationChecks.lost_repetition_rejected': [],
 'Hypermath.LayeredDerivationChecks.malformed_atom_rejected': ['propext'],
 'Hypermath.LayeredDerivationChecks.reversed_claims_rejected': [],
 'Hypermath.LayeredDerivationChecks.wrong_layer_atom_rejected': []}
# Reviewed context construction and adversarial premise/trace checks. These
# dependencies permit no native assumptions, choice axiom, or admissions.
LAYERED_DERIVATION_DEPENDENCIES.update({
    'Hypermath.ContextualComposition.joint_state': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.trace_append': ['propext'],
    'Hypermath.ContextualComposition.join_history': ['propext'],
    'Hypermath.ContextualComposition.join_call_runs': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.checked_context': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.check_compose': ['propext'],
    'Hypermath.ContextualComposition.base_check': ['propext'],
    'Hypermath.ContextualComposition.lifted_check': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.lifted_recovery': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.lifted_history': ['Quot.sound', 'propext'],
    'Hypermath.ContextualComposition.joined_trace_check': ['propext'],
    'Hypermath.LayeredDerivationChecks.isolated_trace_splice_rejected': [],
    'Hypermath.LayeredDerivationChecks.contextual_trace_accepted': [],
    'Hypermath.LayeredDerivationChecks.asserted_context_can_execute': ['Quot.sound', 'propext'],
    'Hypermath.LayeredDerivationChecks.unsupported_premise_rejected': ['Quot.sound', 'propext'],
    'Hypermath.LayeredDerivationChecks.invalid_join_lifts_rejected': ['Quot.sound', 'propext'],
    'Hypermath.LayeredDerivationChecks.joined_claim_order_checked': [],
})
LAYERED_DERIVATION_DEPENDENCIES.update({
    'Hypermath.OperationalCorrespondence.run_append': ['propext'],
    'Hypermath.OperationalCorrespondence.run_decodes': [],
    'Hypermath.OperationalCorrespondence.run_encoded': [],
    'Hypermath.OperationalCorrespondence.lift_compose': [],
    'Hypermath.OperationalCorrespondence.lift_run_decodes': [],
    'Hypermath.OperationalCorrespondence.run_lift_commutes': [],
    'Hypermath.OperationalCorrespondence.run_frame': ['propext'],
    'Hypermath.OperationalCorrespondence.accept_run_initial': ['propext'],
    'Hypermath.OperationalCorrespondence.represented_run': ['propext'],
    'Hypermath.OperationalCorrespondence.represented_check': ['propext'],
    'Hypermath.OperationalCorrespondence.represented_composition_check': ['propext'],
    'Hypermath.LayeredDerivationChecks.canonical_step_check_passes': [],
    'Hypermath.LayeredDerivationChecks.canonical_check_does_not_iterate': [],
    'Hypermath.LayeredDerivationChecks.alias_step_not_closed': [],
    'Hypermath.LayeredDerivationChecks.canonical_lift_check_passes': [],
    'Hypermath.LayeredDerivationChecks.reached_alias_lift_loses_information': [],
    'Hypermath.LayeredDerivationChecks.direct_step_corresponds': [],
    'Hypermath.LayeredDerivationChecks.tampered_endpoint_rejected': [],
})
LAYERED_DERIVATION_DEPENDENCIES.update({'Hypermath.RetainedExecution.readInstruction_instructionTree': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.readFrame_frameTree': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.frameTree_injective': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.readPayload_payload': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.decode_encode': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.wrong_layer_rejected': ['propext'],
 'Hypermath.RetainedExecution.record_only_protocol_rejected': ['propext'],
 'Hypermath.RetainedExecution.accepted_combine': ['propext'],
 'Hypermath.RetainedExecution.lowerAtom_lift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.inspect_lift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.check_lift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.inspect_seq': [],
 'Hypermath.RetainedExecution.check_seq': ['propext'],
 'Hypermath.RetainedExecution.lift_preserves_composition': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.recoverThrough_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.inspect_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.check_iterateLift': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.composition_lift_preserves': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.submitted_frame_recovered': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.submitted_frame_check': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.finished_frame_check': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.accepted_frame_sound': ['propext'],
 'Hypermath.RetainedExecution.checked_surface_sound': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.sequencing': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.liftMap': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.erased_record_still_valid': [],
 'Hypermath.RetainedExecution.Checks.erased_frame_rejected': [],
 'Hypermath.RetainedExecution.Checks.wrong_state_rejected': [],
 'Hypermath.RetainedExecution.Checks.incomplete_frame_rejected': [],
 'Hypermath.RetainedExecution.Checks.erased_history_retained': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.erased_history_rejected': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.composed_frames_retained': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.composed_frames_accepted': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.erased_composition_rejected': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.repeated_frames_retained': ['Quot.sound', 'propext'],
 'Hypermath.RetainedExecution.Checks.encoded_erasure_still_decodes': ['Quot.sound', 'propext']})
LAYERED_DERIVATION_DEPENDENCIES.update({'Hypermath.PathLayers.expand_identity': [],
 'Hypermath.PathLayers.expand_compose': [],
 'Hypermath.PathLayers.lowerAtom_lift': [],
 'Hypermath.PathLayers.expand_lift': [],
 'Hypermath.PathLayers.recoverThrough_iterateLift': ['propext'],
 'Hypermath.PathLayers.expand_iterateLift': [],
 'Hypermath.PathLayers.composition_lift_preserves': ['propext'],
 'Hypermath.PathLayers.composed_edges_preserved': ['propext'],
 'Hypermath.PathLayers.composed_length_preserved': ['propext'],
 'Hypermath.PathLayers.expand_promote': [],
 'Hypermath.PathLayers.nonempty_iff_base': [],
 'Hypermath.PathLayers.no_steps_remains_empty': [],
 'Hypermath.PathLayers.native_reachability_iff': ['Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'],
 'Hypermath.PathLayers.native_endpoint_preserved': ['Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'],
 'Hypermath.PathLayers.native_composition_lift_preserves': ['Hypermath.Congruent',
                                                            'Hypermath.Form',
                                                            'Hypermath.f2f',
                                                            'propext'],
 'Hypermath.PathLayers.native_without_steps': ['Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'],
 'Hypermath.PathLayers.cycle_witness_length_preserved': ['Hypermath.Congruent',
                                                         'Hypermath.Form',
                                                         'Hypermath.Simulation',
                                                         'Hypermath.deriver',
                                                         'Hypermath.f2f',
                                                         'Hypermath.filtrationSimCong'],
 'Hypermath.PathLayers.recoverCycle_reifyCycle': ['Hypermath.Form',
                                                  'Hypermath.Simulation',
                                                  'Hypermath.deriver',
                                                  'Hypermath.f2f',
                                                  'propext'],
 'Hypermath.PathLayers.cycle_surface_iff_witness': ['Hypermath.Form',
                                                    'Hypermath.Simulation',
                                                    'Hypermath.deriver',
                                                    'Hypermath.f2f'],
 'Hypermath.PathLayers.loopSequencing': ['propext'],
 'Hypermath.PathLayers.loopLiftMap': ['propext'],
 'Hypermath.PathLayers.reifyCycle': ['Hypermath.Form',
                                     'Hypermath.Simulation',
                                     'Hypermath.deriver',
                                     'Hypermath.f2f'],
 'Hypermath.PathLayers.recoverCycle': ['Hypermath.Form',
                                       'Hypermath.Simulation',
                                       'Hypermath.deriver',
                                       'Hypermath.f2f'],
 'Hypermath.PathLayers.Checks.two_steps_retained': ['propext'],
 'Hypermath.PathLayers.Checks.nested_paths_recovered': ['propext'],
 'Hypermath.PathLayers.Checks.grouping_remains_distinct': [],
 'Hypermath.PathLayers.Checks.grouping_has_same_path': []})
LAYERED_DERIVATION_DEPENDENCIES.update({'Hypermath.PathTransport.Alignment.starts': [],
 'Hypermath.PathTransport.Alignment.ends': [],
 'Hypermath.PathTransport.Alignment.length_eq': [],
 'Hypermath.PathTransport.Alignment.compose': [],
 'Hypermath.PathTransport.reproduce_compose': [],
 'Hypermath.PathTransport.composed_length': [],
 'Hypermath.PathTransport.composed_endpoint_related': [],
 'Hypermath.PathTransport.composed_edges': [],
 'Hypermath.PathTransport.raise_retains_certificate': [],
 'Hypermath.PathTransport.raise_recovers_surface': ['propext'],
 'Hypermath.PathTransport.raise_preserves_path': [],
 'Hypermath.PathTransport.native_law_iff_transfer': ['Hypermath.Congruent',
                                                     'Hypermath.Form',
                                                     'Hypermath.Simulation',
                                                     'Hypermath.f2f'],
 'Hypermath.PathTransport.Reproduction.append': [],
 'Hypermath.PathTransport.reproduce': [],
 'Hypermath.PathTransport.composeAcross': [],
 'Hypermath.PathTransport.atLayer': [],
 'Hypermath.PathTransport.raise': [],
 'Hypermath.PathTransport.nativeTransfer': ['Hypermath.Congruent',
                                            'Hypermath.Form',
                                            'Hypermath.Simulation',
                                            'Hypermath.f2f'],
 'Hypermath.PathTransport.Checks.reproduced_copy_changes_endpoint': [],
 'Hypermath.PathTransport.Checks.original_and_copy_retained': [],
 'Hypermath.PathTransport.Checks.path_preserves_component': [],
 'Hypermath.PathTransport.Checks.related_without_connector': [],
 'Hypermath.PathTransport.Checks.relation_alone_insufficient': []})
LAYERED_DERIVATION_DEPENDENCIES.update({'HypermathTransportCountermodel.simulation_is_equivalence': [],
 'HypermathTransportCountermodel.forming_preserves_not_limit': ['propext'],
 'HypermathTransportCountermodel.finite_position_not_limit': ['propext'],
 'HypermathTransportCountermodel.simulation_limit_iff': ['propext'],
 'HypermathTransportCountermodel.full_axioms_hold': ['propext'],
 'HypermathTransportCountermodel.self_derivation_holds': [],
 'HypermathTransportCountermodel.cycle_has_two_steps': [],
 'HypermathTransportCountermodel.related_starts_are_ground_generated': [],
 'HypermathTransportCountermodel.step_stays_in_cycle': ['propext'],
 'HypermathTransportCountermodel.path_stays_in_cycle': ['propext'],
 'HypermathTransportCountermodel.no_finite_reproduction': ['Quot.sound', 'propext'],
 'HypermathTransportCountermodel.native_one_step_law_fails': ['Quot.sound', 'propext'],
 'HypermathTransportCountermodel.no_step_transfer': ['Quot.sound', 'propext'],
 'HypermathTransportCountermodel.full_model_with_cycle_without_reproduction': ['Quot.sound',
                                                                               'propext'],
 'HypermathTransportCountermodel.cycleWitness': []})
LAYERED_DERIVATION_TARGETS = tuple(LAYERED_DERIVATION_DEPENDENCIES)

PROBE_TARGETS = {"countermodel": COUNTERMODEL_TARGETS, "finite_trace": TRACE_CHECK_TARGETS,
                 "observation": OBSERVATION_TARGETS, "full_model": FULL_MODEL_TARGETS,
                 "finite_action": ACTION_COUNTERMODEL_TARGETS,
                 "ground_syntax": GROUND_SYNTAX_TARGETS,
                 "ground_derivation": GROUND_DERIVATION_TARGETS,
                 "record_encoding": RECORD_ENCODING_TARGETS,
                 "record_machine": RECORD_MACHINE_TARGETS,
                 "layered_derivation": LAYERED_DERIVATION_TARGETS}


def probe_dependencies_valid(name: str, records: dict[str, list[str]]) -> bool:
    if name == "full_model":
        return records == FULL_MODEL_DEPENDENCIES
    if name == "finite_action":
        return records == ACTION_COUNTERMODEL_DEPENDENCIES
    if name == "observation":
        return records == OBSERVATION_DEPENDENCIES
    if name == "ground_syntax":
        return records == GROUND_SYNTAX_DEPENDENCIES
    if name == "ground_derivation":
        return records == GROUND_DERIVATION_DEPENDENCIES
    if name == "record_encoding":
        return records == RECORD_ENCODING_DEPENDENCIES
    if name == "record_machine":
        return records == RECORD_MACHINE_DEPENDENCIES
    if name == "layered_derivation":
        return records == LAYERED_DERIVATION_DEPENDENCIES
    allowed = LEAN_BUILTINS if name == "countermodel" else frozenset()
    return all(dep in allowed for deps in records.values() for dep in deps)


def digest(value: dict) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def dependency_records(output: str, expected: tuple[str, ...]) -> dict[str, list[str]]:
    records = {}
    pattern = r"(?m)^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    report_prefix = r"(?m)^'[^'\n]+' (?:depends on axioms:|does not depend on any axioms)"
    matches = list(re.finditer(pattern, output))
    if len(matches) != len(re.findall(report_prefix, output)):
        raise ValueError("malformed dependency record")
    for match in matches:
        name = match.group(1)
        if name in records:
            raise ValueError("duplicate dependency record")
        if match.group(2) is None:
            deps = []
        else:
            deps = [item.strip() for item in match.group(2).split(",")]
            if not deps or any(not item for item in deps):
                raise ValueError("empty axiom dependency")
        if any(not re.fullmatch(r"[\w.]+", item) for item in deps):
            raise ValueError("malformed axiom name")
        if len(deps) != len(set(deps)):
            raise ValueError("duplicate axiom dependency")
        records[name] = sorted(deps)
    if set(records) != set(expected):
        raise ValueError("missing or unexpected dependency records")
    return records


def target_declaration_kind(output: str) -> str | None:
    """Distinguish a closed proof from a named, unproved proposition."""
    matches = re.findall(
        r"(?m)^(theorem|axiom|def|opaque)\s+Hypermath\.selfDerivation(?:\.\{[^}]*\})?\s*:",
        output,
    )
    return matches[0] if len(matches) == 1 and matches[0] in {"theorem", "def"} else None


def target_is_theorem(output: str) -> bool:
    return target_declaration_kind(output) == "theorem"


def kernel_declarations(output: str) -> dict[str, str]:
    """Read marked kernel declarations under the pinned printer configuration."""
    pattern = r"(?m)^HYPERMATH_DECL_BEGIN:([\w.]+)\n(.*?)^HYPERMATH_DECL_END:\1$"
    pairs = re.findall(pattern, output.replace("\r\n", "\n"), re.S | re.M)
    records = {name: " ".join(body.split()) for name, body in pairs}
    expected = set(AXIOM_DECLARATIONS) | set(DEFINITION_DECLARATIONS) | set(PROVED_DECLARATIONS) | {TARGET}
    if len(records) != len(pairs) or set(records) != expected:
        raise ValueError("missing, duplicate, or unexpected kernel declaration report")
    for name, declaration in records.items():
        kind = (target_declaration_kind(output) if name == TARGET else
                "theorem" if name in PROVED_DECLARATIONS else "axiom")
        if name in DEFINITION_DECLARATIONS:
            # Definition bodies and attributes are compared verbatim by policy_errors.
            continue
        if not declaration.startswith(f"{kind} {name} "):
            raise ValueError("kernel declaration has the wrong name or kind")
    for name in {TARGET} | set(PROVED_DECLARATIONS):
        if " :=" not in records[name]:
            raise ValueError("target or theorem report lacks a body")
        # A proposition definition's body IS the target statement. Never
        # discard it as though it were an irrelevant proof implementation.
        if name != TARGET or target_is_theorem(output):
            records[name] = records[name].split(" :=", 1)[0]
    return records


def policy_errors(output: str, inputs: dict, assumptions: list[dict]) -> list[str]:
    """Compare kernel declarations with the reviewed fixed assumption policy."""
    records = kernel_declarations(output)
    dependencies = dependency_records(output, DEPENDENCY_TARGETS)
    reasons = []
    if records[TARGET] not in {TARGET_STATEMENT, TARGET_CLAIM}:
        reasons.append("selfDerivation statement differs from the reviewed target")
    if {k: records[k] for k in AXIOM_DECLARATIONS} != AXIOM_DECLARATIONS:
        reasons.append("kernel axiom declarations differ from the reviewed assumption policy")
    if {k: records[k] for k in DEFINITION_DECLARATIONS} != DEFINITION_DECLARATIONS:
        reasons.append("finite construction definitions differ from the reviewed semantics")
    if {k: records[k] for k in PROVED_DECLARATIONS} != PROVED_DECLARATIONS:
        reasons.append("constructive milestone statements differ from reviewed targets")
    names = [a["name"] for a in assumptions]
    if len(names) != len(set(names)) or set(names) != set(AXIOM_DECLARATIONS):
        reasons.append("source assumption inventory differs from the reviewed allowance")
    if any(a.get("kernel_declaration") != records.get(a["name"]) for a in assumptions):
        reasons.append("reported assumption declarations do not match kernel output")
    allowed = set(AXIOM_DECLARATIONS) | LEAN_BUILTINS | {"sorryAx"}
    if any(dep not in allowed for values in dependencies.values() for dep in values):
        reasons.append("unreviewed transitive axiom dependency")
    if (set(PROVED_DEPENDENCIES) != set(PROVED_DECLARATIONS)
            or any(dependencies[name] != sorted(PROVED_DEPENDENCIES[name])
                   for name in PROVED_DECLARATIONS)):
        reasons.append("milestone dependencies differ from their individually reviewed assumptions")
    if inputs.get("lean4/Audit.lean") != AUDIT_SOURCE_SHA256:
        reasons.append("reporter source differs from reviewed reporting commands")
    if inputs.get("lean4/Countermodels.lean") != COUNTERMODEL_SOURCE_SHA256:
        reasons.append("countermodel source differs from reviewed probes")
    if inputs.get("lean4/Hypermath/Trace.lean") != TRACE_SOURCE_SHA256:
        reasons.append("finite trace semantics differ from the reviewed construction")
    if inputs.get("lean4/TraceChecks.lean") != TRACE_CHECKS_SOURCE_SHA256:
        reasons.append("finite trace checks differ from the reviewed probes")
    if inputs.get("lean4/Hypermath/Observation.lean") != OBSERVATION_SOURCE_SHA256:
        reasons.append("observation semantics differ from the reviewed construction")
    if inputs.get("lean4/ObservationChecks.lean") != OBSERVATION_CHECKS_SOURCE_SHA256:
        reasons.append("observation checks differ from the reviewed probes")
    if inputs.get("lean4/FullAxiomModel.lean") != FULL_MODEL_SOURCE_SHA256:
        reasons.append("full axiom model differs from the reviewed model")
    if inputs.get("lean4/Hypermath/FiniteAction.lean") != FINITE_ACTION_SOURCE_SHA256:
        reasons.append("finite action criterion differs from the reviewed construction")
    if inputs.get("lean4/FiniteActionCountermodel.lean") != ACTION_COUNTERMODEL_SOURCE_SHA256:
        reasons.append("finite action countermodel differs from the reviewed model")
    if inputs.get("lean4/Hypermath/GroundSyntax.lean") != GROUND_SYNTAX_SOURCE_SHA256:
        reasons.append("ground syntax and checker differ from the reviewed source fragment")
    if inputs.get("lean4/GroundSyntaxChecks.lean") != GROUND_SYNTAX_CHECKS_SOURCE_SHA256:
        reasons.append("ground syntax checks differ from the reviewed probes")
    if inputs.get("lean4/Hypermath/GroundDerivation.lean") != GROUND_DERIVATION_SOURCE_SHA256:
        reasons.append("composed ground calculus differs from the reviewed construction")
    if inputs.get("lean4/GroundDerivationChecks.lean") != GROUND_DERIVATION_CHECKS_SOURCE_SHA256:
        reasons.append("composed ground checks differ from the reviewed probes")
    if inputs.get("lean4/Hypermath/GroundCode.lean") != GROUND_CODE_SOURCE_SHA256:
        reasons.append("ground tree encoding differs from the reviewed construction")
    if inputs.get("lean4/Hypermath/RecordEncoding.lean") != RECORD_ENCODING_SOURCE_SHA256:
        reasons.append("record encoding differs from the reviewed construction")
    if inputs.get("lean4/RecordEncodingChecks.lean") != RECORD_ENCODING_CHECKS_SOURCE_SHA256:
        reasons.append("record encoding checks differ from the reviewed probes")
    if inputs.get("lean4/Hypermath/RecordMachine.lean") != RECORD_MACHINE_SOURCE_SHA256:
        reasons.append("record execution machine differs from the reviewed construction")
    if inputs.get("lean4/RecordMachineChecks.lean") != RECORD_MACHINE_CHECKS_SOURCE_SHA256:
        reasons.append("record machine checks differ from the reviewed probes")
    if inputs.get("lean4/Hypermath/RuleSubstitution.lean") != RULE_SUBSTITUTION_SOURCE_SHA256:
        reasons.append("rule substitution and retained calls differ from the reviewed construction")
    if inputs.get("lean4/Hypermath/Sequential.lean") != SEQUENTIAL_SOURCE_SHA256:
        reasons.append("sequencing laws differ from the reviewed construction")
    if inputs.get("lean4/Hypermath/UnaryFormation.lean") != UNARY_FORMATION_SOURCE_SHA256:
        reasons.append("unary formation differs from the reviewed fixed-term boundary")
    if inputs.get("lean4/Hypermath/LayeredDerivation.lean") != LAYERED_DERIVATION_SOURCE_SHA256:
        reasons.append("layered derivation differs from the reviewed preservation construction")
    if inputs.get("lean4/Hypermath/ContextualComposition.lean") != CONTEXTUAL_COMPOSITION_SOURCE_SHA256:
        reasons.append("contextual composition differs from the reviewed premise construction")
    if inputs.get("lean4/Hypermath/OperationalCorrespondence.lean") != OPERATIONAL_CORRESPONDENCE_SOURCE_SHA256:
        reasons.append("operational correspondence differs from the reviewed local-law construction")
    if inputs.get("lean4/Hypermath/TransportCountermodel.lean") != TRANSPORT_COUNTERMODEL_SOURCE_SHA256:
        reasons.append("transport countermodel differs from the reviewed full-clause construction")
    if inputs.get("lean4/Hypermath/PathTransport.lean") != PATH_TRANSPORT_SOURCE_SHA256:
        reasons.append("path transport differs from the reviewed conditional reproduction construction")
    if inputs.get("lean4/Hypermath/PathLayers.lean") != PATH_LAYERS_SOURCE_SHA256:
        reasons.append("path layers differ from the reviewed witnessed-path construction")
    if inputs.get("lean4/Hypermath/RetainedExecution.lean") != RETAINED_EXECUTION_SOURCE_SHA256:
        reasons.append("retained execution differs from the reviewed frame-preservation construction")
    if inputs.get("lean4/Hypermath/TerminalRetention.lean") != TERMINAL_RETENTION_SOURCE_SHA256:
        reasons.append("terminal retention differs from the reviewed orbit obstruction")
    if inputs.get("lean4/LayeredDerivationChecks.lean") != LAYERED_DERIVATION_CHECKS_SOURCE_SHA256:
        reasons.append("layered derivation checks differ from the reviewed probes")
    if inputs.get("lean4/SurfaceBridge.lean") != SURFACE_BRIDGE_SOURCE_SHA256:
        reasons.append("surface transport differs from the reviewed executable bridge")
    return reasons
