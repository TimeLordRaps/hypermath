"""Parse the expected Lean reports; missing or duplicate records are invalid."""

from __future__ import annotations

import hashlib
import json
import re

from ._baseline import (
    ACTION_COUNTERMODEL_SOURCE_SHA256,
    TARGET_AT_LIMIT_SOURCE_SHA256,
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
    LAYER_CONSUMPTION_CHECKS_SOURCE_SHA256,
    LAYER_DECLARATION_HOME,
    LAYERED_DERIVATION_CHECKS_SOURCE_SHA256,
    LAYERED_DERIVATION_SOURCE_SHA256,
    NONDEGENERATE_CYCLE_SOURCE_SHA256,
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
    "IrreflexiveSimilar.prefixAxioms_hold",
    "IrreflexiveSimilar.similar_reflexive_claim_fails",
    "IrreflexiveSimilar.similar_symmetric_claim_fails",
    "IrreflexiveSimilar.column_quotient_claim_fails",
    "IrreflexiveSimilar.prefix_without_reflexive_or_symmetric_similar",
    "IrreflexiveSimilar.similar_reflexivity_independent",
    "IrreflexiveSimilar.similar_symmetry_independent",
    "AsymmetricCongruent.prefixAxioms_hold",
    "AsymmetricCongruent.congruent_symmetry_claim_fails",
    "AsymmetricCongruent.congruent_symmetry_independent",
    "AsymmetricCongruent.componentwise_symmetry_is_exactly_congruent_symmetry",
    "AsymmetricCongruent.congruent_transitivity_claim_fails",
    "AsymmetricCongruent.congruent_transitivity_independent",
    "AsymmetricCongruent.congruent_is_free_above_equality",
    "IrreflexiveSimilar.similar_transitive_claim_fails",
    "IrreflexiveSimilar.congruent_reflexive_claim_fails",
    "IrreflexiveSimilar.simulation_reflexive_claim_fails",
    "IrreflexiveSimilar.congruent_reflexivity_fails_with_unreached_form",
    "similar_transitivity_independent",
    "congruent_reflexivity_independent",
    "simulation_reflexivity_independent",
    "simulation_symmetry_independent",
    "simulation_transitivity_independent",
    "FreeSimulation.prefixAxioms_hold",
    "FreeSimulation.simulation_symmetry_claim_fails",
    "FreeSimulation.simulation_transitivity_claim_fails",
    "FreeSimulation.simulation_is_free_above_equality_apart_from_axDiff",
    "FreeFiltration.prefixAxioms_of_conditions",
    "FreeFiltration.conditions_of_prefixAxioms",
    "FreeFiltration.prefixAxioms_iff_conditions",
    "FreeFiltration.reach_is_total_on_the_chain",
    "FreeFiltration.ext_conditions",
    "FreeFiltration.congruent_reflexivity_needs_an_unreached_point",
    "FreeFiltration.minimal_upper_relations_leave_five_conditions_on_similar",
    "FreeFiltration.five_hold_without_chainIsCofinal",
    "FreeFiltration.five_hold_without_similarReflexive",
    "FreeFiltration.five_hold_without_imageSimilar",
    "FreeFiltration.five_hold_without_imageSimilarToGround",
    "FreeFiltration.five_hold_without_doubleImageSimilar",
    "FreeFiltration.five_hold_without_formingAvoidsGround",
    "FreeFiltration.formedAtLeast_conditions",
    "FreeFiltration.similar_can_be_a_partial_order",
    "FreeFiltration.total_similar_leaves_exactly_three_conditions",
    "FreeFiltration.congruent_reflexivity_is_not_a_fourth_condition",
    "FreeFiltration.total_similar_makes_reach_total",
    "FreeFiltration.ground_is_not_an_image",
    "FreeFiltration.ground_is_not_a_fixed_point",
    "FreeFiltration.no_model_on_one_point",
    "FreeFiltration.two_points_are_enough",
    "FreeFiltration.two_is_the_smallest_carrier",
    "FreeFiltration.simulation_is_never_total",
    "FreeFiltration.total_congruent_forces_total_similar",
    "FreeFiltration.the_extremes_of_the_three_relations",
    "FreeFiltration.bool_ne_is_not",
    "FreeFiltration.forming_is_forced_at_two_points",
    "FreeFiltration.reach_is_total_at_two_points",
    "FreeFiltration.both_diagonals_are_forced_at_two_points",
    "FreeFiltration.similar_is_forced_off_one_cell_at_two_points",
    "FreeFiltration.two_points_are_enough_with_total_similar",
    "FreeFiltration.two_points_are_enough_with_maximal_simulation",
    "FreeFiltration.the_free_cells_are_free",
    "FreeFiltration.not_self_ne",
    "FreeFiltration.self_ne_not",
    "FreeFiltration.eight_cells_are_forced_at_two_points",
    "FreeFiltration.two_points_are_enough_with_total_congruent",
    "FreeFiltration.congruent_has_two_free_cells_at_two_points",
    "FreeFiltration.the_eight_decide_forming_and_eight_of_twelve_cells",
    "FreeFiltration.ThreeFormChoice.one_holds",
    "FreeFiltration.ThreeFormChoice.two_holds",
    "FreeFiltration.forming_is_not_forced_at_three_points",
    "FreeFiltration.two_points_determine_forming_and_three_do_not",
    "FreeFiltration.similar_is_never_equality",
    "FreeFiltration.similarity_is_not_contained_in_simulation",
    "FreeFiltration.the_three_relations_are_never_all_one",
    "FreeFiltration.congruent_may_equal_similar",
    "FreeFiltration.neither_inclusion_is_forced_to_be_strict",
    "FreeFiltration.two_hold_without_simulationIntoCongruent",
    "FreeFiltration.two_hold_without_simulationReflexive",
    "FreeFiltration.two_hold_without_imageNotSimulatingGround",
    "FreeFiltration.operationAxioms_iff_conditions",
    "FreeFiltration.prefixWithOperations_iff_conditions",
    "FreeFiltration.operations_exclude_the_unreached_point",
    "FreeFiltration.endpoints_free_off_one_path",
    "FreeFiltration.determined_by_its_closing_clause",
    "FreeFiltration.incidence_one_is_two_cases",
    "FreeFiltration.carried_symbols_are_free",
    "FreeFiltration.carrying_iff_prefix",
    "FreeFiltration.the_unmentioned_are_unconstrained",
    "FreeFiltration.carrying_iff_the_whole_clause_set",
    "FreeFiltration.carried_symbols_are_free_at_forty_four",
    "FreeFiltration.the_unmentioned_are_unconstrained_at_forty_four",
    "FreeFiltration.compose_nonempty_binders_are_inert",
    "FreeFiltration.composeAxioms_iff_conditions",
    "FreeFiltration.prefixOperationsCompose_iff_conditions",
    "FreeFiltration.compose_conditions_are_always_available",
    "FreeFiltration.composeConditions_iff_the_three",
    "FreeFiltration.strictly_associative_is_associative_up_to_cp",
    "FreeFiltration.strict_unit_is_unital_up_to_cp",
    "FreeFiltration.no_non_unit_collapses_cp",
    "FreeFiltration.NeedsAssociativeUpToCp.two_hold_and_composition_is_not_associative",
    "FreeFiltration.NeedsUnitalUpToCp.two_hold_and_the_unit_is_not_a_unit",
    "FreeFiltration.NeedsSomeNonUnit.two_hold_and_everything_is_the_unit",
    "FreeFiltration.transfiniteConditions_iff_the_five",
    "FreeFiltration.someStartAtGround_is_implied_by_the_eight",
    "FreeFiltration.someEndAtLimit_is_implied_by_the_operations",
    "FreeFiltration.two_of_the_nineteen_are_theorems_of_the_others",
    "FreeFiltration.nineteen_iff_seventeen",
    "FreeFiltration.twenty_eight_clauses_carry_the_content",
    "FreeFiltration.twenty_eight_clauses_are_seventeen_conditions",
    "FreeFiltration.the_deriver_binder_is_inert",
    "FreeFiltration.eleven_prefix_clauses_carry_the_content",
    "FreeFiltration.eleven_prefix_clauses_are_eight_conditions",
    "FreeFiltration.twenty_clauses_are_seventeen_conditions",
    "FreeFiltration.nine_prefix_clauses_carry_the_content",
    "FreeFiltration.three_implications_are_two_equivalences",
    "FreeFiltration.nine_prefix_clauses_are_eight_conditions",
    "FreeFiltration.eighteen_clauses_are_seventeen_conditions",
    "FreeFiltration.nine_is_six_and_a_cycle",
    "FreeFiltration.DropsReachIntoCongruent.six_hold_and_reach_does_not_reach_congruence",
    "FreeFiltration.DropsCongruentIntoSimulation.six_hold_and_congruence_does_not_reach_equality",
    "FreeFiltration.DropsSimulationIntoReach.six_hold_and_equality_does_not_reach_back",
    "FreeFiltration.the_unit_clause_is_two",
    "FreeFiltration.the_successor_clause_is_two",
    "FreeFiltration.WitnessConjunctionDoesNotSplit.the_halves_hold_and_the_clause_fails",
    "FreeFiltration.splitComposeAxioms_iff_conditions",
    "FreeFiltration.compose_is_four_split_conditions",
    "FreeFiltration.sharp_transfinite_is_four_split_conditions",
    "FreeFiltration.twenty_split_clauses_are_nineteen_split_conditions",
    "FreeFiltration.unitalUpToCp_iff_the_two_halves",
    "FreeFiltration.TheUnitalHalvesAreTwo.neither_unital_half_implies_the_other",
    "FreeFiltration.succEscapes_iff_the_two_halves",
    "FreeFiltration.TheSuccHalvesAreTwo.neither_succ_half_implies_the_other",
    "FreeFiltration.the_hub_is_two_implications",
    "FreeFiltration.conditions_are_eight_split_conditions",
    "FreeFiltration.nine_clauses_are_eight_split_conditions",
    "FreeFiltration.three_arrows_are_two_arrows",
    "FreeFiltration.the_two_lists_agree_over_the_six",
    "FreeFiltration.neither_list_has_a_removable_member",
    "FreeFiltration.two_irredundant_lists_of_different_lengths",
    "FreeFiltration.no_uniform_derivation",
    "FreeFiltration.no_other_pair_of_arrows_is_the_hub",
    "FreeFiltration.the_hub_pair_does_say_it",
    "FreeFiltration.no_two_of_the_triangle_suffice",
    "FreeFiltration.the_hub_is_the_unique_minimum",
    "AxiomsMeasureVocabulary.the_image_misses_the_ground_by_library",
    "AxiomsMeasureVocabulary.the_image_misses_the_ground_by_hand",
    "FreeFiltration.a_limit_on_the_chain_absorbs_it",
    "FreeFiltration.unreached_limits_are_not_simulated_finitely",
    "FreeFiltration.a_moving_successor_escapes",
    "FreeFiltration.NeedsLimitAbsorbsTheChain.eighteen_hold_and_the_limit_does_not_absorb_the_chain",
    "FreeFiltration.NeedsLimitNotSimulatedFinitely.eighteen_hold_and_a_chain_point_simulates_the_limit",
    "FreeFiltration.NeedsSuccEscapes.eighteen_hold_and_the_successor_stands_still",
    "FreeFiltration.lists_join_freely_exactly_on_disjoint_symbols",
    "FreeFiltration.transfinite_clauses_are_five_conditions",
    "FreeFiltration.all_thirty_nine_iff_nineteen_conditions",
    "FreeFiltration.all_forty_four_iff_twenty_four_conditions",
    "FreeFiltration.closingAxioms_iff_conditions",
    "FreeFiltration.chain_points_are_reached",
    "FreeFiltration.the_limit_is_off_the_chain",
    "FreeFiltration.no_three_distinct_booleans",
    "FreeFiltration.no_limit_on_two_points",
    "FreeFiltration.operation_conditions_hold_on_one_point",
    "FreeFiltration.transfinite_conditions_hold_on_one_point",
    "FreeFiltration.only_the_prefix_demands_a_second_form",
    "FreeFiltration.the_third_form_is_a_joint_demand",
    "FreeFiltration.no_compose_on_one_path",
    "FreeFiltration.two_paths_are_enough",
    "FreeFiltration.two_is_the_smallest_path_carrier",
    "FreeFiltration.ThreePointLimit.conditions_hold",
    "FreeFiltration.ThreePointLimit.transfinite_conditions_hold",
    "FreeFiltration.ThreePointLimit.all_nineteen_conditions_hold",
    "FreeFiltration.three_is_the_smallest_carrier_with_a_limit",
    "FreeFiltration.spanned_carriers_admit_no_limit",
    "FreeFiltration.LimitAdjoined.all_nineteen_conditions_hold",
    "FreeFiltration.nineteen_is_not_fourteen_plus_five",
    "FreeFiltration.the_closes_are_definitional",
    "FreeFiltration.three_of_the_fourteen_are_derivable",
    "FreeFiltration.prefix_is_its_fourteen_contentful_clauses",
    "FreeFiltration.twenty_nine_clauses_carry_the_content",
    "FreeFiltration.the_canonical_clauses_are_the_free_ones",
    "FreeFiltration.conditions_iff_the_eight",
    "FreeFiltration.reached_points_are_self_congruent",
    "FreeFiltration.self_simulating_points_are_reached",
    "FreeFiltration.conditions_iff_six_and_two_implications",
    "FreeFiltration.NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable",
    "FreeFiltration.NeedsSimulationDiagonalIsReach.the_rising_half_is_not_derivable",
    "FreeFiltration.NeedsSimIntoCong.seven_hold_and_the_inclusion_fails",
    "FreeFiltration.NeedsCongIntoSim.seven_hold_and_the_descent_fails",
    "FreeFiltration.NeedsImageSimilar.seven_hold_and_the_image_is_not_similar",
    "FreeFiltration.NeedsImageSimilarToGround.seven_hold_and_the_image_misses_the_ground",
    "FreeFiltration.NeedsDoubleImageSimilar.seven_hold_and_the_double_image_is_not_similar",
    "FreeFiltration.NeedsImageNotSimulatingGround.seven_hold_and_the_denial_fails",
    "FreeFiltration.NeedsCongruentDiagonalIsReach.seven_hold_and_the_congruent_diagonal_fails",
    "FreeFiltration.NeedsSimulationDiagonalIsReach.seven_hold_and_the_simulation_diagonal_fails",
    "FreeFiltration.operationConditions_iff_the_three",
    "FreeFiltration.reached_points_are_their_own_identity_witness",
    "FreeFiltration.a_reached_common_predecessor_pairs_them",
    "FreeFiltration.mutual_predecessors_are_apart_witnesses",
    "FreeFiltration.NeedsApartWitnesses.ten_hold_and_nothing_is_apart",
    "FreeFiltration.NeedsIdentityWitness.ten_hold_and_one_point_has_no_identity_witness",
    "FreeFiltration.NeedsPairedWitnesses.ten_hold_and_one_pair_is_unpaired",
    "WeakPositionPrice.notFiniteByTransitivity",
    "WeakPositionPrice.derivedByPathByBridge",
    "WeakPositionPrice.the_weak_position_is_unaffordable_here",
    "FreeFiltration.ComposeNeedsTransitivity.fourFold_of_transitive",
    "FreeFiltration.ComposeNeedsTransitivity.related_satisfies_the_clauses",
    "FreeFiltration.ComposeNeedsTransitivity.related_denies_the_four_fold",
    "FreeFiltration.ComposeNeedsTransitivity.related_is_reflexive",
    "FreeFiltration.ComposeNeedsTransitivity.four_fold_without_transitivity",
    "FreeFiltration.FormClosureIsOneDirection.the_ground_closure_needs_only_the_loop",
    "FreeFiltration.FormClosureIsOneDirection.the_close_clause_is_exactly_its_converse",
    "FreeFiltration.FormClosureIsOneDirection.the_other_clauses_do_not_give_the_close",
    "FreeFiltration.ComposeNeedsTransitivity.transitivity_is_exactly_the_missing_step",
    "FreeFiltration.NeedsFormingIsNotCongruentToGround.four_hold_and_the_denial_fails",
    "FreeFiltration.NeedsCongruentPathIsSymmetric.four_hold_and_path_congruence_is_not_symmetric",
    "FreeFiltration.NeedsSimilarIsReflexive.four_hold_and_similarity_is_not_reflexive",
    "FreeFiltration.NeedsSimilarIsSymmetric.four_hold_and_similarity_is_not_symmetric",
    "FreeFiltration.NeedsCongruentIsTransitive.four_hold_and_congruence_is_not_transitive",
))

# The exact axiom cost of every countermodel report, measured rather than
# bounded. This was the last probe group checked only for the absence of
# exotic axioms, which let a report's cost change silently as long as the
# source digest was refreshed with it --- and the pair in
# `AxiomsMeasureVocabulary` exists precisely to show that a cost can change
# with no model changed and nothing reproved. Four shapes, and which report
# has which is a fact about how a proof is written, not about what it says.
# Choice enters exactly at the limit: every report that adjoins the
# unreached point and no other.
COUNTERMODEL_CLASSICAL = frozenset((
    "FreeFiltration.LimitAdjoined.all_nineteen_conditions_hold",
    "FreeFiltration.NeedsLimitAbsorbsTheChain.eighteen_hold_and_the_limit_does_not_absorb_the_chain",
    "FreeFiltration.NeedsLimitNotSimulatedFinitely.eighteen_hold_and_a_chain_point_simulates_the_limit",
    "FreeFiltration.NeedsSuccEscapes.eighteen_hold_and_the_successor_stands_still",
    "FreeFiltration.nineteen_is_not_fourteen_plus_five",
))

# Quotient soundness arrives with the decision procedures.
COUNTERMODEL_QUOTIENT = frozenset((
    "FreeFiltration.NeedsSimilarIsReflexive.four_hold_and_similarity_is_not_reflexive",
    "FreeFiltration.NeedsSimilarIsSymmetric.four_hold_and_similarity_is_not_symmetric",
    "FreeFiltration.NeedsCongruentIsTransitive.four_hold_and_congruence_is_not_transitive",
    "AsymmetricCongruent.congruent_symmetry_independent",
    "similar_transitivity_independent",
    "congruent_reflexivity_independent",
    "simulation_reflexivity_independent",
    "simulation_symmetry_independent",
    "simulation_transitivity_independent",
    "IrreflexiveSimilar.similar_reflexivity_independent",
    "IrreflexiveSimilar.similar_symmetry_independent",
    "AsymmetricCongruent.congruent_transitivity_independent",
    "FreeFiltration.NeedsApartWitnesses.ten_hold_and_nothing_is_apart",
    "FreeFiltration.NeedsDoubleImageSimilar.seven_hold_and_the_double_image_is_not_similar",
    "FreeFiltration.NeedsIdentityWitness.ten_hold_and_one_point_has_no_identity_witness",
    "FreeFiltration.NeedsImageSimilar.seven_hold_and_the_image_is_not_similar",
    "FreeFiltration.NeedsImageSimilarToGround.seven_hold_and_the_image_misses_the_ground",
    "FreeFiltration.NeedsPairedWitnesses.ten_hold_and_one_pair_is_unpaired",
    "FreeFiltration.determined_by_its_closing_clause",
    "FreeFiltration.incidence_one_is_two_cases",
    "directionality_claim_fails",
    "prefixAxioms_hold",
    "preserving_prefix_axioms_hold",
))

# Proposition extensionality, almost always through a rewriting tactic
# or through `Nat.succ_ne_zero`, which is itself proved with it.
COUNTERMODEL_PROPEXT = frozenset((
    "FreeFiltration.NeedsCongruentPathIsSymmetric.four_hold_and_path_congruence_is_not_symmetric",
    "FreeFiltration.NeedsFormingIsNotCongruentToGround.four_hold_and_the_denial_fails",
    "FreeFiltration.NeedsCongruentPathIsSymmetric.four_hold_and_path_congruence_is_not_symmetric",
    "AsymmetricCongruent.congruent_is_free_above_equality",
    "AsymmetricCongruent.prefixAxioms_hold",
    "AxiomsMeasureVocabulary.the_image_misses_the_ground_by_library",
    "FreeFiltration.DropsSimulationIntoReach.six_hold_and_equality_does_not_reach_back",
    "FreeFiltration.NeedsCongIntoSim.seven_hold_and_the_descent_fails",
    "FreeFiltration.NeedsCongruentDiagonalIsReach.seven_hold_and_the_congruent_diagonal_fails",
    "FreeFiltration.NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable",
    "FreeFiltration.NeedsSimIntoCong.seven_hold_and_the_inclusion_fails",
    "FreeFiltration.compose_conditions_are_always_available",
    "FreeFiltration.congruent_reflexivity_needs_an_unreached_point",
    "FreeFiltration.five_hold_without_chainIsCofinal",
    "FreeFiltration.five_hold_without_similarReflexive",
    "FreeFiltration.five_hold_without_imageSimilar",
    "FreeFiltration.five_hold_without_imageSimilarToGround",
    "FreeFiltration.five_hold_without_doubleImageSimilar",
    "FreeFiltration.endpoints_free_off_one_path",
    "FreeFiltration.ext_conditions",
    "FreeFiltration.formedAtLeast_conditions",
    "FreeFiltration.ThreePointLimit.conditions_hold",
    "FreeFiltration.ThreePointLimit.transfinite_conditions_hold",
    "FreeFiltration.ThreePointLimit.all_nineteen_conditions_hold",
    "FreeFiltration.ThreeFormChoice.one_holds",
    "FreeFiltration.ThreeFormChoice.two_holds",
    "FreeFiltration.forming_is_not_forced_at_three_points",
    "FreeFiltration.two_points_determine_forming_and_three_do_not",
    "FreeFiltration.three_is_the_smallest_carrier_with_a_limit",
    "FreeFiltration.neither_inclusion_is_forced_to_be_strict",
    "FreeFiltration.lists_join_freely_exactly_on_disjoint_symbols",
    "FreeFiltration.neither_list_has_a_removable_member",
    "FreeFiltration.no_other_pair_of_arrows_is_the_hub",
    "FreeFiltration.no_two_of_the_triangle_suffice",
    "FreeFiltration.operations_exclude_the_unreached_point",
    "FreeFiltration.reach_is_total_on_the_chain",
    "FreeFiltration.similar_can_be_a_partial_order",
    "FreeFiltration.the_hub_is_the_unique_minimum",
    "FreeFiltration.two_irredundant_lists_of_different_lengths",
    "FreeSimulation.prefixAxioms_hold",
    "FreeSimulation.simulation_is_free_above_equality_apart_from_axDiff",
    "IrreflexiveSimilar.congruent_reflexivity_fails_with_unreached_form",
    "IrreflexiveSimilar.prefixAxioms_hold",
    "IrreflexiveSimilar.prefix_without_reflexive_or_symmetric_similar",
    "WeakPositionPrice.the_weak_position_is_unaffordable_here",
    "d_spans_ground_claim_fails",
    "driver_cycle_claim_fails",
    "driver_endpoint_cycle_without_positive_trace",
    "reverse_filtration_fails",
))

COUNTERMODEL_DEPENDENCIES = {
    name: (
        ["Classical.choice", "Quot.sound", "propext"]
        if name.removeprefix("HypermathCountermodel.") in COUNTERMODEL_CLASSICAL
        else ["Quot.sound", "propext"]
        if name.removeprefix("HypermathCountermodel.") in COUNTERMODEL_QUOTIENT
        else ["propext"]
        if name.removeprefix("HypermathCountermodel.") in COUNTERMODEL_PROPEXT
        else []
    )
    for name in COUNTERMODEL_TARGETS
}

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
    "HypermathFullAxiomModel.preClosureAxiomsWith_congruentPath": ['Classical.choice', 'Quot.sound', 'propext'],
    "HypermathFullAxiomModel.asym_violates_axCongruentPathSymm": ['propext'],
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
    "HypermathFullAxiomModel.directionality_holds": ["Quot.sound", "propext"],
    "HypermathFullAxiomModel.full_clauses_with_directional_derives": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.fullAxiomsWith_congruentPath": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.congruentPathInternals_holds": [],
    "HypermathFullAxiomModel.asym_full_axioms_hold": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.congruentPathInternals_claim_fails": ["propext"],
    "HypermathFullAxiomModel.congruentPath_symmetry_independent": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.tupleCongruentPath_iff": [],
    "HypermathFullAxiomModel.tuple_full_axioms_hold": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.tupleCongruentPath_symm_of_congruent_symm": [],
    "HypermathFullAxiomModel.tuple_reading_consistent_and_conditional": [
        "Classical.choice", "Quot.sound", "propext",
    ],
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
    "HypermathFullAxiomModel.ground_is_not_its_image": [],
    "HypermathFullAxiomModel.distinct_operations_claim_holds": [],
    "HypermathFullAxiomModel.full_clauses_with_distinct_operations": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.transport_derives_is_symmetric": [],
    "HypermathFullAxiomModel.directionality_independent": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.distinct_operations_independent": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    # §XIV: the three path clauses with compose, pathGround and congruentPath
    # all open. Varying congruentPath alone left reflexivity looking forced.
    "HypermathFullAxiomModel.model_path_clauses": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.shift_path_clauses": ["Quot.sound", "propext"],
    "HypermathFullAxiomModel.congruentPath_is_not_an_equivalence": [
        "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.path_clauses_decide_nothing_about_congruence": [
        "Classical.choice", "Quot.sound", "propext",
    ],
    "HypermathFullAxiomModel.closing_clauses_consistent_with_full_axioms": [
        "Classical.choice", "Quot.sound", "propext",
    ],
}
FULL_MODEL_TARGETS = tuple(FULL_MODEL_DEPENDENCIES)
ACTION_COUNTERMODEL_TARGETS = tuple("HypermathFiniteActionCountermodel." + name for name in (
    "full_axioms_hold", "numeral_collision", "action_disagreement",
    "finite_action_incompatible", "no_exact_finite_action", "congruence_is_equivalence",
    "relation_action_incompatible", "no_congruent_finite_action",
    "ordinal_zero_identity_claim_fails", "ordinal_successor_action_claim_fails",
    "path_length_arithmetic_claim_fails", "self_derivation_target_fails_at_limit",
    "self_derivation_without_arithmetic_bridge",
    "numeral_equality_observation_fails", "no_numeral_equality_decoder",
    "primitive_records_collide", "primitive_conclusions_differ",
    "no_semantic_primitive_record_decoder",
    "no_preserving_step", "every_D_entry_is_empty", "no_nonzero_D_entry",
    "full_clauses_without_nonzero_D", "self_derivation_independent",
))
ACTION_COUNTERMODEL_DEPENDENCIES = {
    name: (
        ["Quot.sound", "propext"]
        if name.endswith((".full_axioms_hold", ".self_derivation_without_arithmetic_bridge",
                          ".full_clauses_without_nonzero_D", ".self_derivation_independent"))
        else ["propext"] if name.endswith((".no_preserving_step",
                                           ".every_D_entry_is_empty", ".no_nonzero_D_entry")) else []
    )
    for name in ACTION_COUNTERMODEL_TARGETS
}
# The same interpretation problem answered the other way. This model gives up the
# action disagreement and keeps the self-derivation target, which is the pairing
# the finite-action model carried before the deriver's position was declared.
TARGET_AT_LIMIT_TARGETS = tuple("HypermathTargetAtLimitModel." + name for name in (
    "full_axioms_hold", "congruence_is_equivalence", "self_derivation_target_holds",
    "no_preserving_step", "every_D_entry_is_empty", "no_nonzero_D_entry",
    "full_clauses_and_target_without_nonzero_D", "deriver_is_not_finite",
    "no_simulation_step", "every_simulation_entry_is_empty", "no_driver_cycle_witness",
    "target_does_not_yield_a_cycle_certificate", "cycle_certificate_independent",
    "successor_agreement_holds", "transport_successor_disagrees",
    "certificate_tracks_successor_agreement", "simulation_is_transitive",
    "transport_simulation_is_transitive",
    "cycle_certificate_independent_under_transitivity",
    "transport_cycle_is_degenerate", "apply_moves_the_deriver",
    "cycle_certificate_independent_nondegenerately",
))
# Cheaper than the finite-action model's: its clause proofs are structural rather
# than simp-driven, so nothing in this file reaches quotient soundness, and the
# two propositions carrying the target's own content cost no axiom at all.
# The four carrying the target's own content and the successor law's own content
# cost nothing: each is a structural term rather than a case split over clauses.
TARGET_AT_LIMIT_AXIOM_FREE = frozenset((
    "congruence_is_equivalence", "self_derivation_target_holds",
    "successor_agreement_holds", "transport_successor_disagrees",
    "simulation_is_transitive", "transport_simulation_is_transitive",
    "transport_cycle_is_degenerate", "apply_moves_the_deriver",
))
TARGET_AT_LIMIT_DEPENDENCIES = {
    name: ([] if name.rsplit(".", 1)[-1] in TARGET_AT_LIMIT_AXIOM_FREE else ["propext"])
    for name in TARGET_AT_LIMIT_TARGETS
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
LAYERED_DERIVATION_DEPENDENCIES.update({'HypermathTransportCountermodel.congruent_is_total': [],
 'HypermathTransportCountermodel.distinct_operations_claim_fails': [],
 'HypermathTransportCountermodel.no_incongruence_is_derivable': ['propext'],
 'HypermathTransportCountermodel.sequencing_asymmetry_never_applies': [],
 'HypermathTransportCountermodel.nothing_separates_the_two_operations': ['propext']})
LAYERED_DERIVATION_TARGETS = tuple(LAYERED_DERIVATION_DEPENDENCIES)

# The four files that declare the theory's own symbols and clauses, in the
# order they are layered. A report names two vocabularies at once: the Lean
# foundation axioms a proof costs, and the declarations from this list it
# uses. Only the second says anything about the layer stack.
LAYER_FILE_ORDER = ('L0Ground', 'L1Relations', 'L2Operations', 'L3Ordinatics')
# What the Lean kernel supplies, plus the marker an admitted proof leaves
# behind. Derived from the reviewed list rather than spelled again: two
# spellings of one list in two modules is two things to keep right, and the
# only use either has is membership.
LAYER_FOUNDATION = frozenset(LEAN_BUILTINS | {"sorryAx"})

LAYER_AXIOM_HOME = {
    'Hypermath.Congruent': 'L0Ground',
    'Hypermath.Definition': 'L0Ground',
    'Hypermath.Derives': 'L0Ground',
    'Hypermath.Discharge': 'L0Ground',
    'Hypermath.Form': 'L0Ground',
    'Hypermath.FormClosure': 'L0Ground',
    'Hypermath.HMSyntax': 'L0Ground',
    'Hypermath.Semantics': 'L0Ground',
    'Hypermath.Similar': 'L0Ground',
    'Hypermath.Simulation': 'L0Ground',
    'Hypermath.Substance': 'L0Ground',
    'Hypermath.axBox': 'L0Ground',
    'Hypermath.axCongruentTrans': 'L0Ground',
    'Hypermath.axDiff': 'L0Ground',
    'Hypermath.axDiffCongruent': 'L0Ground',
    'Hypermath.axFormClosesLoop': 'L0Ground',
    'Hypermath.axGroundSelf': 'L0Ground',
    'Hypermath.axGroundSemanticsAx': 'L0Ground',
    'Hypermath.axGroundSubstanceAx': 'L0Ground',
    'Hypermath.axGroundSyntaxAx': 'L0Ground',
    'Hypermath.axSemanticsRequiresSyntax': 'L0Ground',
    'Hypermath.axSim': 'L0Ground',
    'Hypermath.axSimilarRefl': 'L0Ground',
    'Hypermath.axSimilarSymm': 'L0Ground',
    'Hypermath.axSubstanceRequiresSemantics': 'L0Ground',
    'Hypermath.axSyntaxRequiresSubstance': 'L0Ground',
    'Hypermath.closeDefinitionOpaque': 'L0Ground',
    'Hypermath.closeDerivesOpaque': 'L0Ground',
    'Hypermath.closeDischargeOpaque': 'L0Ground',
    'Hypermath.closeFormClosureOpaque': 'L0Ground',
    'Hypermath.closeSemanticsOpaque': 'L0Ground',
    'Hypermath.closeStructContinues': 'L0Ground',
    'Hypermath.closeStructDistinct': 'L0Ground',
    'Hypermath.closeStructOrbits': 'L0Ground',
    'Hypermath.closeSubstanceOpaque': 'L0Ground',
    'Hypermath.closeSyntaxOpaque': 'L0Ground',
    'Hypermath.f2f': 'L0Ground',
    'Hypermath.ground': 'L0Ground',
    'Hypermath.structContinues': 'L0Ground',
    'Hypermath.structDistinct': 'L0Ground',
    'Hypermath.structOrbits': 'L0Ground',
    'Hypermath.deriver': 'L1Relations',
    'Hypermath.filtrationCongSim': 'L1Relations',
    'Hypermath.filtrationSimCong': 'L1Relations',
    'Hypermath.traceLevels': 'L1Relations',
    'Hypermath.DerivationPath': 'L2Operations',
    'Hypermath.axComposeAssoc': 'L2Operations',
    'Hypermath.axComposeIdentity': 'L2Operations',
    'Hypermath.axComposeNonempty': 'L2Operations',
    'Hypermath.axCongruentPathSymm': 'L2Operations',
    'Hypermath.axCoop': 'L2Operations',
    'Hypermath.axCoopComm': 'L2Operations',
    'Hypermath.axCoopIdentity': 'L2Operations',
    'Hypermath.axSeq': 'L2Operations',
    'Hypermath.axSeqAsymm': 'L2Operations',
    'Hypermath.axSeqIdentityL': 'L2Operations',
    'Hypermath.axSeqIdentityR': 'L2Operations',
    'Hypermath.compose': 'L2Operations',
    'Hypermath.congruentPath': 'L2Operations',
    'Hypermath.pathEnd': 'L2Operations',
    'Hypermath.pathGround': 'L2Operations',
    'Hypermath.pathLength': 'L2Operations',
    'Hypermath.pathStart': 'L2Operations',
    'Hypermath.pathStep': 'L2Operations',
    'Hypermath.pathTrace': 'L2Operations',
    'Hypermath.ordinatics': 'L3Ordinatics',
}

LAYER_CONSUMPTION_TARGETS = tuple(LAYER_DECLARATION_HOME)

# Which layers' declarations each file's content actually consumes. Counts
# move whenever a proof is rewritten; this support does not, and it is the
# support that says whether the stack is a chain.
LAYER_CONSUMPTION_SUPPORT = {
    'FiniteAction': ('L0Ground',),
    'GroundDerivation': ('L0Ground',),
    'GroundSyntax': ('L0Ground',),
    'L0Ground': ('L0Ground',),
    'L1Relations': ('L0Ground', 'L1Relations'),
    'L2Operations': ('L0Ground', 'L1Relations', 'L2Operations'),
    'L3Ordinatics': ('L0Ground', 'L1Relations', 'L2Operations', 'L3Ordinatics'),
    'PathLayers': ('L0Ground', 'L1Relations'),
    'PathTransport': ('L0Ground',),
    'QuadrilateralFiltration': ('L0Ground',),
}

# Declared and used by nothing: asserted clauses and symbols that no proof or
# statement anywhere in the development consumes.
LAYER_UNCONSUMED = (
    'Hypermath.axComposeAssoc',
    'Hypermath.axSeqIdentityL',
    'Hypermath.closeFormClosureOpaque',
    'Hypermath.pathStep',
    'Hypermath.pathTrace',
)

# Declared and used once: the sole consumer of each name that exactly one
# declaration in the development consumes. Counts are not structural and are
# not pinned anywhere --- but the step from one to zero is, because it is the
# step out of the development and into `LAYER_UNCONSUMED`. Five of these seven
# are held by two theorems, so the idle set is five given these proofs and ten
# without them: what the sweep measures is the development, not the theory.
LAYER_SPENT_ONCE = {
    'Hypermath.Discharge': 'Hypermath.dischargeIsAbstractionTier',
    'Hypermath.FormClosure': 'Hypermath.groundIsFormClosed',
    'Hypermath.axCongruentPathSymm': 'Hypermath.congruentPathInternals',
    'Hypermath.axFormClosesLoop': 'Hypermath.groundIsFormClosed',
    'Hypermath.axGroundSyntaxAx': 'Hypermath.groundIsFormClosed',
    'Hypermath.axSeqAsymm': 'Hypermath.plusAndAdditionallyAreDistinct',
    'Hypermath.axSeqIdentityR': 'Hypermath.sequencingClausesAreCooperationClauses',
    'Hypermath.axSimilarSymm': 'Hypermath.similarSymmetric',
    'Hypermath.closeDischargeOpaque': 'Hypermath.dischargeIsAbstractionTier',
}

# Applied, but only inside proofs that are not finished: names every one of
# whose consumers is an admitted declaration. There are no admissions left, so
# there are none; `axSeqAsymm` left this row when `axDiffCongruent` supplied
# the incongruence its one consumer had admitted.
LAYER_HELD_ONLY_BY_ADMISSION: tuple[str, ...] = ()

# Files in which every single declaration consumes a declared name. The
# fourteen files that consume nothing at all are already pinned by their
# absence from LAYER_CONSUMPTION_SUPPORT; this splits the ten that remain.
# These five are the theory: no generic lemma, no arithmetic helper, nothing
# that would still typecheck with the clause list deleted. The other five are
# the bridge --- mostly silent files with a thin seam of declarations that
# reach the vocabulary.
LAYER_WHOLLY_CONSUMING = (
    'L0Ground',
    'L1Relations',
    'L2Operations',
    'L3Ordinatics',
    'QuadrilateralFiltration',
)

# The seam, name by name. `LAYER_WHOLLY_CONSUMING` says which files are the
# theory; this says exactly what the five files that are not the theory take
# from it. The support table above answers the same question by layer, and by
# layer is too coarse to be an interface: it says `GroundSyntax` reaches
# `L0Ground`, which is true of a file using only `Form` and true of a file
# using every clause L0 declares.
#
# Read down the values and the shape of the development is visible. Thirty-three
# of the thirty-eight bridging declarations take symbols only --- `Form`, `f2f`,
# `ground`, the four relations --- and go nowhere near a clause. The five that
# do reach a clause are two mirrored pairs and one lemma: `nativeModel` and
# `native_check_sound` in each of the two ground files, which are a model of the
# ground theory and its soundness and so are exactly the declarations that must
# discharge clauses, plus `cycle_witness_length_preserved`, which needs one
# filtration clause. So the theory's clause list is confined to five files and
# five further declarations, and twenty-six of the thirty-four clauses are never
# consumed outside the five --- among them every clause `L2Operations` declares.
LAYER_BRIDGE_VOCABULARY = {
    'FiniteAction': (
        'Hypermath.Form',
        'Hypermath.f2f',
        'Hypermath.ground',
    ),
    'GroundDerivation': (
        'Hypermath.Form',
        'Hypermath.Similar',
        'Hypermath.Simulation',
        'Hypermath.axBox',
        'Hypermath.axDiff',
        'Hypermath.axGroundSelf',
        'Hypermath.axSim',
        'Hypermath.closeStructContinues',
        'Hypermath.closeStructDistinct',
        'Hypermath.closeStructOrbits',
        'Hypermath.f2f',
        'Hypermath.ground',
        'Hypermath.structContinues',
        'Hypermath.structDistinct',
        'Hypermath.structOrbits',
    ),
    'GroundSyntax': (
        'Hypermath.Form',
        'Hypermath.axBox',
        'Hypermath.axDiff',
        'Hypermath.axGroundSelf',
        'Hypermath.axSim',
        'Hypermath.f2f',
        'Hypermath.ground',
        'Hypermath.structContinues',
        'Hypermath.structDistinct',
        'Hypermath.structOrbits',
    ),
    'PathLayers': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.Simulation',
        'Hypermath.deriver',
        'Hypermath.f2f',
        'Hypermath.filtrationSimCong',
    ),
    'PathTransport': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.Simulation',
        'Hypermath.f2f',
    ),
}


# Declared names that only the seam consumes: the theory would declare them
# and never use them, and deleting the five bridge files would make them idle.
# There are none, and that is the fact worth pinning. It says the bridge takes
# a subset of the theory's own working vocabulary and asks for nothing of its
# own, which is the precise sense in which it is an application of the theory
# rather than a part of it. An empty cell here is what makes the four classes
# a partition: idle, inward only, both sides, and nothing beyond the seam.
LAYER_SEAM_ONLY: tuple[str, ...] = ()


def layer_consumption_shape(
    records: dict[str, list[str]],
) -> tuple[dict[str, tuple[str, ...]], tuple[str, ...], dict[str, str],
           tuple[str, ...], tuple[str, ...], dict[str, tuple[str, ...]],
           tuple[str, ...]]:
    """Reduce the sweep to the seven things about it that are structural.

    Every other probe group decides its validity by comparing the records it
    was given against a reviewed table, so an axiom nobody has reviewed makes
    that comparison false and the audit reports the group as failed. This group
    reads its records through `LAYER_AXIOM_HOME` instead, so an unreviewed
    axiom would raise from inside the lookup --- and a `KeyError` is not one of
    the failures the audit catches, so the run would end with no report at all
    rather than with a failed row. The check below turns that back into the
    same failure every other group has. It is not hypothetical: adding a clause
    to the theory without adding it to the home table produces exactly this.
    """
    unreviewed = sorted({axiom for dependencies in records.values()
                         for axiom in dependencies
                         if axiom not in LAYER_FOUNDATION
                         and axiom not in LAYER_AXIOM_HOME})
    if unreviewed:
        raise ValueError(f"unreviewed axioms in the sweep: {', '.join(unreviewed)}")
    support: dict[str, set[str]] = {}
    for name, dependencies in records.items():
        sites = {LAYER_AXIOM_HOME[axiom] for axiom in dependencies
                 if axiom not in LAYER_FOUNDATION}
        if sites:
            support.setdefault(LAYER_DECLARATION_HOME[name], set()).update(sites)
    consumers: dict[str, list[str]] = {}
    for name, dependencies in records.items():
        for axiom in dependencies:
            if axiom in LAYER_AXIOM_HOME:
                consumers.setdefault(axiom, []).append(name)
    wholly = tuple(sorted(site for site in support if not any(
        LAYER_DECLARATION_HOME[name] == site
        and not any(axiom in LAYER_AXIOM_HOME for axiom in dependencies)
        for name, dependencies in records.items())))
    return ({site: tuple(sorted(sites, key=LAYER_FILE_ORDER.index))
             for site, sites in sorted(support.items())},
            tuple(sorted(name for name in LAYER_AXIOM_HOME
                         if name not in consumers)),
            {axiom: found[0] for axiom, found in sorted(consumers.items())
             if len(found) == 1},
            tuple(axiom for axiom, found in sorted(consumers.items())
                  if all('sorryAx' in records[name] for name in found)),
            wholly,
            {site: tuple(sorted(
                {axiom for name, dependencies in records.items()
                 if LAYER_DECLARATION_HOME[name] == site
                 for axiom in dependencies if axiom in LAYER_AXIOM_HOME}))
             for site in sorted(support) if site not in wholly},
            tuple(axiom for axiom, found in sorted(consumers.items())
                  if not any(LAYER_DECLARATION_HOME[name] in wholly
                             for name in found)))


PROBE_TARGETS = {"countermodel": COUNTERMODEL_TARGETS, "finite_trace": TRACE_CHECK_TARGETS,
                 "observation": OBSERVATION_TARGETS, "full_model": FULL_MODEL_TARGETS,
                 "finite_action": ACTION_COUNTERMODEL_TARGETS,
                 "target_at_limit": TARGET_AT_LIMIT_TARGETS,
                 "ground_syntax": GROUND_SYNTAX_TARGETS,
                 "ground_derivation": GROUND_DERIVATION_TARGETS,
                 "record_encoding": RECORD_ENCODING_TARGETS,
                 "record_machine": RECORD_MACHINE_TARGETS,
                 "layered_derivation": LAYERED_DERIVATION_TARGETS,
                 "layer_consumption": LAYER_CONSUMPTION_TARGETS}


def probe_dependencies_valid(name: str, records: dict[str, list[str]]) -> bool:
    if name == "full_model":
        return records == FULL_MODEL_DEPENDENCIES
    if name == "finite_action":
        return records == ACTION_COUNTERMODEL_DEPENDENCIES
    if name == "target_at_limit":
        return records == TARGET_AT_LIMIT_DEPENDENCIES
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
    if name == "layer_consumption":
        return layer_consumption_shape(records) == (
            LAYER_CONSUMPTION_SUPPORT, LAYER_UNCONSUMED, LAYER_SPENT_ONCE,
            LAYER_HELD_ONLY_BY_ADMISSION, LAYER_WHOLLY_CONSUMING,
            LAYER_BRIDGE_VOCABULARY, LAYER_SEAM_ONLY)
    if name == "countermodel":
        return records == COUNTERMODEL_DEPENDENCIES
    # Every other group that reaches here is allowed no axioms at all.
    return all(not deps for deps in records.values())


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
    if inputs.get("lean4/TargetAtLimitModel.lean") != TARGET_AT_LIMIT_SOURCE_SHA256:
        reasons.append("target-at-limit model differs from the reviewed model")
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
    if inputs.get("lean4/Hypermath/NondegenerateCycle.lean") != NONDEGENERATE_CYCLE_SOURCE_SHA256:
        reasons.append("nondegenerate cycle model differs from the reviewed moving-cycle construction")
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
    if inputs.get("lean4/LayerConsumptionChecks.lean") != LAYER_CONSUMPTION_CHECKS_SOURCE_SHA256:
        reasons.append("layer consumption sweep differs from the reviewed inventory")
    if inputs.get("lean4/SurfaceBridge.lean") != SURFACE_BRIDGE_SOURCE_SHA256:
        reasons.append("surface transport differs from the reviewed executable bridge")
    return reasons
