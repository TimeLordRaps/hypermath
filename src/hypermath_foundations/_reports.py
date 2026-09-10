"""Parse the expected Lean reports; missing or duplicate records are invalid."""

from __future__ import annotations

import hashlib
import json
import re

from ._baseline import (
    ACTION_COUNTERMODEL_SOURCE_SHA256,
    AUDIT_SOURCE_SHA256,
    AXIOM_DECLARATIONS,
    COUNTERMODEL_SOURCE_SHA256,
    DEFINITION_DECLARATIONS,
    FINITE_ACTION_SOURCE_SHA256,
    FULL_MODEL_SOURCE_SHA256,
    GROUND_CODE_SOURCE_SHA256,
    GROUND_DERIVATION_CHECKS_SOURCE_SHA256,
    GROUND_DERIVATION_SOURCE_SHA256,
    GROUND_SYNTAX_CHECKS_SOURCE_SHA256,
    GROUND_SYNTAX_SOURCE_SHA256,
    LEAN_BUILTINS,
    OBSERVATION_CHECKS_SOURCE_SHA256,
    OBSERVATION_SOURCE_SHA256,
    PROVED_DECLARATIONS,
    PROVED_DEPENDENCIES,
    RECORD_ENCODING_CHECKS_SOURCE_SHA256,
    RECORD_ENCODING_SOURCE_SHA256,
    RECORD_MACHINE_CHECKS_SOURCE_SHA256,
    RECORD_MACHINE_SOURCE_SHA256,
    TARGET_STATEMENT,
    TRACE_CHECKS_SOURCE_SHA256,
    TRACE_SOURCE_SHA256,
)

FORMAT = "hypermath-audit-1"
REPOSITORY = "https://github.com/TimeLordRaps/hypermath"
TARGET = "Hypermath.selfDerivation"
DEPENDENCY_TARGETS = (
    "Hypermath.applyGroundIsDistinct", "Hypermath.groundIsFormClosed",
    "Hypermath.orbitStructure", "Hypermath.similarReflexive",
    "Hypermath.derivesIsDirectional", "Hypermath.dIsReflexive",
    "Hypermath.plusAndAdditionallyAreDistinct", "Hypermath.pathGroundIsIdentity",
    "Hypermath.simulationPairExists",
    "Hypermath.driverCycleIsClosed", TARGET,
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
RECORD_MACHINE_TARGETS = tuple(RECORD_MACHINE_DEPENDENCIES)
FULL_MODEL_DEPENDENCIES = {
    **{"HypermathFullAxiomModel." + name: [] for name in (
        "same_conclusion_opposite_acceptance", "no_conclusion_only_record_checker",
    )},
    **{"HypermathFullAxiomModel." + name: ["propext"] for name in (
        "finite_numerals_injective", "recordValue_is_interpretation",
        "formulaValue_is_interpretation", "record_native_ready",
    )},
    **{"HypermathFullAxiomModel." + name: ["Classical.choice", "Quot.sound", "propext"]
       for name in (
           "full_axioms_hold", "boundary_probe", "full_clauses_with_faithful_records",
           "no_preserving_record_to_formula", "full_clauses_with_rejected_closed_record",
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
))
ACTION_COUNTERMODEL_DEPENDENCIES = {
    name: (
        ["Quot.sound", "propext"]
        if name.endswith((".full_axioms_hold", ".self_derivation_without_arithmetic_bridge"))
        else ["propext"] if name.endswith(".self_derivation_target_holds") else []
    )
    for name in ACTION_COUNTERMODEL_TARGETS
}
PROBE_TARGETS = {"countermodel": COUNTERMODEL_TARGETS, "finite_trace": TRACE_CHECK_TARGETS,
                 "observation": OBSERVATION_TARGETS, "full_model": FULL_MODEL_TARGETS,
                 "finite_action": ACTION_COUNTERMODEL_TARGETS,
                 "ground_syntax": GROUND_SYNTAX_TARGETS,
                 "ground_derivation": GROUND_DERIVATION_TARGETS,
                 "record_encoding": RECORD_ENCODING_TARGETS,
                 "record_machine": RECORD_MACHINE_TARGETS}


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


def target_is_theorem(output: str) -> bool:
    matches = re.findall(
        r"(?m)^(theorem|axiom|def|opaque)\s+Hypermath\.selfDerivation(?:\.\{[^}]*\})?\s*:",
        output,
    )
    return matches == ["theorem"]


def kernel_declarations(output: str) -> dict[str, str]:
    """Read marked kernel declarations under the pinned printer configuration."""
    pattern = r"(?m)^HYPERMATH_DECL_BEGIN:([\w.]+)\n(.*?)^HYPERMATH_DECL_END:\1$"
    pairs = re.findall(pattern, output.replace("\r\n", "\n"), re.S | re.M)
    records = {name: " ".join(body.split()) for name, body in pairs}
    expected = set(AXIOM_DECLARATIONS) | set(DEFINITION_DECLARATIONS) | set(PROVED_DECLARATIONS) | {TARGET}
    if len(records) != len(pairs) or set(records) != expected:
        raise ValueError("missing, duplicate, or unexpected kernel declaration report")
    for name, declaration in records.items():
        kind = "theorem" if name == TARGET or name in PROVED_DECLARATIONS else "axiom"
        if name in DEFINITION_DECLARATIONS:
            # Definition bodies and attributes are compared verbatim by policy_errors.
            continue
        if not declaration.startswith(f"{kind} {name} "):
            raise ValueError("kernel declaration has the wrong name or kind")
    for name in {TARGET} | set(PROVED_DECLARATIONS):
        if " :=" not in records[name]:
            raise ValueError("theorem report lacks a proof body")
        records[name] = records[name].split(" :=", 1)[0]
    return records


def policy_errors(output: str, inputs: dict, assumptions: list[dict]) -> list[str]:
    """Compare kernel declarations with the reviewed fixed assumption policy."""
    records = kernel_declarations(output)
    dependencies = dependency_records(output, DEPENDENCY_TARGETS)
    reasons = []
    if records[TARGET] != TARGET_STATEMENT:
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
    return reasons
