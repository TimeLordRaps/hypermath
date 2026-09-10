"""Parse the expected Lean reports; missing or duplicate records are invalid."""

from __future__ import annotations

import hashlib
import json
import re

from ._baseline import (
    AUDIT_SOURCE_SHA256,
    AXIOM_DECLARATIONS,
    COUNTERMODEL_SOURCE_SHA256,
    DEFINITION_DECLARATIONS,
    LEAN_BUILTINS,
    PROVED_DECLARATIONS,
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
    "Hypermath.pathLengthArithmetic", "Hypermath.simulationPairExists",
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
CLAIMS = ("self_derivation", "source_adequacy", "recursive_arithmetic_completeness")


def digest(value: dict) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def dependency_records(output: str, expected: tuple[str, ...]) -> dict[str, list[str]]:
    records = {}
    pattern = r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output):
        name = match.group(1)
        if name in records:
            raise ValueError("duplicate dependency record")
        deps = [] if match.group(2) is None else [
            item.strip() for item in match.group(2).split(",") if item.strip()
        ]
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
        reasons.append("finite D definitions differ from the reviewed semantics")
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
    constructive_allowed = LEAN_BUILTINS | {"Hypermath.Form", "Hypermath.f2f", "Hypermath.Congruent"}
    if any(dep not in constructive_allowed for name in PROVED_DECLARATIONS
           for dep in dependencies[name]):
        reasons.append("constructive milestone has an admission or an extra logical assumption")
    if inputs.get("lean4/Audit.lean") != AUDIT_SOURCE_SHA256:
        reasons.append("reporter source differs from reviewed reporting commands")
    if inputs.get("lean4/Countermodels.lean") != COUNTERMODEL_SOURCE_SHA256:
        reasons.append("countermodel source differs from reviewed probes")
    if inputs.get("lean4/Hypermath/Trace.lean") != TRACE_SOURCE_SHA256:
        reasons.append("finite trace semantics differ from the reviewed construction")
    if inputs.get("lean4/TraceChecks.lean") != TRACE_CHECKS_SOURCE_SHA256:
        reasons.append("finite trace checks differ from the reviewed probes")
    return reasons
