"""Parse the expected Lean reports; missing or duplicate records are invalid."""

from __future__ import annotations

import hashlib
import json
import re

from ._baseline import (
    AUDIT_SOURCE_SHA256,
    AXIOM_DECLARATIONS,
    COUNTERMODEL_SOURCE_SHA256,
    LEAN_BUILTINS,
    TARGET_STATEMENT,
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
)
COUNTERMODEL_TARGETS = tuple("HypermathCountermodel." + name for name in (
    "prefixAxioms_hold", "reverse_filtration_fails", "directionality_claim_fails",
    "d_reflexivity_claim_fails", "driver_cycle_claim_fails",
))
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
    if len(records) != len(pairs) or set(records) != set(AXIOM_DECLARATIONS) | {TARGET}:
        raise ValueError("missing, duplicate, or unexpected kernel declaration report")
    for name, declaration in records.items():
        kind = "theorem" if name == TARGET else "axiom"
        if not declaration.startswith(f"{kind} {name} :"):
            raise ValueError("kernel declaration has the wrong name or kind")
    if " :=" not in records[TARGET]:
        raise ValueError("target theorem report lacks a proof body")
    records[TARGET] = records[TARGET].split(" :=", 1)[0]
    return records


def policy_errors(output: str, inputs: dict, assumptions: list[dict]) -> list[str]:
    """Compare kernel declarations with the reviewed fixed assumption policy."""
    records = kernel_declarations(output)
    dependencies = dependency_records(output, DEPENDENCY_TARGETS)
    reasons = []
    if records[TARGET] != TARGET_STATEMENT:
        reasons.append("selfDerivation statement differs from the reviewed target")
    if {k: v for k, v in records.items() if k != TARGET} != AXIOM_DECLARATIONS:
        reasons.append("kernel axiom declarations differ from the reviewed assumption policy")
    names = [a["name"] for a in assumptions]
    if len(names) != len(set(names)) or set(names) != set(AXIOM_DECLARATIONS):
        reasons.append("source assumption inventory differs from the reviewed allowance")
    if any(a.get("kernel_declaration") != records.get(a["name"]) for a in assumptions):
        reasons.append("reported assumption declarations do not match kernel output")
    allowed = set(AXIOM_DECLARATIONS) | LEAN_BUILTINS | {"sorryAx"}
    if any(dep not in allowed for values in dependencies.values() for dep in values):
        reasons.append("unreviewed transitive axiom dependency")
    if inputs.get("lean4/Audit.lean") != AUDIT_SOURCE_SHA256:
        reasons.append("reporter source differs from reviewed reporting commands")
    if inputs.get("lean4/Countermodels.lean") != COUNTERMODEL_SOURCE_SHA256:
        reasons.append("countermodel source differs from reviewed probes")
    return reasons
