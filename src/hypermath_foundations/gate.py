"""Conservative report consistency checks, not report authentication."""

from __future__ import annotations

import re
from pathlib import PurePosixPath

from ._reports import (
    DEPENDENCY_TARGETS,
    FORMAT,
    PROBE_TARGETS,
    REPOSITORY,
    TARGET,
    dependency_records,
    digest,
    kernel_declarations,
    policy_errors,
    probe_dependencies_valid,
    target_is_theorem,
)


def evaluate_gate(report, claim="self_derivation", *, require_clean=True) -> bool:
    """Check whether report fields consistently support the requested gate.

    This does NOT authenticate arbitrary JSON, establish that its subprocesses
    really ran, or compare it with a checkout now. Consumers must run a fresh
    audit using a trusted/pinned runner and check their source revision policy.
    Stable dirty input can be inspected with require_clean=False; that does not
    make its Git revision alone an identity for the modified contents.
    """
    if claim != "self_derivation" or type(require_clean) is not bool:
        # Neither native-source adequacy nor arithmetic completeness is proved.
        return False
    try:
        if report["format"] != FORMAT or report["execution"] != {
            "mode": "lean", "completed": True,
        }:
            return False
        subject = report["subject"]
        if (subject != report["subject_after"] or subject["repository"] != REPOSITORY
                or not re.fullmatch(r"[0-9a-f]{40}", subject["revision"])
                or type(subject["dirty"]) is not bool or (require_clean and subject["dirty"])):
            return False
        inputs = report["inputs"]
        before = inputs["before"]
        if (inputs["stable"] is not True or before != inputs["after"]
                or not isinstance(before, dict) or inputs["sha256"] != digest(before)):
            return False
        required = {"L0_ground.hm", "L1_relations.hm", "L2_operations.hm", "L3_ordinatics.hm",
                    "lean4/lean-toolchain", "lean4/lakefile.toml", "lean4/Audit.lean",
                    "lean4/Countermodels.lean", "lean4/Hypermath.lean",
                    "lean4/TraceChecks.lean", "lean4/Hypermath/Trace.lean",
                    "lean4/ObservationChecks.lean", "lean4/Hypermath/Observation.lean",
                    "lean4/FullAxiomModel.lean",
                    "lean4/Hypermath/FiniteAction.lean",
                    "lean4/FiniteActionCountermodel.lean",
                    "lean4/Hypermath/L0Ground.lean", "lean4/Hypermath/L1Relations.lean",
                    "lean4/Hypermath/L2Operations.lean",
                    "lean4/Hypermath/L3Ordinatics.lean",
                    "runner/hypermath_foundations/audit.py", "runner/hypermath_foundations/gate.py",
                    "runner/hypermath_foundations/_reports.py",
                    "runner/hypermath_foundations/_baseline.py",
                    "runner/hypermath_foundations/_inventory.py"}
        if not required <= before.keys():
            return False
        for path, checksum in before.items():
            if (not isinstance(path, str) or "\\" in path or ":" in path
                    or PurePosixPath(path).is_absolute() or ".." in PurePosixPath(path).parts
                    or not re.fullmatch(r"[0-9a-f]{64}", checksum)):
                return False
        toolchain = report["toolchain"]
        pinned = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-[\w.]+)?)",
                              toolchain["requested"])
        observed = re.search(r"Lean\s+\(version\s+([^,\s)]+)", toolchain["observed"])
        if not pinned or not observed or pinned.group(1) != observed.group(1):
            return False
        if report["runner"] != {"name": "hypermath-foundations", "version": "0.1.0"}:
            return False
        checks = report["checks"]
        if (checks["proof_admissibility"]["status"] != "PASS"
                or checks["proof_admissibility"]["attempted"] is not True
                or checks["assumption_policy"]["status"] != "PASS"
                or checks["assumption_policy"]["attempted"] is not True):
            return False
        for name in ("lean_build", "dependency_output", *PROBE_TARGETS):
            item = checks[name]
            if (item["status"] != "PASS" or item["attempted"] is not True
                    or type(item["exit_code"]) is not int or item["exit_code"] != 0
                    or not isinstance(item["output"], str) or not item["reasons"]):
                return False
        output = checks["dependency_output"]["output"]
        records = dependency_records(output, DEPENDENCY_TARGETS)
        if not target_is_theorem(output):
            return False
        declarations = kernel_declarations(output)
        if report["target"] != {"name": TARGET, "kind": "theorem",
                                "dependencies": records[TARGET], "statement": declarations[TARGET]}:
            return False
        if "sorryAx" in records[TARGET]:
            return False
        transitive = sorted(name for name, deps in records.items() if "sorryAx" in deps)
        if report["admissions"]["transitive_targets"] != transitive:
            return False
        source_admissions = report["admissions"]["source"]
        if not isinstance(source_admissions, list):
            return False
        for entry in source_admissions:
            if (entry["path"] not in before or type(entry["line"]) is not int
                    or entry["line"] < 1 or entry["token"] not in {"sorry", "admit", "sorryAx"}):
                return False
        assumptions = report["declared_assumptions"]
        if not isinstance(assumptions, list):
            return False
        if policy_errors(output, before, assumptions):
            return False
        names = set()
        for entry in assumptions:
            if (entry["name"] in names or entry["path"] not in before
                    or type(entry["line"]) is not int or entry["line"] < 1
                    or entry["kind"] not in {"source_parameter", "logical_axiom"}):
                return False
            names.add(entry["name"])
        if any(dep.startswith("Hypermath.") and dep not in names
               for dependencies in records.values() for dep in dependencies):
            return False
        for name, targets in PROBE_TARGETS.items():
            records = dependency_records(checks[name]["output"], targets)
            if not probe_dependencies_valid(name, records):
                return False
        claims = report["claims"]
        if (claims["self_derivation"]["status"] != "PASS"
                or not claims["self_derivation"]["reasons"]
                or claims["source_adequacy"]["status"] != "UNKNOWN"
                or claims["recursive_arithmetic_completeness"]["status"] != "UNKNOWN"):
            return False
        return True
    except (KeyError, TypeError, ValueError, AttributeError):
        return False
