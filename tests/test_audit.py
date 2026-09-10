"""Contract tests with bounded synthetic process observations, not Lean proofs."""

from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

import pytest

from hypermath_foundations import audit as audit_module
from hypermath_foundations import evaluate_gate, run_audit
from hypermath_foundations.__main__ import legacy_main, main
from hypermath_foundations._baseline import AXIOM_DECLARATIONS, TARGET_STATEMENT
from hypermath_foundations._inventory import lean_code
from hypermath_foundations._reports import (
    COUNTERMODEL_TARGETS,
    DEPENDENCY_TARGETS,
    REPOSITORY,
    TARGET,
)


def dependency_output(*, admitted=False, kind="theorem", missing=None):
    lines = []
    declarations = {**AXIOM_DECLARATIONS, TARGET: TARGET_STATEMENT + " := proofBody"}
    for name, declaration in declarations.items():
        if name == TARGET:
            declaration = declaration.replace("theorem ", kind + " ", 1)
        lines.extend([f"HYPERMATH_DECL_BEGIN:{name}", declaration, f"HYPERMATH_DECL_END:{name}"])
    for name in DEPENDENCY_TARGETS:
        if name == missing:
            continue
        deps = "sorryAx" if admitted and name == TARGET else "Hypermath.axGroundSelf"
        lines.append(f"'{name}' depends on axioms: [{deps}]")
    return "\n".join(lines)


def countermodel_output():
    return "\n".join(f"'{name}' does not depend on any axioms" for name in COUNTERMODEL_TARGETS)


@pytest.fixture
def checkout(tmp_path, monkeypatch):
    root = tmp_path / "checkout"
    project = Path(__file__).resolve().parents[1]
    files = {
        "L0_ground.hm": "ground", "L1_relations.hm": "relations",
        "L2_operations.hm": "operations", "L3_ordinatics.hm": "ordinal",
        "lean4/lean-toolchain": "leanprover/lean4:v4.14.0",
        "lean4/lakefile.toml": 'name = "Hypermath"', "lean4/Hypermath.lean": "import Hypermath",
        "lean4/Audit.lean": (project / "lean4/Audit.lean").read_text(encoding="utf-8"),
        "lean4/Countermodels.lean": (project / "lean4/Countermodels.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/L0Ground.lean": "-- fixture",
        "lean4/Hypermath/L1Relations.lean": "-- fixture",
        "lean4/Hypermath/L2Operations.lean": "-- fixture",
        "lean4/Hypermath/L3Ordinatics.lean": "namespace Hypermath\n" + "\n".join(
            f"axiom {name.removeprefix('Hypermath.')} : Prop" for name in AXIOM_DECLARATIONS),
    }
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.replace("\r\n", "\n").encode("utf-8"))
    subject = {"repository": REPOSITORY, "revision": "a" * 40, "dirty": False}
    monkeypatch.setattr(audit_module, "_subject", lambda _: copy.deepcopy(subject))
    monkeypatch.setattr(audit_module, "_find_lake", lambda _: "lake")

    def run(command, cwd, timeout, redact):
        assert 0 < timeout <= 300
        if command[-1] == "--version":
            return 0, "Lean (version 4.14.0, commit abc, Release)\n"
        if command[-1] == "Audit.lean":
            return 0, dependency_output()
        if command[-1] == "Countermodels.lean":
            return 0, countermodel_output()
        return 0, "Build completed successfully.\n"

    monkeypatch.setattr(audit_module, "_run_process", run)
    return root, subject, run


def test_fresh_success_preserves_relative_assumptions_and_unknown_bridges(checkout):
    root, _, _ = checkout
    report = run_audit(root)
    assert evaluate_gate(report)
    assert report["claims"]["self_derivation"]["status"] == "PASS"
    assert report["claims"]["source_adequacy"]["status"] == "UNKNOWN"
    assert not evaluate_gate(report, "recursive_arithmetic_completeness")
    assert len(report["declared_assumptions"]) == 69
    assert str(root) not in json.dumps(report)


@pytest.mark.parametrize("alter", [
    lambda out: out.replace(f"'{TARGET}' depends on axioms: [Hypermath.axGroundSelf]", ""),
    lambda out: out.replace(f"theorem {TARGET}", f"axiom {TARGET}"),
    lambda out: out + f"\n'{TARGET}' depends on axioms: [Hypermath.axGroundSelf]",
    lambda out: "",
])
def test_missing_or_malformed_target_is_not_pass(checkout, monkeypatch, alter):
    root, _, run = checkout
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (0, alter(dependency_output())) if cmd[-1] == "Audit.lean"
                        else run(cmd, *args))
    report = run_audit(root)
    assert report["claims"]["self_derivation"]["status"] == "UNKNOWN"
    assert report["checks"]["dependency_output"]["status"] == "FAIL"
    assert not evaluate_gate(report)


def test_admitted_target_keeps_build_success_separate(checkout, monkeypatch):
    root, _, run = checkout
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (0, dependency_output(admitted=True)) if cmd[-1] == "Audit.lean"
                        else run(cmd, *args))
    report = run_audit(root)
    assert report["execution"]["completed"] is True
    assert report["checks"]["lean_build"]["status"] == "PASS"
    assert report["claims"]["self_derivation"]["status"] == "UNKNOWN"
    assert report["checks"]["proof_admissibility"]["status"] == "FAIL"
    assert not evaluate_gate(report)
    report["claims"]["self_derivation"]["status"] = "PASS"
    report["target"]["dependencies"] = []
    assert not evaluate_gate(report)


@pytest.mark.parametrize("mutation", [
    lambda r: r["inputs"]["after"].update({"L0_ground.hm": "0" * 64}),
    lambda r: r["inputs"].update(sha256="0" * 64),
    lambda r: r["subject_after"].update(revision="b" * 40),
    lambda r: r["checks"]["lean_build"].update(exit_code=1),
    lambda r: r["checks"]["countermodel"].update(output=""),
    lambda r: r["execution"].update(mode="inventory"),
    lambda r: r.update(declared_assumptions=[]),
    lambda r: r["claims"]["source_adequacy"].update(status="PASS"),
    lambda r: r["toolchain"].update(observed="Lean (version 4.15.0, Release)"),
])
def test_inconsistent_pass_reports_are_rejected(checkout, mutation):
    report = run_audit(checkout[0])
    mutation(report)
    assert not evaluate_gate(report)


@pytest.mark.parametrize("value", [None, {}, {"format": "hypermath-audit-1"}, [], "PASS"])
def test_malformed_gate_fails_closed(value):
    assert not evaluate_gate(value)


def test_dirty_bytes_are_auditable_but_default_consumption_requires_clean(checkout):
    root, subject, _ = checkout
    subject["dirty"] = True
    report = run_audit(root)
    assert report["claims"]["self_derivation"]["status"] == "PASS"
    assert not evaluate_gate(report)
    assert evaluate_gate(report, require_clean=False)


def test_mutation_during_process_invalidates_evidence(checkout, monkeypatch):
    root, _, run = checkout

    def changing_run(cmd, *args):
        if cmd[-1] == "Countermodels.lean":
            (root / "L0_ground.hm").write_text("changed", encoding="utf-8")
        return run(cmd, *args)

    monkeypatch.setattr(audit_module, "_run_process", changing_run)
    report = run_audit(root)
    assert not report["inputs"]["stable"]
    assert report["claims"]["self_derivation"]["status"] == "UNKNOWN"
    assert not evaluate_gate(report)


def test_inventory_never_passes_proof_gate(checkout, monkeypatch):
    root, _, _ = checkout
    monkeypatch.setattr(audit_module, "_run_process", lambda *a: pytest.fail("Lean ran"))
    report = run_audit(root, inventory_only=True)
    assert report["execution"]["completed"]
    assert all(c["status"] == "UNKNOWN" and not c["attempted"]
               for c in report["checks"].values())
    assert not evaluate_gate(report)


def test_missing_tool_is_unknown(checkout, monkeypatch):
    def missing(_):
        raise FileNotFoundError("lake unavailable")

    monkeypatch.setattr(audit_module, "_find_lake", missing)
    report = run_audit(checkout[0])
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


def test_timeout_invalidates_run(checkout, monkeypatch):
    root, _, run = checkout
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (124, "partial output") if cmd[-1] == "build" else run(cmd, *args))
    report = run_audit(root, timeout=0.1)
    assert report["checks"]["lean_build"]["exit_code"] == 124
    assert report["claims"]["self_derivation"]["status"] == "UNKNOWN"
    assert not evaluate_gate(report)


def test_real_subprocess_timeout_is_bounded(tmp_path):
    code, _ = audit_module._run_process(
        [sys.executable, "-u", "-c", "import time; print('entered', flush=True); time.sleep(5)"],
        tmp_path, 0.2, lambda text: text,
    )
    assert code == 124


def test_nested_comments_and_strings_are_not_admissions():
    code = lean_code('/- sorry /- admit -/ -/\n-- sorryAx\ndef s := "sorry"\ntheorem x := by sorry')
    assert code.count("sorry") == 1


def test_redaction_preserves_relative_evidence(tmp_path):
    redact = audit_module._redactor(tmp_path)
    assert str(tmp_path) not in redact(f"{tmp_path}/lean4/Audit.lean")
    assert "Z:" not in redact("error at Z:\\private\\source.lean:12")
    assert redact("Hypermath/L0Ground.lean:12") == "Hypermath/L0Ground.lean:12"


def test_cli_software_completion_and_strict_gates(checkout, capsys):
    root = str(checkout[0])
    argv = ["audit", "--root", root, "--output", "report.json"]
    assert main([*argv, "--inventory-only"]) == 0
    assert main([*argv, "--require-complete"]) == 2
    assert main([*argv, "--require-self-derivation"]) == 0
    assert main(["audit", "--root", root, "--output", "../escape.json"]) == 1
    capsys.readouterr()


@pytest.mark.parametrize("code", [1, 124])
def test_legacy_tool_failure_precedes_remaining_admissions(checkout, monkeypatch, code):
    root, _, run = checkout
    path = root / "lean4/Hypermath/L3Ordinatics.lean"
    with path.open("a", encoding="utf-8") as file:
        file.write("\ntheorem admitted : True := by sorry\n")
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (code, "failed") if cmd[-1] == "build" else run(cmd, *args))
    assert legacy_main(root, ["--output", "legacy.json"]) == code


@pytest.mark.parametrize("alter", [
    lambda out: out.replace(TARGET_STATEMENT, f"theorem {TARGET} : True"),
    lambda out: out.replace(AXIOM_DECLARATIONS["Hypermath.axGroundSelf"],
                           "axiom Hypermath.axGroundSelf : False"),
    lambda out: out.replace("depends on axioms: [Hypermath.axGroundSelf]",
                           "depends on axioms: [Foreign.hiddenOracle]"),
])
def test_changed_statement_or_unreviewed_assumption_is_unknown(checkout, monkeypatch, alter):
    root, _, run = checkout
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (0, alter(dependency_output())) if cmd[-1] == "Audit.lean"
                        else run(cmd, *args))
    report = run_audit(root)
    assert report["execution"]["completed"]
    assert report["checks"]["assumption_policy"]["status"] == "FAIL"
    assert report["claims"]["self_derivation"]["status"] == "UNKNOWN"
    report["claims"]["self_derivation"]["status"] = "PASS"
    report["checks"]["assumption_policy"]["status"] = "PASS"
    report["checks"]["proof_admissibility"]["status"] = "PASS"
    assert not evaluate_gate(report)


def test_replaced_reporter_cannot_authorize_its_own_output(checkout):
    root, _, _ = checkout
    (root / "lean4/Audit.lean").write_text('#eval IO.println "forged report"', encoding="utf-8")
    report = run_audit(root)
    assert report["checks"]["assumption_policy"]["status"] == "FAIL"
    assert not evaluate_gate(report)


def test_timeout_validation(checkout):
    for timeout in (0, -1, 301, True, float("nan")):
        with pytest.raises(ValueError):
            run_audit(checkout[0], timeout=timeout)
