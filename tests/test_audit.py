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
from hypermath_foundations._baseline import (
    AXIOM_DECLARATIONS,
    DEFINITION_DECLARATIONS,
    PROVED_DECLARATIONS,
    PROVED_DEPENDENCIES,
    TARGET_STATEMENT,
)
from hypermath_foundations._inventory import SOURCE_PARAMETERS, lean_code
from hypermath_foundations._reports import (
    ACTION_COUNTERMODEL_DEPENDENCIES,
    COUNTERMODEL_TARGETS,
    DEPENDENCY_TARGETS,
    FULL_MODEL_DEPENDENCIES,
    GROUND_DERIVATION_DEPENDENCIES,
    GROUND_SYNTAX_DEPENDENCIES,
    OBSERVATION_DEPENDENCIES,
    RECORD_ENCODING_DEPENDENCIES,
    REPOSITORY,
    TARGET,
    TRACE_CHECK_TARGETS,
)


def dependency_output(*, admitted=False, kind="theorem", missing=None):
    lines = []
    declarations = {**AXIOM_DECLARATIONS, **DEFINITION_DECLARATIONS,
                    **{name: value + " := proofBody" for name, value in PROVED_DECLARATIONS.items()},
                    TARGET: TARGET_STATEMENT + " := proofBody"}
    for name, declaration in declarations.items():
        if name == TARGET:
            declaration = declaration.replace("theorem ", kind + " ", 1)
        lines.extend([f"HYPERMATH_DECL_BEGIN:{name}", declaration, f"HYPERMATH_DECL_END:{name}"])
    for name in DEPENDENCY_TARGETS:
        if name == missing:
            continue
        deps = (", ".join(sorted(PROVED_DEPENDENCIES[name]))
                if name in PROVED_DECLARATIONS else "Hypermath.axGroundSelf")
        if admitted and name == TARGET:
            deps = "sorryAx"
        lines.append(f"'{name}' depends on axioms: [{deps}]")
    return "\n".join(lines)


def countermodel_output():
    return "\n".join(f"'{name}' does not depend on any axioms" for name in COUNTERMODEL_TARGETS)


def action_countermodel_output():
    lines = []
    for name, dependencies in ACTION_COUNTERMODEL_DEPENDENCIES.items():
        if dependencies:
            lines.append(f"'{name}' depends on axioms: [{', '.join(dependencies)}]")
        else:
            lines.append(f"'{name}' does not depend on any axioms")
    return "\n".join(lines)


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
        "lean4/TraceChecks.lean": (project / "lean4/TraceChecks.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/Trace.lean": (project / "lean4/Hypermath/Trace.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/Observation.lean": (project / "lean4/Hypermath/Observation.lean").read_text(encoding="utf-8"),
        "lean4/ObservationChecks.lean": (project / "lean4/ObservationChecks.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/GroundSyntax.lean": (
            project / "lean4/Hypermath/GroundSyntax.lean").read_text(encoding="utf-8"),
        "lean4/GroundSyntaxChecks.lean": (
            project / "lean4/GroundSyntaxChecks.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/GroundDerivation.lean": (
            project / "lean4/Hypermath/GroundDerivation.lean").read_text(encoding="utf-8"),
        "lean4/GroundDerivationChecks.lean": (
            project / "lean4/GroundDerivationChecks.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/GroundCode.lean": (
            project / "lean4/Hypermath/GroundCode.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/RecordEncoding.lean": (
            project / "lean4/Hypermath/RecordEncoding.lean").read_text(encoding="utf-8"),
        "lean4/RecordEncodingChecks.lean": (
            project / "lean4/RecordEncodingChecks.lean").read_text(encoding="utf-8"),
        "lean4/FullAxiomModel.lean": (project / "lean4/FullAxiomModel.lean").read_text(encoding="utf-8"),
        "lean4/Hypermath/FiniteAction.lean": (
            project / "lean4/Hypermath/FiniteAction.lean").read_text(encoding="utf-8"),
        "lean4/FiniteActionCountermodel.lean": (
            project / "lean4/FiniteActionCountermodel.lean").read_text(encoding="utf-8"),
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
        if command[-1] == "TraceChecks.lean":
            return 0, "\n".join(f"'{name}' does not depend on any axioms" for name in TRACE_CHECK_TARGETS)
        if command[-1] == "FiniteActionCountermodel.lean":
            return 0, action_countermodel_output()
        if command[-1] in {"GroundSyntaxChecks.lean", "GroundDerivationChecks.lean",
                           "RecordEncodingChecks.lean"}:
            expected = {"GroundSyntaxChecks.lean": GROUND_SYNTAX_DEPENDENCIES,
                        "GroundDerivationChecks.lean": GROUND_DERIVATION_DEPENDENCIES,
                        "RecordEncodingChecks.lean": RECORD_ENCODING_DEPENDENCIES}[command[-1]]
            return 0, "\n".join(
                f"'{name}' depends on axioms: [{', '.join(dependencies)}]"
                if dependencies else f"'{name}' does not depend on any axioms"
                for name, dependencies in expected.items()
            )
        for filename, expected in (("ObservationChecks.lean", OBSERVATION_DEPENDENCIES),
                                   ("FullAxiomModel.lean", FULL_MODEL_DEPENDENCIES)):
            if command[-1] == filename:
                return 0, "\n".join(
                    f"'{name}' depends on axioms: [{', '.join(dependencies)}]"
                    if dependencies
                    else f"'{name}' does not depend on any axioms"
                    for name, dependencies in expected.items()
                )
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
    assert len(report["declared_assumptions"]) == 67
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
    lambda r: r["checks"]["finite_trace"].update(output=""),
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


@pytest.mark.parametrize("flags", [[], ["--require-self-derivation"]])
def test_cli_rejects_completed_execution_with_changed_policy_source(checkout, flags):
    root = checkout[0]
    with (root / "lean4/Hypermath/GroundSyntax.lean").open("a", encoding="utf-8") as file:
        file.write("\n-- Byte policy no longer matches the reviewed source.\n")
    assert main(["audit", "--root", str(root), "--output", "report.json", *flags]) == 1
    report = json.loads((root / "report.json").read_text())
    assert report["execution"]["completed"] is True
    assert report["checks"]["assumption_policy"]["status"] == "FAIL"


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
    lambda out: out.replace(DEFINITION_DECLARATIONS["Hypermath.D"],
                           "def Hypermath.D : Hypermath.Form → Hypermath.Form → Prop := fun _ _ => True"),
    lambda out: out.replace(PROVED_DECLARATIONS["Hypermath.dEntryEndpointIteration"],
                           "theorem Hypermath.dEntryEndpointIteration : True"),
    lambda out: out.replace(DEFINITION_DECLARATIONS["Hypermath.finiteApplyFromGround"],
                           "def Hypermath.finiteApplyFromGround : Hypermath.Form → Prop := fun _ => True"),
    lambda out: out.replace(PROVED_DECLARATIONS["Hypermath.notGroundSpanningClaim"],
                           "theorem Hypermath.notGroundSpanningClaim : Hypermath.groundSpanningClaim"),
    lambda out: out.replace("'Hypermath.dIsReflexive' depends on axioms: [Hypermath.Congruent, Hypermath.Form, Hypermath.f2f]",
                           "'Hypermath.dIsReflexive' depends on axioms: [sorryAx, Hypermath.Form]"),
    lambda out: out.replace("'Hypermath.dIsReflexive' depends on axioms: [Hypermath.Congruent, Hypermath.Form, Hypermath.f2f]",
                           "'Hypermath.dIsReflexive' depends on axioms: [Hypermath.axGroundSelf]"),
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


@pytest.mark.parametrize("name,deps", [
    ("Hypermath.finiteApplyGround", "Hypermath.Form, Hypermath.f2f, Hypermath.ground, Hypermath.axLimitNotFinite"),
    ("Hypermath.notGroundSpanningClaim", "Hypermath.Form"),
])
def test_milestone_dependencies_cannot_gain_or_hide_assumptions(checkout, monkeypatch, name, deps):
    root, _, run = checkout
    expected = ", ".join(sorted(PROVED_DEPENDENCIES[name]))
    output = dependency_output().replace(f"'{name}' depends on axioms: [{expected}]",
                                         f"'{name}' depends on axioms: [{deps}]")
    monkeypatch.setattr(audit_module, "_run_process", lambda cmd, *args:
                        (0, output) if cmd[-1] == "Audit.lean" else run(cmd, *args))
    report = run_audit(root)
    assert report["checks"]["assumption_policy"]["status"] == "FAIL"
    assert not evaluate_gate(report)


@pytest.mark.parametrize("process,filename", [("finite_trace", "TraceChecks.lean"),
                                             ("observation", "ObservationChecks.lean")])
@pytest.mark.parametrize("dependency", ["sorryAx", "Foreign.oracle", "propext"])
def test_constructive_trace_probes_require_no_axioms(checkout, monkeypatch, dependency, process, filename):
    root, _, run = checkout

    def altered(cmd, *args):
        code, output = run(cmd, *args)
        if cmd[-1] == filename:
            output = output.replace("does not depend on any axioms",
                                    f"depends on axioms: [{dependency}]", 1)
        return code, output

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"][process]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


@pytest.mark.parametrize("name,replacement", [
    ("Hypermath.Observation.chosenDecoder_correct", "does not depend on any axioms"),
    ("Hypermath.Observation.compatible_iff_decoder", "depends on axioms: [propext]"),
    ("Hypermath.Observation.reuse_preserves_observations", "depends on axioms: [Classical.choice]"),
    ("Hypermath.Observation.equality_queries_iff_injective", "depends on axioms: [sorryAx]"),
])
def test_reification_dependency_policy_is_exact(checkout, monkeypatch, name, replacement):
    root, _, run = checkout

    def altered(cmd, *args):
        code, output = run(cmd, *args)
        if cmd[-1] == "ObservationChecks.lean":
            output = "\n".join(
                f"'{name}' {replacement}" if line.startswith(f"'{name}' ") else line
                for line in output.splitlines()
            )
        return code, output

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"]["observation"]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


@pytest.mark.parametrize("path", ["lean4/Audit.lean", "lean4/Hypermath/Trace.lean", "lean4/TraceChecks.lean",
                                  "lean4/Hypermath/Observation.lean", "lean4/ObservationChecks.lean",
                                  "lean4/FullAxiomModel.lean", "lean4/Hypermath/FiniteAction.lean",
                                  "lean4/FiniteActionCountermodel.lean",
                                  "lean4/Hypermath/GroundSyntax.lean", "lean4/GroundSyntaxChecks.lean",
                                  "lean4/Hypermath/GroundDerivation.lean",
                                  "lean4/GroundDerivationChecks.lean",
                                  "lean4/Hypermath/GroundCode.lean",
                                  "lean4/Hypermath/RecordEncoding.lean",
                                  "lean4/RecordEncodingChecks.lean"])
def test_replaced_reporter_or_trace_cannot_authorize_its_own_output(checkout, path):
    root, _, _ = checkout
    (root / path).write_text('#eval IO.println "forged report"', encoding="utf-8")
    report = run_audit(root)
    assert report["checks"]["assumption_policy"]["status"] == "FAIL"
    assert not evaluate_gate(report)


@pytest.mark.parametrize("alteration", ["missing", "hidden_source_rule", "admission", "failure"])
@pytest.mark.parametrize("fragment,reporter,namespace", [
    ("ground_syntax", "GroundSyntaxChecks.lean", "GroundSyntax"),
    ("ground_derivation", "GroundDerivationChecks.lean", "GroundDerivation"),
])
def test_ground_fragment_requires_exact_proof_dependencies(
    checkout, monkeypatch, alteration, fragment, reporter, namespace,
):
    root, _, run = checkout

    def altered(command, *args):
        code, output = run(command, *args)
        if command[-1] == reporter:
            if alteration == "missing":
                output = "\n".join(line for line in output.splitlines()
                                   if f"{namespace}.native_check_sound'" not in line)
            elif alteration == "hidden_source_rule":
                output = output.replace("Hypermath.axDiff, ", "")
            elif alteration == "admission":
                output = output.replace("does not depend on any axioms",
                                        "depends on axioms: [sorryAx]", 1)
            else:
                code = 1
        return code, output

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"][fragment]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


@pytest.mark.parametrize("alteration", ["missing", "hidden_choice", "admission", "failure"])
def test_record_encoding_requires_exact_proof_dependencies(checkout, monkeypatch, alteration):
    root, _, run = checkout

    def altered(command, *args):
        code, output = run(command, *args)
        if command[-1] == "RecordEncodingChecks.lean":
            if alteration == "missing":
                output = "\n".join(line for line in output.splitlines()
                                   if "RecordEncoding.checkNumbers_sound'" not in line)
            elif alteration == "hidden_choice":
                output = output.replace("Classical.choice, ", "")
            elif alteration == "admission":
                output = output.replace("does not depend on any axioms",
                                        "depends on axioms: [sorryAx]", 1)
            else:
                code = 1
        return code, output

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"]["record_encoding"]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


@pytest.mark.parametrize("alteration", ["missing", "hidden_choice", "extra_choice", "admission"])
def test_faithful_model_requires_exact_dependencies(checkout, monkeypatch, alteration):
    root, _, run = checkout

    def altered(command, *args):
        code, output = run(command, *args)
        if command[-1] == "FullAxiomModel.lean":
            if alteration == "missing":
                output = "\n".join(line for line in output.splitlines()
                                   if "FullAxiomModel.interpreted_record_recovered'" not in line)
            elif alteration == "hidden_choice":
                output = output.replace("Classical.choice, ", "")
            elif alteration == "extra_choice":
                output = output.replace("[propext]", "[Classical.choice, propext]", 1)
            else:
                output = output.replace("[propext]", "[propext, sorryAx]", 1)
        return code, output

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"]["full_model"]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)


def test_timeout_validation(checkout):
    for timeout in (0, -1, 301, True, float("nan")):
        with pytest.raises(ValueError):
            run_audit(checkout[0], timeout=timeout)


@pytest.mark.parametrize("relative_path", [
    "lean4/FullAxiomModel.lean",
    "lean4/FiniteActionCountermodel.lean",
])
def test_full_models_cover_exact_reviewed_logical_clause_types(relative_path):
    """The model must cover the actual axiom list, not a smaller lookalike."""
    import re

    path = Path(__file__).resolve().parents[1] / relative_path
    source = lean_code(path.read_text(encoding="utf-8"))
    fields = source.split("structure FullAxioms : Prop where\n", 1)[1].split("\ntheorem ", 1)[0]
    actual = dict(re.findall(r"^  (\w+) : (.+)$", fields, re.M))
    expected = {
        name.removeprefix("Hypermath."): declaration.split(" : ", 1)[1].replace("Hypermath.", "")
        for name, declaration in AXIOM_DECLARATIONS.items()
        if name.removeprefix("Hypermath.") not in SOURCE_PARAMETERS
    }
    assert len(actual) == len(expected) == 38
    assert actual == expected


@pytest.mark.parametrize("alter", [
    lambda out: out.replace(
        "depends on axioms: [Quot.sound, propext]",
        "depends on axioms: [propext]",
        1,
    ),
    lambda out: out.replace(
        "does not depend on any axioms",
        "depends on axioms: [Classical.choice]",
        1,
    ),
    lambda out: out.replace(
        "depends on axioms: [Quot.sound, propext]",
        "depends on axioms: [Quot.sound,, propext]",
        1,
    ),
    lambda out: out + "\n'HypermathFiniteActionCountermodel.full_axioms_hold' "
    "depends on axioms: [sorryAx",
])
def test_finite_action_model_requires_exact_dependency_surface(checkout, monkeypatch, alter):
    root, _, run = checkout

    def altered(command, *args):
        if command[-1] == "FiniteActionCountermodel.lean":
            return 0, alter(action_countermodel_output())
        return run(command, *args)

    monkeypatch.setattr(audit_module, "_run_process", altered)
    report = run_audit(root)
    assert report["checks"]["finite_action"]["status"] == "FAIL"
    assert not report["execution"]["completed"]
    assert not evaluate_gate(report)
