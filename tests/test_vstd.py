"""Exercise native Verifier Standard (VSTD) objects from its released wheel."""

from __future__ import annotations

import copy
import hashlib
import importlib.metadata
import json
import re
import subprocess
import sys
from pathlib import Path

import pytest
import verifier

import hypermath_foundations
from hypermath_foundations.vstd import (
    _AuditMechanism,
    _portable,
    evaluate_audit_report,
    write_verification_receipt,
)


@pytest.fixture
def report():
    """Synthetic unresolved audit; this fixture never establishes a theorem."""
    inventory = {"L0_ground.hm": hashlib.sha256(b"source fixture").hexdigest()}
    return {
        "format": "hypermath-audit-1",
        "runner": {"name": "hypermath-foundations", "version": "0.1.0"},
        "subject": {
            "repository": "https://github.com/TimeLordRaps/hypermath.git",
            "revision": "1" * 40,
            "dirty": False,
        },
        "toolchain": {"requested": "leanprover/lean4:v4.28.0", "observed": "fixture", "python": "fixture"},
        "execution": {"mode": "lean", "completed": True},
        "inputs": {"before": inventory, "after": dict(inventory), "stable": True,
                   "sha256": hashlib.sha256(b"fixture inventory").hexdigest()},
        "checks": {name: {"status": "UNKNOWN" if name == "proof_admissibility" else "PASS",
                          "attempted": name != "proof_admissibility",
                          "exit_code": None if name == "proof_admissibility" else 0,
                          "output": "", "reasons": ["fixture"]}
                   for name in ("lean_build", "dependency_output", "countermodel", "finite_trace",
                                "observation", "full_model", "finite_action",
                                "proof_admissibility")},
        "target": {"name": "Hypermath.selfDerivation", "kind": "theorem", "dependencies": ["sorryAx"]},
        "admissions": {"source": [{"path": "L0_ground.hm", "line": 1, "token": "sorry"}],
                       "transitive_targets": ["sorryAx"]},
        "declared_assumptions": [{"name": "sourceParameter", "path": "L0_ground.hm", "line": 2,
                                  "kind": "source_parameter"}],
        "claims": {name: {"status": "UNKNOWN", "reasons": ["proof obligation remains"]}
                   for name in ("self_derivation", "source_adequacy", "recursive_arithmetic_completeness")},
    }


def outcomes(result):
    return {key: record["evaluation"]["outcome"] for key, record in result["results"].items()}


def test_real_released_verifier_wheel_is_used():
    assert verifier.__version__ == "1.3.0"
    distribution = importlib.metadata.distribution("verifier-standard")
    assert distribution.version == "1.3.0"
    assert distribution.read_text("direct_url.json") is None


def test_core_adapter_import_does_not_require_optional_dependency():
    module_path = Path(__file__).parents[1] / "src" / "hypermath_foundations" / "vstd.py"
    code = (
        "import importlib.util, sys; "
        "spec=importlib.util.spec_from_file_location('standalone_vstd', sys.argv[1]); "
        "module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); "
        "assert 'verifier' not in sys.modules; print('optional import remains lazy')"
    )
    completed = subprocess.run([sys.executable, "-S", "-c", code, str(module_path)], timeout=15)
    assert completed.returncode == 0


def test_input_pass_cannot_replace_native_replay(report):
    for claim in report["claims"].values():
        claim["status"] = "PASS"
    result = evaluate_audit_report(report)
    assert set(outcomes(result).values()) == {"UNKNOWN"}
    assert result["conformance"] == "NOT_ESTABLISHED"
    for item in result["results"].values():
        proposition = verifier.BoundProposition.from_dict(item["proposition"])
        assert proposition.mechanism_id == "hypermath-foundations/audit-replay-2"
        assert proposition.digest() == item["evaluation"]["binding_digest"]
        assert proposition.expected is True
    store = verifier.EvidenceStore()
    store.import_base64(result["evidence"])
    assert json.loads(store.resolve(result["audit_sha256"])) == report


def test_real_session_reruns_registered_mechanism_once(report, monkeypatch, tmp_path):
    calls = []
    report["checks"]["proof_admissibility"].update(
        status="FAIL", attempted=True, reasons=["sorryAx occurs in target dependencies"]
    )

    def replay(root, timeout):
        calls.append((root, timeout))
        return copy.deepcopy(report)

    monkeypatch.setattr(hypermath_foundations, "run_audit", replay)
    result = evaluate_audit_report(report, foundation_root=tmp_path, timeout=11)
    assert calls == [(tmp_path, 11)]
    assert outcomes(result) == {
        "self_derivation": "UNKNOWN", "source_adequacy": "UNKNOWN",
        "recursive_arithmetic_completeness": "UNKNOWN", "audit_replay_matches": "PASS",
    }
    assert result["results"]["self_derivation"]["evaluation"]["observations"]["declared_assumptions"]
    assert result["results"]["self_derivation"]["evaluation"]["observations"]["proof_admissibility"]["status"] == "FAIL"


@pytest.mark.parametrize("mutation", ["revision", "dirty", "inputs", "target", "toolchain"])
def test_wrong_foundation_coordinate_never_supports_derivation(report, monkeypatch, tmp_path, mutation):
    replay = copy.deepcopy(report)
    if mutation == "revision":
        replay["subject"]["revision"] = "2" * 40
    elif mutation == "dirty":
        replay["subject"]["dirty"] = True
    elif mutation == "inputs":
        replay["inputs"]["after"]["L0_ground.hm"] = "f" * 64
    elif mutation == "target":
        replay["target"]["name"] = "Hypermath.otherTheorem"
    else:
        replay["toolchain"]["observed"] = "different Lean"
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: replay)
    result = evaluate_audit_report(report, foundation_root=tmp_path)
    assert outcomes(result)["self_derivation"] == "UNKNOWN"
    assert outcomes(result)["audit_replay_matches"] == "FAIL"


@pytest.mark.parametrize(
    ("field", "mutate"),
    [
        (
            "checks",
            lambda replay: replay["checks"]["dependency_output"].__setitem__(
                "output", "changed dependency evidence"
            ),
        ),
        (
            "checks",
            lambda replay: replay["checks"]["finite_action"].__setitem__(
                "output", "changed finite-action evidence"
            ),
        ),
        (
            "claims",
            lambda replay: replay["claims"]["self_derivation"].__setitem__(
                "reasons", ["changed claim basis"]
            ),
        ),
        (
            "claims",
            lambda replay: replay["claims"]["source_adequacy"].__setitem__("status", "FAIL"),
        ),
        (
            "admissions",
            lambda replay: replay["admissions"].__setitem__("transitive_targets", []),
        ),
        (
            "runner",
            lambda replay: replay["runner"].__setitem__("version", "different-runner"),
        ),
        (
            "subject_after",
            lambda replay: replay["subject_after"].__setitem__("revision", "2" * 40),
        ),
        (
            "execution",
            lambda replay: replay["execution"].__setitem__("worker", "unexpected-worker"),
        ),
        (
            "toolchain",
            lambda replay: replay["toolchain"].__setitem__("python", "different-python"),
        ),
    ],
)
def test_semantic_report_difference_never_matches_replay(
    report, monkeypatch, tmp_path, field, mutate
):
    report["subject_after"] = copy.deepcopy(report["subject"])
    replay = copy.deepcopy(report)
    mutate(replay)
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: replay)
    result = evaluate_audit_report(report, foundation_root=tmp_path)
    evaluation = result["results"]["audit_replay_matches"]["evaluation"]
    assert evaluation["outcome"] == "FAIL"
    assert f"native replay differs at {field}" in evaluation["observations"]["binding_differences"]


def test_incremental_build_step_state_and_line_order_are_normalized(
    report, monkeypatch, tmp_path
):
    replay = copy.deepcopy(report)
    report["checks"]["lean_build"]["output"] = (
        "✔ [1/2] Built Hypermath.Core\n✔ [2/2] Built Hypermath.Action\n"
    )
    replay["checks"]["lean_build"]["output"] = (
        "✔ [2/2] Replayed Hypermath.Action\n✔ [1/2] Replayed Hypermath.Core\n"
    )
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: replay)
    result = evaluate_audit_report(report, foundation_root=tmp_path)
    assert outcomes(result)["audit_replay_matches"] == "PASS"


@pytest.mark.parametrize(
    "replay_output",
    [
        "✔ [1/2] Replayed Hypermath.Core\n✔ [2/2] Replayed Hypermath.Other\n",
        "✔ [1/2] Replayed Hypermath.Core\n",
        (
            "✔ [1/2] Replayed Hypermath.Core\n"
            "✔ [1/2] Replayed Hypermath.Core\n"
            "✔ [2/2] Replayed Hypermath.Action\n"
        ),
    ],
    ids=("changed-line", "removed-line", "duplicated-line"),
)
def test_incremental_build_line_content_and_multiplicity_remain_exact(
    report, monkeypatch, tmp_path, replay_output
):
    replay = copy.deepcopy(report)
    report["checks"]["lean_build"]["output"] = (
        "✔ [1/2] Built Hypermath.Core\n✔ [2/2] Built Hypermath.Action\n"
    )
    replay["checks"]["lean_build"]["output"] = replay_output
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: replay)
    result = evaluate_audit_report(report, foundation_root=tmp_path)
    assert outcomes(result)["audit_replay_matches"] == "FAIL"


def test_replayed_pass_requires_native_gate_acceptance(report, monkeypatch, tmp_path):
    report["claims"]["self_derivation"]["status"] = "PASS"
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: copy.deepcopy(report))
    monkeypatch.setattr(hypermath_foundations, "evaluate_gate", lambda *_args, **_kwargs: False)
    assert outcomes(evaluate_audit_report(report, foundation_root=tmp_path))["self_derivation"] == "UNKNOWN"


@pytest.mark.parametrize("coordinate", ["subject", "revision", "trust_roots"])
def test_mechanism_does_not_accept_wrong_coordinate(report, coordinate):
    result = evaluate_audit_report(report)
    item = result["results"]["self_derivation"]
    tampered = copy.deepcopy(item["proposition"])
    if coordinate == "subject":
        tampered["subject_id"] = "different-audit"
    elif coordinate == "revision":
        tampered["parameters"]["revision"] = "0" * 40
    else:
        tampered["trust_roots"] = ["unestablished independent authority"]
    store = verifier.EvidenceStore()
    store.import_base64(result["evidence"])
    session = verifier.VerificationSession(store)
    session.register(_AuditMechanism(None, 60))
    evaluation = session.evaluate(verifier.BoundProposition.from_dict(tampered))
    assert evaluation.outcome is verifier.MechanismOutcome.FAIL


def test_real_wheel_receipt_validation_and_tamper_refusal(report, tmp_path):
    output = tmp_path / "evidence"
    receipt_path = write_verification_receipt(report, output)
    assert verifier.validate_run_receipt(receipt_path) == 0
    receipt = json.loads(receipt_path.read_bytes())
    assert receipt["schema_version"] == "VSTD-1"
    assert receipt["receipt_kind"] == "generic_computational_run"
    assert receipt["source_state"]["local_repository_path"] == "."
    assert {entry["path"] for entry in receipt["inputs"]} == {
        "audit.json", "session.json", "package_evidence.py",
    }
    native = json.loads((output / "verification.json").read_bytes())
    assert set(outcomes(native).values()) == {"UNKNOWN"}
    assert receipt["claims"]["execution_completed"] is True
    for path in output.rglob("*"):
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            assert str(tmp_path) not in text
            assert not re.search(r"(?<![A-Za-z0-9])[A-Za-z]:[\\/]", text), path.name
            assert not re.search(r"/(?:Users|home|mnt|Volumes|tmp|var|opt|usr|workspace)/", text), path.name
    receipt["claim_statement"] = "All arithmetic was proved."
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
    assert verifier.validate_run_receipt(receipt_path) != 0


def test_existing_receipt_directory_is_preserved(report, tmp_path):
    marker = tmp_path / "keep.txt"
    marker.write_text("user evidence", encoding="utf-8")
    with pytest.raises(FileExistsError):
        write_verification_receipt(report, tmp_path)
    assert marker.read_text(encoding="utf-8") == "user evidence"


def test_malformed_report_does_not_emit_receipt(report, tmp_path):
    report["inputs"]["before"] = {"../outside.hm": "0" * 64}
    with pytest.raises(ValueError, match="repository-relative"):
        write_verification_receipt(report, tmp_path / "receipt")
    assert not (tmp_path / "receipt").exists()


def test_machine_paths_rejected_before_publication(report):
    report["checks"]["lean_build"]["output"] = "Z" + ":/workstation/private/source.lean"
    with pytest.raises(ValueError, match="machine-specific"):
        evaluate_audit_report(report)


def test_json_escaped_relative_windows_trace_preserves_evidence_bytes(report, tmp_path):
    report["checks"]["lean_build"]["output"] = (
        "trace: .> LEAN_PATH=.\\.lake\\build\\lib PATH "
        "<home>\\.elan\\toolchains\\leanprover--lean4---v4.14.0\\bin\\lean.exe "
        ".\\Hypermath\\L0Ground.lean\n"
    )
    receipt_path = write_verification_receipt(report, tmp_path / "bundle")
    assert verifier.validate_run_receipt(receipt_path) == 0
    receipt = json.loads(receipt_path.read_bytes())
    evidence_bytes = (receipt_path.parent / "audit.json").read_bytes()
    assert json.loads(evidence_bytes) == report
    input_ref = next(item for item in receipt["inputs"] if item["path"] == "audit.json")
    assert hashlib.sha256(evidence_bytes).hexdigest() == input_ref["sha256"]


@pytest.mark.parametrize("path", [
    "\\\\" + "host" + "\\share\\source.lean",
    "\\\\" + "host",
    "\\\\" + "?\\UNC\\host\\share\\source.lean",
    "file:" + "///source.lean",
    "/" + "tmp/private/source.lean",
    "Z" + ":\\source.lean",
])
def test_real_machine_paths_remain_rejected_inside_json_values(report, path):
    report["checks"]["lean_build"]["output"] = "compiler: " + path
    with pytest.raises(ValueError, match="machine-specific"):
        evaluate_audit_report(report)


def test_escaped_relative_separators_in_plain_text_are_not_unc_paths():
    _portable("trace: build" + "\\\\" + "lib" + "\\\\" + "Core.lean")


def test_redacted_linux_trace_preserves_evidence_bytes(report, tmp_path):
    report["checks"]["lean_build"]["output"] = (
        "trace: LD_LIBRARY_PATH=<python>/lib "
        "<runtime>/toolchains/leanprover--lean4---v4.14.0/bin/lean "
        "./Hypermath/L0Ground.lean -o ./.lake/build/lib/Hypermath/L0Ground.olean\n"
    )
    receipt_path = write_verification_receipt(report, tmp_path / "bundle")
    assert verifier.validate_run_receipt(receipt_path) == 0
    assert json.loads((receipt_path.parent / "audit.json").read_bytes()) == report


@pytest.mark.parametrize("path", ["/" + "bin/lean", "/" + "home/user/source.lean"])
def test_absolute_linux_paths_remain_rejected(report, path):
    report["checks"]["lean_build"]["output"] = "compiler=" + path
    with pytest.raises(ValueError, match="machine-specific"):
        evaluate_audit_report(report)


@pytest.mark.parametrize("failure", ["coordinate", "unavailable", "downgraded_claim"])
def test_failed_required_replay_preserves_receipt_but_raises(report, monkeypatch, tmp_path, failure):
    replay = copy.deepcopy(report)
    if failure == "coordinate":
        replay["subject"]["revision"] = "2" * 40
    elif failure == "downgraded_claim":
        report["claims"]["self_derivation"]["status"] = "PASS"

    def run_replay(*_args, **_kwargs):
        if failure == "unavailable":
            raise TimeoutError("bounded replay did not complete")
        return replay

    monkeypatch.setattr(hypermath_foundations, "run_audit", run_replay)
    output = tmp_path / "bundle"
    with pytest.raises(RuntimeError, match="required native replay"):
        write_verification_receipt(report, output, foundation_root=tmp_path)
    assert verifier.validate_run_receipt(output / "receipt.json") == 0
    native = json.loads((output / "verification.json").read_bytes())
    assert outcomes(native)["self_derivation"] == "UNKNOWN"
    expected_match = {"coordinate": "FAIL", "unavailable": "UNKNOWN", "downgraded_claim": "FAIL"}
    assert outcomes(native)["audit_replay_matches"] == expected_match[failure]


def test_matching_unresolved_replay_remains_writable(report, monkeypatch, tmp_path):
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: copy.deepcopy(report))
    output = tmp_path / "bundle"
    receipt_path = write_verification_receipt(report, output, foundation_root=tmp_path)
    assert verifier.validate_run_receipt(receipt_path) == 0
    native = json.loads((output / "verification.json").read_bytes())
    assert outcomes(native)["self_derivation"] == "UNKNOWN"
    assert outcomes(native)["audit_replay_matches"] == "PASS"


@pytest.mark.parametrize("side", ["supplied", "replayed"])
@pytest.mark.parametrize("failure", ["countermodel", "finite_trace", "observation", "full_model",
                                     "finite_action", "inventory", "inconsistent_completion"])
def test_incomplete_lean_audit_never_matches_replay(report, monkeypatch, tmp_path, side, failure):
    replay = copy.deepcopy(report)
    candidate = report if side == "supplied" else replay
    if failure == "inventory":
        candidate["execution"] = {"mode": "inventory", "completed": True}
    else:
        name = failure if failure in {
            "finite_trace", "observation", "full_model", "finite_action",
        } else "countermodel"
        candidate["checks"][name].update(status="FAIL", attempted=True, exit_code=1)
        candidate["execution"]["completed"] = failure == "inconsistent_completion"
    assert candidate["target"]["kind"] == "theorem"
    assert candidate["claims"]["self_derivation"]["status"] == "UNKNOWN"
    monkeypatch.setattr(hypermath_foundations, "run_audit", lambda *_args, **_kwargs: replay)
    output = tmp_path / "bundle"
    with pytest.raises(RuntimeError, match="required native replay"):
        write_verification_receipt(report, output, foundation_root=tmp_path)
    assert verifier.validate_run_receipt(output / "receipt.json") == 0
    native = json.loads((output / "verification.json").read_bytes())
    assert outcomes(native)["audit_replay_matches"] == "FAIL"
    assert outcomes(native)["self_derivation"] == "UNKNOWN"
