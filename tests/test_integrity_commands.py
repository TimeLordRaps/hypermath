"""Regression checks for policy failures and fresh Windows-style checkouts."""

import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from hypermath_foundations._baseline import (
    GROUND_CODE_SOURCE_SHA256,
    GROUND_DERIVATION_CHECKS_SOURCE_SHA256,
    GROUND_DERIVATION_SOURCE_SHA256,
    GROUND_SYNTAX_CHECKS_SOURCE_SHA256,
    GROUND_SYNTAX_SOURCE_SHA256,
    RECORD_ENCODING_CHECKS_SOURCE_SHA256,
    RECORD_ENCODING_SOURCE_SHA256,
    RECORD_MACHINE_CHECKS_SOURCE_SHA256,
    RECORD_MACHINE_SOURCE_SHA256,
)

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("policy,strict,expected", [
    ({"status": "FAIL", "attempted": True}, False, 1),
    ({"status": "UNKNOWN", "attempted": True}, False, 1),
    (None, False, 1),
    ({"status": "PASS", "attempted": False}, False, 1),
    ({"status": "PASS", "attempted": True}, False, 0),
    ({"status": "PASS", "attempted": True}, True, 2),
])
def test_integrity_command_distinguishes_policy_from_proof(
    tmp_path, monkeypatch, policy, strict, expected,
):
    spec = importlib.util.spec_from_file_location(
        "foundation_integrity_command", ROOT / "scripts/check_foundation.py",
    )
    command = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(command)
    # Execution completion and replay agreement can coexist with a policy failure.
    # This isolates command exit behavior; it supplies no mathematical evidence.
    report = {
        "toolchain": {"exit_code": 0},
        "execution": {"completed": True},
        "checks": {"proof_admissibility": {"status": "FAIL", "exit_code": None}},
        "claims": {"self_derivation": {"status": "UNKNOWN"}},
    }
    if policy is not None:
        report["checks"]["assumption_policy"] = policy
    retained = []
    monkeypatch.setattr(command, "run_audit", lambda *a, **k: report)
    monkeypatch.setattr(command, "write_verification_receipt",
                        lambda received, *a, **k: retained.append(received))
    output = tmp_path / "evidence"
    argv = ["check_foundation", "--output", str(output)]
    if strict:
        argv.append("--require-complete")
    monkeypatch.setattr(sys, "argv", argv)
    assert command.main() == expected
    assert json.loads((output / "audit.json").read_text()) == report
    assert retained == [report]


def test_fresh_autocrlf_checkout_preserves_primitive_checker_policy_bytes(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    shutil.copyfile(ROOT / ".gitattributes", source / ".gitattributes")
    expected = {
        "lean4/Hypermath/GroundSyntax.lean": GROUND_SYNTAX_SOURCE_SHA256,
        "lean4/GroundSyntaxChecks.lean": GROUND_SYNTAX_CHECKS_SOURCE_SHA256,
        "lean4/Hypermath/GroundDerivation.lean": GROUND_DERIVATION_SOURCE_SHA256,
        "lean4/GroundDerivationChecks.lean": GROUND_DERIVATION_CHECKS_SOURCE_SHA256,
        "lean4/Hypermath/GroundCode.lean": GROUND_CODE_SOURCE_SHA256,
        "lean4/Hypermath/RecordEncoding.lean": RECORD_ENCODING_SOURCE_SHA256,
        "lean4/RecordEncodingChecks.lean": RECORD_ENCODING_CHECKS_SOURCE_SHA256,
        "lean4/Hypermath/RecordMachine.lean": RECORD_MACHINE_SOURCE_SHA256,
        "lean4/RecordMachineChecks.lean": RECORD_MACHINE_CHECKS_SOURCE_SHA256,
    }
    for relative in expected:
        destination = source / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / relative).read_bytes())

    def git(*args):
        subprocess.run(["git", *args], check=True, capture_output=True, timeout=15)

    git("-C", str(source), "init")
    git("-C", str(source), "add", ".")
    git("-C", str(source), "-c", "user.name=Fixture", "-c",
        "user.email=fixture@example.invalid", "commit", "-m", "Portable source fixture")
    destination = tmp_path / "fresh"
    git("clone", "--no-local", "--config", "core.autocrlf=true", str(source), str(destination))
    for relative, digest in expected.items():
        assert hashlib.sha256((destination / relative).read_bytes()).hexdigest() == digest
