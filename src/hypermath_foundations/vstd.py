"""Verifier Standard (VSTD) bindings for bounded Hypermath audit evidence.

The optional ``verification`` extra supplies the real verifier-standard 1.3.0
objects. A native session can replay a clean, pinned foundation checkout. Its
``self_derivation`` predicate means conditional Lean proof admissibility under
the report's declared assumptions, not source adequacy or complete arithmetic.
Without a checkout, mathematical propositions remain UNKNOWN.

The generated VSTD-1 generic-run receipt records evidence packaging. Session
records are domain artifacts inside that receipt, not VSTD-4 conformance claims.
"""

from __future__ import annotations

import hashlib
import importlib
import json
import re
from dataclasses import replace
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

__all__ = ["evaluate_audit_report", "write_verification_receipt"]

_VERSION = "1.3.0"
_REPOSITORY = "https://github.com/TimeLordRaps/hypermath.git"
_CLAIMS = ("self_derivation", "source_adequacy", "recursive_arithmetic_completeness")
_MAX_BYTES = 8 * 1024 * 1024
_TRUST_ROOTS = (
    "verifier-standard==1.3.0 evidence dispatch",
    "Hypermath audit implementation and the report's named Lean toolchain",
    "Explicit source parameters and logical axioms carried in audit evidence",
)
_MACHINE_PATH = re.compile(
    r"(?<![A-Za-z0-9])[A-Za-z]:[\\/]|file://|"
    r"(?<![\w.\\])\\\\(?:[?.]\\|[A-Za-z0-9][\w.-]*(?:\\|(?=$|[\s\"'<>])))|"
    r"(?<![\w./>\\-])/(?:Users|home|mnt|Volumes|tmp|var|opt|private|root|workspace|workspaces|"
    r"usr|etc|bin|sbin|run|media)/"
)


def _verifier() -> Any:
    try:
        module = importlib.import_module("verifier")
    except ImportError as exc:
        raise ImportError(
            "VSTD support requires hypermath-foundations[verification] "
            "with verifier-standard==1.3.0"
        ) from exc
    if module.__version__ != _VERSION:
        raise ImportError("VSTD support requires verifier-standard==1.3.0 exactly")
    return module


def _bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False
    ).encode("utf-8")


def _digest(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _portable(value: Any) -> None:
    if isinstance(value, str):
        without_urls = re.sub(r"https?://[^\s\"<>]+", "", value)
        if _MACHINE_PATH.search(without_urls):
            raise ValueError("audit evidence contains a machine-specific filesystem path")
    elif isinstance(value, dict):
        for key, item in value.items():
            _portable(key)
            _portable(item)
    elif isinstance(value, (list, tuple)):
        for item in value:
            _portable(item)


def _report_bytes(report: Mapping[str, Any]) -> bytes:
    """Reject unsuitable input before issuing any evidence objects or files."""
    if not isinstance(report, Mapping) or report.get("format") != "hypermath-audit-1":
        raise ValueError("expected a hypermath-audit-1 report")
    for field in ("subject", "inputs", "checks", "toolchain", "target", "claims"):
        if not isinstance(report.get(field), dict):
            raise ValueError(f"audit report requires object field {field}")
    if not isinstance(report.get("declared_assumptions"), list):
        raise ValueError("audit report requires declared_assumptions")
    for name in _CLAIMS:
        claim = report["claims"].get(name)
        if not isinstance(claim, dict) or claim.get("status") not in {"PASS", "FAIL", "UNKNOWN"}:
            raise ValueError(f"audit report has no supported status for {name}")
    for phase in ("before", "after"):
        inventory = report["inputs"].get(phase)
        if not isinstance(inventory, dict):
            raise ValueError(f"audit report requires inputs.{phase}")
        for name, digest in inventory.items():
            path = PurePosixPath(name)
            if path.is_absolute() or ".." in path.parts or "\\" in name or ":" in name:
                raise ValueError("audit input locators must be repository-relative")
            if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
                raise ValueError("audit input digest must be a SHA-256 hexadecimal digest")
    _portable(dict(report))
    payload = _bytes(dict(report))
    if len(payload) > _MAX_BYTES:
        raise ValueError("audit report exceeds the 8 MiB evidence bound")
    return payload


def _parameters(report: Mapping[str, Any]) -> dict[str, str]:
    return {
        "repository": str(report["subject"].get("repository", "")),
        "revision": str(report["subject"].get("revision", "")),
        "target": str(report["target"].get("name", "")),
    }


class _AuditMechanism:
    mechanism_id = "hypermath-foundations/audit-replay-1"

    def __init__(self, foundation_root: Path | None, timeout: int) -> None:
        self.root = foundation_root
        self.timeout = timeout
        self.replay: dict[str, Any] | None = None
        self.replay_error: str | None = None
        self.prepared = False
        # Bind every Python source file in this small mechanism's package. The
        # names are portable; the module digests are derived from actual bytes.
        self.inventory = {
            path.name: _digest(path.read_bytes())
            for path in sorted(Path(__file__).parent.glob("*.py"))
        }
        self.mechanism_digest = _digest(_bytes(self.inventory))

    def prepare(self) -> None:
        if self.prepared:
            return
        self.prepared = True
        if self.root is None:
            return
        from . import run_audit

        try:
            self.replay = run_audit(self.root, timeout=self.timeout)
            _report_bytes(self.replay)
        except Exception as exc:
            # Exception details can contain local paths. The exception class is
            # sufficient to preserve failure without publishing those paths.
            self.replay = None
            self.replay_error = f"native replay unavailable: {type(exc).__name__}"

    def _differences(self, report: dict[str, Any]) -> list[str]:
        if self.replay is None:
            return [self.replay_error or "no native foundation checkout was supplied"]
        differences = []
        for label, candidate in (("supplied", report), ("replayed", self.replay)):
            execution = candidate.get("execution")
            if (not isinstance(execution, dict) or execution.get("mode") != "lean"
                    or execution.get("completed") is not True):
                differences.append(f"{label} audit has no completed Lean execution")
            for name in ("lean_build", "dependency_output", "countermodel", "finite_trace"):
                check = candidate["checks"].get(name)
                if (not isinstance(check, dict) or check.get("status") != "PASS"
                        or check.get("attempted") is not True
                        or type(check.get("exit_code")) is not int or check["exit_code"] != 0):
                    differences.append(f"{label} Lean process {name} did not complete successfully")
            subject = candidate["subject"]
            if subject.get("repository", "").removesuffix(".git") != _REPOSITORY[:-4]:
                differences.append(f"{label} repository is not canonical Hypermath")
            if subject.get("dirty") is not False:
                differences.append(f"{label} source checkout is not clean")
            if not re.fullmatch(r"[0-9a-f]{40}", str(subject.get("revision", ""))):
                differences.append(f"{label} source revision is not pinned")
            inputs = candidate["inputs"]
            if not inputs["before"] or inputs.get("stable") is not True:
                differences.append(f"{label} source inventory is not stable")
            if inputs["before"] != inputs["after"]:
                differences.append(f"{label} input bytes changed during execution")
        for field in ("subject", "inputs", "target", "declared_assumptions"):
            if report[field] != self.replay[field]:
                differences.append(f"native replay differs at {field}")
        for field in ("requested", "observed"):
            if report["toolchain"].get(field) != self.replay["toolchain"].get(field):
                differences.append(f"native replay differs at toolchain.{field}")
        current_inventory = {
            path.name: _digest(path.read_bytes())
            for path in sorted(Path(__file__).parent.glob("*.py"))
        }
        if current_inventory != self.inventory:
            differences.append("mechanism source changed during replay")
        return differences

    def evaluate(self, binding: Any, evidence: Any) -> Any:
        vstd = _verifier()
        unknown = vstd.MechanismOutcome.UNKNOWN
        report = json.loads(evidence[0])
        _report_bytes(report)
        if binding.subject_id != _digest(evidence[0]):
            return vstd.MechanismDecision(
                vstd.MechanismOutcome.FAIL, "subject does not match the bound audit report bytes"
            )
        if dict(binding.parameters) != _parameters(report) or set(binding.trust_roots) != set(_TRUST_ROOTS):
            return vstd.MechanismDecision(
                vstd.MechanismOutcome.FAIL, "claim coordinate or trust roots differ from the audit mechanism"
            )
        if binding.predicate not in (*_CLAIMS, "audit_replay_matches"):
            return vstd.MechanismDecision(unknown, "unsupported Hypermath proposition")
        if binding.expected is not True:
            return vstd.MechanismDecision(unknown, "unsupported expected proposition value")
        self.prepare()
        differences = self._differences(report)
        observations = {
            "reported_status": report["claims"].get(binding.predicate, {}).get("status"),
            "replay_performed": self.replay is not None,
            "binding_differences": differences,
            "declared_assumptions": report["declared_assumptions"],
        }
        if self.replay is not None:
            observations["replay_sha256"] = _digest(_report_bytes(self.replay))
            observations["proof_admissibility"] = self.replay["checks"].get("proof_admissibility")
        if binding.predicate == "audit_replay_matches":
            outcome = unknown if self.replay is None else (
                vstd.MechanismOutcome.FAIL if differences else vstd.MechanismOutcome.PASS
            )
            return vstd.MechanismDecision(
                outcome, "Exact source, toolchain and target comparison after native replay.",
                observations,
            )
        if binding.predicate != "self_derivation":
            return vstd.MechanismDecision(
                unknown, "No source-adequacy or recursive-arithmetic completeness checker exists.",
                observations,
            )
        if differences:
            return vstd.MechanismDecision(
                unknown, "The bound conditional Lean proof has no matching clean native replay.",
                observations,
            )
        from . import evaluate_gate

        assert self.replay is not None
        declared = self.replay["claims"]["self_derivation"]["status"]
        observations["replayed_claim"] = self.replay["claims"]["self_derivation"]
        outcome = vstd.MechanismOutcome(declared)
        if declared == "PASS" and not evaluate_gate(self.replay, claim="self_derivation"):
            outcome = unknown
        return vstd.MechanismDecision(
            outcome,
            "Fresh Lean proof-admissibility audit under explicit declared assumptions; "
            "this does not establish native source self-derivation or complete arithmetic.",
            observations,
        )


def evaluate_audit_report(
    report: Mapping[str, Any], *, foundation_root: Path | str | None = None, timeout: int = 60
) -> dict[str, Any]:
    """Execute native VSTD bound propositions and retain their exact evidence.

    The returned domain record is not a numbered-profile conformance receipt.
    Evidence bounds govern input bytes/items; ``timeout`` separately bounds each
    native audit subprocess. Native execution streams through ``run_audit``.
    """
    if type(timeout) is not int or not 0 < timeout <= 300:
        raise ValueError("timeout must be a positive integer number of seconds at most 300")
    payload = _report_bytes(report)
    report = json.loads(payload)
    vstd = _verifier()
    mechanism = _AuditMechanism(Path(foundation_root) if foundation_root is not None else None, timeout)
    mechanism.prepare()
    store = vstd.EvidenceStore()
    evidence_refs = [store.add(payload)]
    if mechanism.replay is not None:
        evidence_refs.append(store.add(_report_bytes(mechanism.replay)))
    evidence_refs = list(dict.fromkeys(evidence_refs))
    session = vstd.VerificationSession(store)
    session.register(mechanism)
    results = {}
    for claim in (*_CLAIMS, "audit_replay_matches"):
        proposition = vstd.BoundProposition(
            subject_id=_digest(payload), predicate=claim, expected=True,
            mechanism_id=mechanism.mechanism_id, mechanism_digest=mechanism.mechanism_digest,
            evidence_refs=tuple(evidence_refs),
            trust_roots=_TRUST_ROOTS,
            bounds=vstd.EvidenceBounds(max_evidence_items=2, max_evidence_bytes=2 * _MAX_BYTES),
            parameters=_parameters(report),
        )
        results[claim] = {"proposition": proposition.to_dict(),
                          "evaluation": session.evaluate(proposition).to_dict()}
    return {
        "format": "hypermath-vstd-session-1",
        "verifier_distribution": f"verifier-standard=={_VERSION}",
        "conformance": "NOT_ESTABLISHED",
        "scope": "Native bounded audit propositions, not VSTD-4 conformance or complete arithmetic.",
        "audit_sha256": _digest(payload),
        "mechanism_sources": mechanism.inventory,
        "evidence": store.export_base64(evidence_refs),
        "results": results,
    }


def write_verification_receipt(
    report: Mapping[str, Any], output_directory: Path | str, *,
    foundation_root: Path | str | None = None, timeout: int = 60,
) -> Path:
    """Write an actual VSTD-1 receipt over the audit/session evidence package.

    ``output_directory`` must be absent or empty. The real VSTD capture command
    only packages completed evidence; native audits execute first with streaming
    output. Receipt validity never changes a mathematical UNKNOWN into PASS.
    When ``foundation_root`` is supplied, a failed or unavailable matching replay,
    or a replay that cannot support the supplied proof PASS, raises RuntimeError
    after preserving the diagnostic evidence package.
    """
    destination = Path(output_directory)
    if destination.exists() and (not destination.is_dir() or any(destination.iterdir())):
        raise FileExistsError("verification output directory must be absent or empty")
    payload = _report_bytes(report)
    result = evaluate_audit_report(report, foundation_root=foundation_root, timeout=timeout)
    _portable(result)
    vstd = _verifier()
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "audit.json").write_bytes(payload)
    (destination / "session.json").write_bytes(_bytes(result))
    script = (
        "from pathlib import Path\n"
        "Path('verification.json').write_bytes(Path('session.json').read_bytes())\n"
        "print('Packaged bounded audit evidence; inspect each native outcome.')\n"
    )
    (destination / "package_evidence.py").write_text(script, encoding="utf-8")
    manifest = {
        "claim": {
            "id": "HYPERMATH-AUDIT-" + hashlib.sha256(payload).hexdigest()[:16],
            "title": "Hypermath bounded audit evidence package",
            "statement": "The command packaged the exact supplied audit and native VSTD session record.",
            "scope": "Evidence packaging; native proof outcomes are separate in verification.json.",
            "limitations": [
                "Receipt validation establishes format and stable-content integrity, not mathematics.",
                "Conditional Lean proof admissibility retains the audit's declared assumptions.",
                "The audit binds the foundation coordinate; source_state describes the packaging context.",
                "Source adequacy and recursive arithmetic completeness remain UNKNOWN.",
                "No VSTD-4 conformance or independent witness is claimed.",
            ],
            "falsification_condition": "Reject changed bound bytes; rerun the native audit on the "
                "same pinned source/toolchain and compare each proposition.",
        },
        "command": ["python", "package_evidence.py"],
        "cwd": ".", "repo_dir": ".", "timeout_seconds": 30,
        "target_name": "hypermath-audit-evidence-package",
        "inputs": [{"path": name, "role": role} for name, role in (
            ("audit.json", "native_audit_report"), ("session.json", "bound_session_evidence"),
            ("package_evidence.py", "packaging_source"),
        )],
        "outputs": [{"path": "verification.json", "role": "bound_session_evidence"}],
        "determinism_declared": "UNKNOWN",
    }
    _portable(manifest)
    (destination / "manifest.source.json").write_bytes(_bytes(manifest))
    receipt = vstd.capture_run(manifest, manifest_dir=destination)
    # VSTD records an absolute local root even for relative manifest locators.
    # Here the root is the evidence directory itself; publish its relative name.
    receipt.source_state = replace(receipt.source_state, local_repository_path=".")
    if receipt.execution.outcome != "COMPLETED":
        raise RuntimeError(f"VSTD evidence packaging did not complete: {receipt.execution.outcome}")
    _portable(receipt.to_dict())
    receipt_path = receipt.save_to_directory(destination)
    # Check every generated artifact, including native manifests, report and
    # logs. Fail rather than silently rewriting any already hashed evidence.
    for path in destination.rglob("*"):
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            # JSON escaping doubles relative Windows separators. Check the
            # decoded values, not that serialization syntax, without changing
            # the bytes bound by the receipt.
            _portable(json.loads(text) if path.suffix.lower() == ".json" else text)
    if foundation_root is not None:
        replay_status = result["results"]["audit_replay_matches"]["evaluation"]["outcome"]
        proof_status = result["results"]["self_derivation"]["evaluation"]["outcome"]
        supplied_status = json.loads(payload)["claims"]["self_derivation"]["status"]
        if replay_status != "PASS" or (supplied_status == "PASS" and proof_status != "PASS"):
            raise RuntimeError(
                "required native replay did not support the supplied audit; "
                "diagnostic evidence remains in the output directory"
            )
    return receipt_path
