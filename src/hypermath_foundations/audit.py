"""Fresh, bounded Lean evidence collection for the current repository contents.

The report is an observation, not a signed attestation. Its hashes identify
inputs; they do not authenticate a report supplied by an untrusted party.
"""

from __future__ import annotations

import hashlib
import os
import platform
import queue
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

from ._inventory import inventory
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


def _subject(root: Path) -> dict:
    values = []
    for args in (("remote", "get-url", "origin"), ("rev-parse", "HEAD"),
                 ("status", "--porcelain", "--untracked-files=normal")):
        try:
            result = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                                    text=True, encoding="utf-8", timeout=10, check=True)
            values.append(result.stdout.strip())
        except (OSError, subprocess.SubprocessError):
            values.append(None)
    remote, revision, status = values
    aliases = {REPOSITORY, REPOSITORY + ".git", "git@github.com:TimeLordRaps/hypermath.git"}
    return {
        "repository": REPOSITORY if remote in aliases else None,
        "revision": revision if revision and re.fullmatch(r"[0-9a-f]{40}", revision) else None,
        "dirty": None if status is None else bool(status),
    }


def _snapshot(root: Path) -> dict[str, str]:
    paths = set(root.glob("*.hm"))
    paths.update((root / "references").rglob("*.hm"))
    for folder, directories, names in os.walk(root / "lean4"):
        directories[:] = [d for d in directories if d not in {".lake", "__pycache__"}]
        paths.update(Path(folder) / n for n in names if n.endswith(".lean"))
    paths.update(root / name for name in (
        "pyproject.toml", "lean4/lean-toolchain", "lean4/lakefile.toml",
        "lean4/lake-manifest.json", "lean4/audit.py",
    ) if (root / name).is_file())
    paths.update((root / "src" / "hypermath_foundations").rglob("*.py"))
    result = {}
    for path in sorted(paths):
        # Do not follow symlinked source inputs outside the audited checkout.
        path.resolve().relative_to(root)
        result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    # Bind the package actually executing, including an installed wheel outside root.
    for path in sorted(Path(__file__).parent.glob("*.py")):
        result["runner/hypermath_foundations/" + path.name] = hashlib.sha256(
            path.read_bytes()).hexdigest()
    return result


def _redactor(root: Path):
    substitutions = [(str(root), "<repository>"), (str(Path.home()), "<home>"),
                     (sys.prefix, "<python>"), (sys.base_prefix, "<python-base>")]
    for name in ("ELAN_HOME", "LEAN_SYSROOT", "VIRTUAL_ENV", "CODEX_HOME", "TEMP", "TMP"):
        if os.environ.get(name):
            substitutions.append((os.environ[name], "<runtime>"))
    substitutions.sort(key=lambda pair: len(pair[0]), reverse=True)

    def redact(text: str) -> str:
        for path, replacement in substitutions:
            for variant in {path, path.replace("\\", "/"), path.replace("/", "\\")}:
                text = re.sub(re.escape(variant), lambda _: replacement, text, flags=re.I)
        # Foreign absolute Windows paths may occur in compiler diagnostics too.
        return re.sub(r"(?<![\w])[A-Za-z]:[/\\][^\s\]\[\"'<>]+", "<absolute-path>", text)

    return redact


def _find_lake(override: str | None) -> str:
    if override:
        return override
    installed = shutil.which("lake")
    if installed:
        return installed
    local = Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if local.is_file():
        return str(local)
    raise FileNotFoundError("lake unavailable; install the pinned Lean toolchain")


def _run_process(command: list[str], cwd: Path, timeout: float, redact) -> tuple[int, str]:
    label = " ".join(["lake", *command[1:]])
    print(f"START ({timeout:g}s limit): {label}", file=sys.stderr, flush=True)
    process = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                               errors="replace", start_new_session=os.name != "nt")
    events: queue.Queue[str | None] = queue.Queue()

    def read_output():
        assert process.stdout is not None
        for line in process.stdout:
            events.put(line)
        events.put(None)

    threading.Thread(target=read_output, daemon=True).start()
    started = last_output = time.monotonic()
    collected, ended = [], False
    while not ended or process.poll() is None:
        now = time.monotonic()
        if now - started > timeout:
            print(f"TIMEOUT: {label}; terminating process tree", file=sys.stderr, flush=True)
            try:
                if os.name == "nt":
                    subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                                   capture_output=True, timeout=10, check=False)
                else:
                    os.killpg(process.pid, signal.SIGKILL)
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait(timeout=10)
            return 124, "".join(collected)
        if now - last_output >= 40:
            print(f"OBSERVATION: no output for 40s in {label}; timeout remains active",
                  file=sys.stderr, flush=True)
            last_output = now
        try:
            line = events.get(timeout=0.1)
        except queue.Empty:
            continue
        if line is None:
            ended = True
        else:
            clean = redact(line)
            collected.append(clean)
            print(clean, end="", file=sys.stderr, flush=True)
            last_output = time.monotonic()
    code = process.wait(timeout=10)
    print(f"EXIT {code}: {label}", file=sys.stderr, flush=True)
    return code, "".join(collected)


def _check(reason: str) -> dict:
    return {"status": "UNKNOWN", "attempted": False, "exit_code": None,
            "output": "", "reasons": [reason]}


def run_audit(root, timeout=60, *, inventory_only=False, lake=None) -> dict:
    """Observe a checkout and freshly run Lean, with seconds bounded per process.

    A stable dirty checkout may yield proof evidence for its exact hashed bytes.
    The default downstream gate additionally requires a clean checkout. Source
    adequacy and arithmetic completeness are not established by this audit.
    """
    if isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or not 0 < timeout <= 300:
        raise ValueError("timeout must be positive and at most 300 seconds")
    root = Path(root).resolve(strict=True)
    if not root.is_dir() or not (root / "lean4").is_dir():
        raise ValueError("root must contain the Hypermath lean4 directory")
    redact = _redactor(root)
    before_subject = _subject(root)
    before = _snapshot(root)
    admissions, assumptions = inventory(root)
    toolchain_path = root / "lean4" / "lean-toolchain"
    requested = toolchain_path.read_text(encoding="utf-8-sig").strip() if toolchain_path.exists() else None
    report = {
        "format": FORMAT,
        "runner": {"name": "hypermath-foundations", "version": "0.1.0"},
        "subject": before_subject,
        "toolchain": {"requested": redact(requested) if requested else None,
                      "observed": None, "python": platform.python_version(), "exit_code": None},
        "execution": {"mode": "inventory" if inventory_only else "lean", "completed": False},
        "inputs": {"before": before, "after": {}, "stable": False, "sha256": digest(before)},
        "checks": {name: _check("Lean execution not attempted") for name in
                   ("lean_build", "dependency_output", *PROBE_TARGETS)},
        "target": {"name": TARGET, "kind": None, "dependencies": None, "statement": None},
        "admissions": {"source": admissions, "transitive_targets": []},
        "declared_assumptions": assumptions,
        "claims": {},
    }
    if not inventory_only:
        try:
            executable = _find_lake(lake)
            code, output = _run_process([executable, "env", "lean", "--version"],
                                        root / "lean4", timeout, redact)
            report["toolchain"]["exit_code"] = code
            if code or not re.search(r"Lean\s+\(version\s+\d", output):
                raise RuntimeError("Lean version report unavailable or malformed")
            report["toolchain"]["observed"] = output.strip()
            commands = {
                "lean_build": [executable, "-v", "build"],
                "dependency_output": [executable, "env", "lean", "Audit.lean"],
                "countermodel": [executable, "env", "lean", "Countermodels.lean"],
                "finite_trace": [executable, "env", "lean", "TraceChecks.lean"],
                "observation": [executable, "env", "lean", "ObservationChecks.lean"],
                "full_model": [executable, "env", "lean", "FullAxiomModel.lean"],
                "finite_action": [executable, "env", "lean", "FiniteActionCountermodel.lean"],
                "ground_syntax": [executable, "env", "lean", "GroundSyntaxChecks.lean"],
                "ground_derivation": [executable, "env", "lean", "GroundDerivationChecks.lean"],
                "record_encoding": [executable, "env", "lean", "RecordEncodingChecks.lean"],
            }
            for name, command in commands.items():
                check = report["checks"][name]
                check["attempted"] = True
                code, output = _run_process(command, root / "lean4", timeout, redact)
                check.update(exit_code=code, output=output, status="FAIL" if code else "PASS",
                             reasons=["subprocess failed" if code else "Lean process succeeded"])
                if code:
                    break
                if name == "dependency_output":
                    records = dependency_records(output, DEPENDENCY_TARGETS)
                    if not target_is_theorem(output):
                        raise ValueError("selfDerivation was not reported as a theorem")
                    declarations = kernel_declarations(output)
                    report["target"].update(kind="theorem", dependencies=records[TARGET],
                                            statement=declarations[TARGET])
                    for assumption in assumptions:
                        assumption["kernel_declaration"] = declarations.get(assumption["name"])
                    report["admissions"]["transitive_targets"] = sorted(
                        name for name, deps in records.items() if "sorryAx" in deps)
                elif name in PROBE_TARGETS:
                    records = dependency_records(output, PROBE_TARGETS[name])
                    if not probe_dependencies_valid(name, records):
                        raise ValueError(f"{name} probes have an unreviewed axiom dependency")
        except (OSError, subprocess.SubprocessError, ValueError, RuntimeError) as error:
            reason = redact(f"{type(error).__name__}: {error}")
            print(reason, file=sys.stderr, flush=True)
            for check in report["checks"].values():
                if check["attempted"] and check["status"] == "PASS":
                    # The last successful process may have returned invalid evidence.
                    check["reasons"].append(reason)
            active = next((name for name in reversed(report["checks"])
                           if report["checks"][name]["attempted"]), None)
            if active:
                report["checks"][active]["status"] = "FAIL"
            else:
                report["checks"]["lean_build"]["reasons"] = [reason]
    after = _snapshot(root)
    after_subject = _subject(root)
    report["subject_after"] = after_subject
    report["inputs"].update(after=after, stable=before == after and before_subject == after_subject)
    report["execution"]["completed"] = inventory_only or all(
        item["status"] == "PASS" for item in report["checks"].values())
    policy = _check("Kernel assumption policy was not checked")
    if report["target"]["kind"] == "theorem":
        errors = policy_errors(report["checks"]["dependency_output"]["output"], before, assumptions)
        policy.update(status="FAIL" if errors else "PASS", attempted=True,
                      reasons=errors or ["Kernel assumptions and target match the reviewed allowance"])
    report["checks"]["assumption_policy"] = policy
    status, reasons = "UNKNOWN", ["Fresh successful proof reports are unavailable"]
    if report["execution"]["completed"] and not inventory_only:
        deps = report["target"]["dependencies"]
        if "sorryAx" in deps:
            status, reasons = "UNKNOWN", ["selfDerivation transitively depends on sorryAx"]
        elif policy["status"] == "PASS":
            status, reasons = "PASS", [
                "Lean reports selfDerivation as a theorem without transitive sorryAx",
                "The result remains relative to the listed declared assumptions",
            ]
    admissibility = "UNKNOWN"
    if report["execution"]["completed"] and not inventory_only:
        admissibility = "FAIL" if (
            "sorryAx" in report["target"]["dependencies"] or policy["status"] != "PASS"
        ) else "PASS"
    report["checks"]["proof_admissibility"] = {
        "status": admissibility, "attempted": report["target"]["kind"] == "theorem",
        "exit_code": None, "output": "", "reasons": list(reasons),
    }
    if not report["inputs"]["stable"]:
        status, reasons = "UNKNOWN", ["Source contents or Git coordinate changed during the audit"]
    if any(before_subject[key] is None for key in before_subject):
        status, reasons = "UNKNOWN", ["Canonical repository coordinate could not be established"]
    report["claims"] = {
        "self_derivation": {"status": status, "reasons": reasons},
        "source_adequacy": {"status": "UNKNOWN", "reasons": [
            "No adequacy proof connects the full native .hm semantics to this Lean translation"]},
        "recursive_arithmetic_completeness": {"status": "UNKNOWN", "reasons": [
            "No bridge proof establishes recursive arithmetic completeness"]},
    }
    return report
