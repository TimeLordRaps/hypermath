"""Bounded, streaming build and admission audit for the Lean translation.

Exit 0: audited builds pass and no admitted proof was found in these surfaces.
Exit 1: tooling, build, dependency report, or countermodel check failed.
Exit 2: compilation may pass, but admitted proofs remain (expected currently).
Exit 124: a subprocess exceeded its explicitly bounded execution time.

This checks compilation and visible assumptions, not consistency, completeness,
or fidelity of the entire native theory. No third-party Python packages needed.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import sys
import threading
import time


ROOT = Path(__file__).resolve().parent
SOURCE_PARAMETERS = frozenset({
    "Form", "ground", "f2f", "structContinues", "structDistinct", "structOrbits",
    "Similar", "Congruent", "Simulation", "HMSyntax", "Substance", "Semantics",
    "Derives", "Discharge", "Definition", "FormClosure", "deriver", "D",
    "DerivationPath", "pathStep", "pathGround", "pathLength", "pathTrace",
    "compose", "congruentPath", "pathStart", "pathEnd", "ordinalLimit",
    "ordinalSucc", "finiteApplyFromGround", "ordinalApply",
})


def lean_code(source: str) -> str:
    """Mask nested comments and string literals while preserving line numbers."""
    output = list(source)
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                output[index:index + 2] = "  "
                block_depth += 1
                index += 2
                continue
            if source.startswith("-/", index):
                output[index:index + 2] = "  "
                block_depth -= 1
                index += 2
                continue
            if source[index] != "\n":
                output[index] = " "
            index += 1
            continue
        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                output[index:index + 2] = "  "
                index += 2
                continue
            if source[index] == '"':
                in_string = False
            if source[index] != "\n":
                output[index] = " "
            index += 1
            continue
        if source.startswith("/-", index):
            output[index:index + 2] = "  "
            block_depth = 1
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            output[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            in_string = True
            output[index] = " "
            index += 1
        else:
            index += 1
    return "".join(output)


def inventory(details: bool) -> int:
    totals = {"sorry": 0, "parameters": 0, "clauses": 0, "opaque": 0}
    for path in sorted((ROOT / "Hypermath").rglob("*.lean")):
        code = lean_code(path.read_text(encoding="utf-8"))
        admissions = list(re.finditer(r"\b(?:sorry|sorryAx|admit)\b", code))
        axioms = list(re.finditer(r"(?m)^\s*axiom\s+([^\s:]+)", code))
        parameters = sum(match.group(1) in SOURCE_PARAMETERS for match in axioms)
        opaques = list(re.finditer(r"(?m)^\s*opaque\s+([^\s:]+)", code))
        counts = {"sorry": len(admissions), "parameters": parameters,
                  "clauses": len(axioms) - parameters, "opaque": len(opaques)}
        for key in totals:
            totals[key] += counts[key]
        print(f"{path.relative_to(ROOT)}: admitted_tokens={counts['sorry']}; "
              f"source_parameters={parameters}; logical_axiom_clauses={counts['clauses']}; "
              f"opaque_declarations={counts['opaque']}", flush=True)
        for match in admissions:
            line = code.count("\n", 0, match.start()) + 1
            print(f"  OPEN {path.relative_to(ROOT)}:{line}: {match.group()}", flush=True)
        if details:
            for match in axioms:
                name = match.group(1)
                line = code.count("\n", 0, match.start(1)) + 1
                category = "source parameter" if name in SOURCE_PARAMETERS else "logical clause"
                print(f"  ASSUMPTION {path.relative_to(ROOT)}:{line}: {name} ({category})",
                      flush=True)
    print(f"TOTAL: {totals['sorry']} admitted tokens; {totals['parameters']} source "
          f"parameters + {totals['clauses']} logical axiom clauses = "
          f"{totals['parameters'] + totals['clauses']} axiom declarations; "
          f"{totals['opaque']} opaque declarations", flush=True)
    return totals["sorry"]


def find_lake(override: str | None) -> str:
    if override:
        return override
    installed = shutil.which("lake")
    if installed:
        return installed
    local = Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if local.is_file():
        return str(local)
    raise FileNotFoundError("lake was not found; install the pinned toolchain or use --lake PATH")


def run_bounded(command: list[str], timeout: float) -> tuple[int, str]:
    print(f"START ({timeout:g}s limit): {' '.join(command)}", flush=True)
    process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                               errors="replace", start_new_session=os.name != "nt")
    events: queue.Queue[str | None] = queue.Queue()

    def read_output() -> None:
        assert process.stdout is not None
        for line in process.stdout:
            events.put(line)
        events.put(None)

    reader = threading.Thread(target=read_output, daemon=True)
    reader.start()
    started = last_output = time.monotonic()
    collected: list[str] = []
    output_ended = False
    while not output_ended or process.poll() is None:
        now = time.monotonic()
        if now - started > timeout:
            print("STOP-LOSS: subprocess exceeded its timeout; terminating process tree", flush=True)
            if os.name == "nt":
                subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"], timeout=10)
            else:
                import signal
                os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=10)
            return 124, "".join(collected)
        if now - last_output > 40:
            print(f"OBSERVATION: no new output for 40s; still running {command[-1]}; "
                  f"{timeout - (now - started):.1f}s remain before stop-loss", flush=True)
            last_output = now
        try:
            line = events.get(timeout=0.1)
        except queue.Empty:
            continue
        if line is None:
            output_ended = True
        else:
            collected.append(line)
            print(line, end="", flush=True)
            last_output = time.monotonic()
    code = process.wait(timeout=10)
    print(f"EXIT {code}: {' '.join(command)}", flush=True)
    return code, "".join(collected)


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60,
                        help="maximum seconds per subprocess (default: 60)")
    parser.add_argument("--lake", help="path to lake executable")
    parser.add_argument("--inventory-only", action="store_true", help="skip Lean processes")
    parser.add_argument("--details", action="store_true", help="print every declared assumption")
    args = parser.parse_args()
    if not 0 < args.timeout <= 300:
        parser.error("--timeout must be positive and at most 300 seconds")
    admissions = inventory(args.details)
    dependency_admissions = False
    if not args.inventory_only:
        try:
            lake = find_lake(args.lake)
            for command in ([lake, "-v", "build"],
                            [lake, "env", "lean", "Audit.lean"],
                            [lake, "env", "lean", "Countermodels.lean"]):
                code, output = run_bounded(command, args.timeout)
                if code:
                    print("AUDIT TOOLING/BUILD FAILED; no proof-completion claim", flush=True)
                    return 124 if code == 124 else 1
                if command[-1] == "Audit.lean":
                    dependency_admissions = "sorryAx" in output
                if command[-1] == "Countermodels.lean" and "sorryAx" in output:
                    print("COUNTERMODEL CHECK FAILED: countermodel depends on admitted proof", flush=True)
                    return 1
        except (OSError, subprocess.SubprocessError) as error:
            print(f"AUDIT ERROR: {error}", flush=True)
            return 1
    if admissions or dependency_admissions:
        print("PROOF GATE INCOMPLETE: admitted proofs remain; compilation success does not "
              "certify the theory, its self-derivation, or arithmetic completeness.", flush=True)
        return 2
    print("No admissions found in audited surfaces. Declared assumptions still require "
          "independent mathematical assessment; this is not a consistency/completeness proof.",
          flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
