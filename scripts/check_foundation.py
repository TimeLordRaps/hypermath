"""Run fresh Hypermath checks and retain evidence before applying a proof gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from hypermath_foundations import evaluate_gate, run_audit
from hypermath_foundations.vstd import write_verification_receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("build/verification"))
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--require-self-derivation", action="store_true")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    if args.output.exists() and (not args.output.is_dir() or any(args.output.iterdir())):
        parser.error("output must be absent or empty; choose a fresh directory for each audit")
    root = Path(__file__).resolve().parents[1]
    report = run_audit(root, timeout=args.timeout)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "audit.json").write_text(
        json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    write_verification_receipt(
        report, args.output / "vstd", foundation_root=root, timeout=args.timeout
    )
    for name, claim in report["claims"].items():
        print(f"{name}: {claim['status']}", flush=True)
    if report["toolchain"].get("exit_code") == 124 or any(
        item.get("exit_code") == 124 for item in report["checks"].values()
    ):
        return 124
    if report["execution"]["completed"] is not True:
        return 1
    policy = report["checks"].get("assumption_policy", {})
    if policy.get("status") != "PASS" or policy.get("attempted") is not True:
        print("Audit integrity gate is not satisfied: assumption policy did not pass", flush=True)
        return 1
    if args.require_complete and not evaluate_gate(report, "recursive_arithmetic_completeness"):
        print("Arithmetic completeness gate is not satisfied", flush=True)
        return 2
    if args.require_self_derivation and not evaluate_gate(report, "self_derivation"):
        print("Self-derivation gate is not satisfied", flush=True)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
