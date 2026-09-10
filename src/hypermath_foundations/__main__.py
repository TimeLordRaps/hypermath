"""Command-line interface for bounded Hypermath evidence audits."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from ._reports import CLAIMS
from .audit import run_audit
from .gate import evaluate_gate


def _options(parser):
    parser.add_argument("--root", default=".", help="checkout to audit")
    parser.add_argument("--output", help="repository-relative JSON report path")
    parser.add_argument("--timeout", type=float, default=60, help="seconds per subprocess (max 300)")
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--lake", help="optional lake executable override")
    parser.add_argument("--details", action="store_true", help="included for legacy compatibility")
    parser.add_argument("--require-self-derivation", action="store_true")
    parser.add_argument("--require-complete", action="store_true")


def _execute(args, *, legacy=False):
    try:
        root = Path(args.root).resolve(strict=True)
        destination = None
        if args.output:
            relative = Path(args.output)
            if relative.is_absolute() or ".." in relative.parts or relative.suffix != ".json":
                raise ValueError("output must be a repository-relative .json path")
            destination = (root / relative).resolve()
            destination.relative_to(root)
        report = run_audit(root, args.timeout, inventory_only=args.inventory_only, lake=args.lake)
        payload = json.dumps(report, indent=2, ensure_ascii=True) + "\n"
        if destination:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(payload, encoding="utf-8")
        else:
            print(payload, end="", flush=True)
    except (OSError, ValueError) as error:
        print(f"Audit could not complete ({type(error).__name__}); check root/output/tool settings",
              file=sys.stderr, flush=True)
        return 1
    if (any(item["exit_code"] == 124 for item in report["checks"].values())
            or report["toolchain"].get("exit_code") == 124):
        return 124
    if not report["execution"]["completed"]:
        return 1
    policy = report["checks"].get("assumption_policy", {})
    if not args.inventory_only and (
        policy.get("status") != "PASS" or policy.get("attempted") is not True
    ):
        print("Audit integrity gate is not satisfied: assumption policy did not pass", flush=True)
        return 1
    if args.require_complete and not all(evaluate_gate(report, c) for c in CLAIMS):
        return 2
    if args.require_self_derivation and not evaluate_gate(report):
        return 2
    if legacy and (report["admissions"]["source"] or report["admissions"]["transitive_targets"]):
        return 2
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    _options(commands.add_parser("audit", help="run a fresh bounded evidence audit"))
    return _execute(parser.parse_args(argv))


def legacy_main(root, argv=None):
    parser = argparse.ArgumentParser(description="Legacy Hypermath proof-admission gate")
    _options(parser)
    parser.set_defaults(root=str(root))
    return _execute(parser.parse_args(argv), legacy=True)


if __name__ == "__main__":
    raise SystemExit(main())
