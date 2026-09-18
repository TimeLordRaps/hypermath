"""Reproduce finite layer graphs and adversarial checks through Lean and Verifier."""

from __future__ import annotations

import argparse
import copy
import json
import shutil
import sys
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from hypermath_foundations._surface import SurfaceRejected  # noqa: E402
from hypermath_foundations.layer_graph import LayerGraph, LayerSupportMechanism  # noqa: E402
from hypermath_foundations.vstd import _bytes, _digest, _portable, _verifier  # noqa: E402


def invalid_projection(surface):
    """Serialize the existing malformed-projection counterexample; Lean checks it."""
    bits = iter(surface["code"])

    def parse():
        return None if next(bits) == "0" else (parse(), parse())

    def emit(tree):
        return "0" if tree is None else "1" + emit(tree[0]) + emit(tree[1])

    def tag(index, payload):
        marker = None
        for _ in range(index):
            marker = (None, marker)
        return marker, payload

    tree = parse()
    assert next(bits, None) is None
    record, claim = tree[1][1]
    malformed = tag(5, (claim, (claim, record)))
    return {"format": surface["format"], "layer": 0,
            "code": emit(tag(12, tag(0, (malformed, claim))))}


def tampered_support(builder, result, target, alteration):
    """Rebind tampered bytes, so the domain check must catch semantic changes."""
    from verifier.core.certificate import canonical_digest

    vstd = _verifier()
    payload = copy.deepcopy({"format": result["format"], "graph": result["graph"],
                             "surfaces": result["surfaces"]})
    edge = next(e for e in payload["graph"]["transformations"]
                if e["outputs"][0]["artifact_id"] == target)
    before = {p["artifact_id"] for p in edge["inputs"]}
    if alteration == "reverse":
        edge["inputs"].reverse()
        for i, port in enumerate(edge["inputs"]):
            port["role"] = f"operand:{i}"
    elif alteration == "repetition":
        edge["inputs"].pop()
    else:
        raise ValueError("unsupported adversarial probe")
    assert {p["artifact_id"] for p in edge["inputs"]} == before
    original = next(e for e in result["assurance"]["events"] if e["subject_id"] == target)
    store = vstd.EvidenceStore()
    reference = store.add(_bytes(payload))
    binding = vstd.BoundProposition.from_dict(original["binding"])
    binding = replace(binding, evidence_refs=(reference,), expected={
        **binding.expected, "historical_graph_digest": canonical_digest(payload["graph"]),
    })
    session = vstd.VerificationSession(store)
    session.register(LayerSupportMechanism(builder.runner))
    evaluation = session.evaluate(binding)
    assert evaluation.outcome is vstd.MechanismOutcome.FAIL, evaluation.to_dict()
    return {"binding": binding.to_dict(), "evaluation": evaluation.to_dict(),
            "evidence_payloads": store.export_base64((reference,))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="build/layer-graph")
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--clean", action="store_true", help="clean output directory if it exists")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    relative = Path(args.output)
    if relative.is_absolute() or ".." in relative.parts:
        parser.error("output must be a repository-relative directory")
    output = (root / relative).resolve()
    output.relative_to(root)
    if args.clean and output.exists():
        shutil.rmtree(output)
    if output.exists() and any(output.iterdir()):
        parser.error("output directory must be absent or empty; use --clean or choose a fresh directory")
    output.mkdir(parents=True, exist_ok=True)
    vstd = _verifier()
    print("START source audit and real Lean surface runner", flush=True)
    builder = LayerGraph(root, timeout=args.timeout)
    output.mkdir(parents=True, exist_ok=True)
    (output / "audit.json").write_bytes(_bytes(builder.runner.audit) + b"\n")
    print("START construct primitive, lifted, composed and repeated surfaces", flush=True)
    ground = builder.primitive()
    difference = builder.primitive("diff")
    first, second = builder.lift(ground), builder.lift(difference)
    composed = builder.compose(first, second)
    repeated = builder.compose(first, first)
    raised = builder.lift(composed)
    print("START earn prerequisite-bound support in the real Verifier ledger", flush=True)
    result = builder.finalize(recorded_at=datetime.now(timezone.utc).isoformat())
    assert len(result["graph"]["artifacts"]) == 7
    assert len(result["assurance"]["events"]) == 5
    assert all(e["outcome"] == "PASS" for e in result["assurance"]["events"])
    assert all(status == "UNKNOWN" for status in result["mathematical_claims"].values())
    _portable(result)
    (output / "graph.json").write_bytes(_bytes(result) + b"\n")
    print("START replay the serialized assurance log using the same bound Lean mechanism", flush=True)
    replay = vstd.recheck_assurance_log(
        result["assurance"], mechanisms=[LayerSupportMechanism(builder.runner)],
    )
    assert replay.to_dict() == result["assurance"]
    assert len(replay.current_trust_events()) == 5
    assert replay.verify_hash_chain()
    print("PASS: five exact support events reconstructed by fresh Lean edge checks", flush=True)
    failures = {}
    for name, target in [("reverse", composed), ("repetition", repeated)]:
        print(f"START reject {name} while preserving the graph input set", flush=True)
        failures[name] = tampered_support(builder, result, target, name)
        print(f"PASS: {name} rejected after rebinding graph and evidence digests", flush=True)
    for name, surface in [
        ("invalid-projection", invalid_projection(builder.surfaces[ground])),
        ("wrong-layer", {**builder.surfaces[ground], "layer": 1}),
        ("trailing-code", {**builder.surfaces[ground], "code": builder.surfaces[ground]["code"] + "0"}),
    ]:
        print(f"START reject {name} in the real Lean checker", flush=True)
        try:
            builder.runner.call("inspect", [surface])
        except SurfaceRejected:
            failures[name] = {"rejected": True, "surface": surface}
        else:
            raise AssertionError(f"{name} was not rejected")
        print(f"PASS: {name} rejected", flush=True)
    builder.runner.assert_current()
    _portable(failures)
    (output / "negative-evidence.json").write_bytes(_bytes(failures) + b"\n")
    summary = {"coordinate": builder.runner.coordinate, "nodes": 7, "supported_edges": 5,
               "replayed_edges": 5, "negative_checks": sorted(failures),
               "targets": {"composed": composed, "repeated": repeated, "raised": raised},
               "artifacts": {name: _digest((output / name).read_bytes())
                             for name in ["audit.json", "graph.json", "negative-evidence.json"]}}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("PASS: real Lean/Verifier graph, exact replay and five adversarial checks; arithmetic claims UNKNOWN",
          flush=True)


if __name__ == "__main__":
    main()
