"""Graph binding contracts with synthetic transport; real Lean runs in the native check script."""

from __future__ import annotations

import copy
from dataclasses import replace

import pytest
import verifier

from hypermath_foundations import _surface as surface_module
from hypermath_foundations import layer_graph
from hypermath_foundations._surface import SurfaceRejected, SurfaceUnavailable, surface_payload
from hypermath_foundations.layer_graph import LayerGraph, LayerSupportMechanism
from hypermath_foundations.vstd import _bytes


class SyntheticRunner:
    """Deliberately synthetic codes: these tests establish no Lean or mathematical result."""

    def __init__(self, *args, **kwargs):
        self.inventory = {"synthetic": "1" * 64}
        self.coordinate = {"repository": "https://github.com/TimeLordRaps/hypermath.git",
                           "revision": "2" * 40, "dirty": True,
                           "source_inventory_digest": "sha256:" + "3" * 64,
                           "lean_toolchain": "synthetic transport only"}
        self.changed = False
        self.unavailable = False

    def assert_current(self):
        if self.changed:
            raise SurfaceUnavailable("synthetic source changed")

    def call(self, operation, inputs=(), *, rule="", depth=0):
        if self.unavailable:
            raise SurfaceUnavailable("synthetic timeout")
        if operation == "primitive":
            layer, code = 0, "0" if rule == "groundSelf" else "100"
        elif operation == "inspect":
            layer, code = inputs[0]["layer"], inputs[0]["code"]
        elif operation == "lift":
            layer, code = inputs[0]["layer"] + 1, "10" + inputs[0]["code"] + "0"
        else:
            layer, code = inputs[0]["layer"], "11" + inputs[0]["code"] + inputs[1]["code"]
        if code == "000":
            raise SurfaceRejected("synthetic invalid record")
        return {"surface": {"format": "hypermath-surface-1", "layer": layer, "code": code},
                "valid": True, "claims": [code]}


@pytest.fixture
def construction(monkeypatch):
    monkeypatch.setattr(layer_graph, "LeanSurfaceRunner", SyntheticRunner)
    builder = LayerGraph("synthetic")
    a = builder.lift(builder.primitive())
    b = builder.lift(builder.primitive("diff"))
    composed = builder.compose(a, b)
    repeated = builder.compose(a, a)
    return builder, a, b, composed, repeated


def bound_edge(builder, payload, identifier):
    mechanism = LayerSupportMechanism(builder.runner)
    store = verifier.EvidenceStore()
    reference = store.add(_bytes(payload))
    session = verifier.VerificationSession(store)
    session.register(mechanism)
    edge = next(e for e in payload["graph"]["transformations"] if e["transformation_id"] == identifier)
    target = edge["outputs"][0]["artifact_id"]
    binding = verifier.BoundProposition(
        subject_id=target, predicate="vstd.graph.support",
        expected={"historical_graph_digest": layer_graph._canonical_digest(payload["graph"]),
                  "inputs": sorted({p["artifact_id"] for p in edge["inputs"]}),
                  "output": target, "prerequisite_trust_event_digests": [],
                  "transformation_id": identifier},
        mechanism_id=mechanism.mechanism_id, mechanism_digest=mechanism.mechanism_digest,
        evidence_refs=(reference,), trust_roots=layer_graph._TRUST_ROOTS,
        bounds=verifier.EvidenceBounds(1, layer_graph._MAX_EVIDENCE_BYTES),
        parameters=layer_graph._parameters(builder.runner),
    )
    return session, binding


def payload_for(builder):
    return copy.deepcopy({"format": layer_graph._DOMAIN, "graph": builder.graph.to_dict(),
                          "surfaces": builder.surfaces})


def test_real_ledger_requires_prerequisites_and_preserves_repeated_ports(construction):
    builder, a, _, _, repeated = construction
    result = builder.finalize(recorded_at="2026-09-10T00:00:00Z")
    assert all(c == "UNKNOWN" for c in result["mathematical_claims"].values())
    events = result["assurance"]["events"]
    assert len(events) == 4 and all(event["outcome"] == "PASS" for event in events)
    event = next(e for e in events if e["subject_id"] == repeated)
    assert event["source_ids"] == [a]
    assert len(event["attributes"]["prerequisite_trust_event_digests"]) == 1
    edge = next(e for e in result["graph"]["transformations"] if e["outputs"][0]["artifact_id"] == repeated)
    assert edge["inputs"] == [{"artifact_id": a, "role": "operand:0"},
                              {"artifact_id": a, "role": "operand:1"}]
    with pytest.raises(ValueError, match="frozen"):
        builder.lift(repeated)


@pytest.mark.parametrize("tamper", [
    "reverse_order", "lose_repetition", "alter_output", "role", "source_coordinate",
    "wrong_graph_digest", "wrong_domain", "wrong_trust_roots", "payload_digest",
])
def test_exact_edge_binding_rejects_tampering(construction, tamper):
    builder, _, _, _, _ = construction
    payload = payload_for(builder)
    index = 3 if tamper == "lose_repetition" else 2
    edge = payload["graph"]["transformations"][index]
    original_inputs = {p["artifact_id"] for p in edge["inputs"]}
    if tamper == "reverse_order":
        edge["inputs"].reverse()
        for i, port in enumerate(edge["inputs"]):
            port["role"] = f"operand:{i}"
    elif tamper == "lose_repetition":
        edge["inputs"].pop()
    elif tamper == "role":
        edge["inputs"][0]["role"] = "unbound"
    elif tamper == "source_coordinate":
        edge["software_provenance"]["revision"] = "9" * 40
    elif tamper in {"alter_output", "payload_digest"}:
        key = edge["outputs"][0]["artifact_id"]
        payload["surfaces"][key]["code"] += "0"
        if tamper == "alter_output":
            # Rebind its content digest too: this must fail the operation, not only hashing.
            raw = _bytes(payload["surfaces"][key])
            node = next(a for a in payload["graph"]["artifacts"] if a["artifact_id"] == key)
            node["content_digest"] = layer_graph._digest(raw).removeprefix("sha256:")
            node["byte_size"] = len(raw)
    session, binding = bound_edge(builder, payload, edge["transformation_id"])
    if tamper == "wrong_graph_digest":
        binding = replace(binding, expected={**binding.expected, "historical_graph_digest": "0" * 64})
    elif tamper == "wrong_domain":
        binding = replace(binding, parameters={"domain": "arithmetic-completeness"})
    elif tamper == "wrong_trust_roots":
        binding = replace(binding, trust_roots=("unsupported unconditional soundness",))
    if tamper in {"reverse_order", "lose_repetition"}:
        assert {p["artifact_id"] for p in edge["inputs"]} == original_inputs
    assert session.evaluate(binding).outcome is verifier.MechanismOutcome.FAIL


@pytest.mark.parametrize("problem", ["changed_source", "timeout", "bound"])
def test_unavailable_checking_stays_unknown(construction, problem):
    builder, _, _, _, _ = construction
    payload = payload_for(builder)
    edge = payload["graph"]["transformations"][2]
    session, binding = bound_edge(builder, payload, edge["transformation_id"])
    if problem == "changed_source":
        builder.runner.changed = True
    elif problem == "timeout":
        builder.runner.unavailable = True
    else:
        binding = replace(binding, bounds=verifier.EvidenceBounds(1, 1))
    assert session.evaluate(binding).outcome is verifier.MechanismOutcome.UNKNOWN


def test_unrelated_invalid_genesis_cannot_be_finalized(construction):
    builder, *_ = construction
    builder._retain({"surface": {"format": "hypermath-surface-1", "layer": 0, "code": "000"}})
    with pytest.raises(SurfaceRejected, match="invalid"):
        builder.finalize(recorded_at="2026-09-10T00:00:00Z")


def test_source_ledger_rejects_missing_derived_prerequisite(construction):
    builder, *_ = construction
    payload = payload_for(builder)
    edge = payload["graph"]["transformations"][2]
    session, binding = bound_edge(builder, payload, edge["transformation_id"])
    ledger = verifier.AssuranceLedger(builder.graph)
    with pytest.raises(ValueError, match="prerequisite"):
        ledger.record_trust(binding.subject_id, binding.expected["inputs"], binding,
                            transformation_id=edge["transformation_id"], session=session,
                            recorded_at="2026-09-10T00:00:00Z")


@pytest.mark.parametrize("field,value,error", [
    ("layer", True, SurfaceRejected), ("layer", -1, SurfaceRejected),
    ("layer", 17, SurfaceUnavailable), ("code", "2", SurfaceRejected),
    ("code", "1" * 8192, SurfaceUnavailable),
], ids=["boolean-layer", "negative-layer", "layer-bound", "nonbinary-code", "tree-bound"])
def test_surface_bounds_do_not_become_mathematical_falsity(field, value, error):
    payload = {"format": "hypermath-surface-1", "layer": 0, "code": "0", field: value}
    with pytest.raises(error):
        surface_payload(payload)


@pytest.mark.parametrize("error", [OSError, ValueError])
def test_unreadable_source_inventory_is_unavailable(monkeypatch, tmp_path, error):
    runner = object.__new__(surface_module.LeanSurfaceRunner)
    runner.root = tmp_path
    runner.inventory = {}
    runner.audit = {"subject": {}}

    def unavailable(_root):
        raise error("synthetic inaccessible source")

    monkeypatch.setattr(surface_module, "_snapshot", unavailable)
    with pytest.raises(SurfaceUnavailable):
        runner.assert_current()
