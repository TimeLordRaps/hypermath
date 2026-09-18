"""Verifier Standard evidence for finite layer lifting and composition.

Graph support means that the bound output is exactly the stated Lean surface
operation on its ordered inputs, and ground-record checking accepts it. It
does not mean native self-derivation, arithmetic truth, or completeness.
"""

from __future__ import annotations

import importlib
import json
from pathlib import Path

from ._surface import LeanSurfaceRunner, SurfaceRejected, SurfaceUnavailable, surface_payload
from .vstd import _bytes, _digest, _portable, _verifier

__all__ = ["LayerGraph", "LayerSupportMechanism", "SurfaceRejected", "SurfaceUnavailable"]

_DOMAIN = "hypermath-finite-layer-1"
_MAX_EVIDENCE_BYTES = 2 * 1024 * 1024
_MAX_NODES = 64
_MAX_EDGES = 64
_TRUST_ROOTS = (
    "Lean 4.14.0 compiler and runtime executing the bound finite surface definitions",
    "Hypermath host serialization and graph adapter at the bound source inventory",
    "Source-derived ground calculus; model soundness is conditional on its stated rules",
    "verifier-standard==1.4.0 evidence dispatch and graph assurance ledger",
)


def _models():
    _verifier()
    return importlib.import_module("verifier.data.models")


def _canonical_digest(value):
    _verifier()
    return importlib.import_module("verifier.core.certificate").canonical_digest(value)


def _parameters(runner):
    return {"domain": _DOMAIN, "source_inventory_digest": runner.coordinate["source_inventory_digest"]}


def _retained_surface(graph, surfaces, identifier):
    models = _models()
    asset = graph.artifacts[identifier]
    value = surface_payload(surfaces[identifier])
    raw = _bytes(value)
    if (asset.content_digest != _digest(raw).removeprefix("sha256:")
            or asset.byte_size != len(raw)
            or asset.status is not models.ArtifactStatus.VALID
            or asset.artifact_type is not models.ArtifactType.EXECUTION_EVIDENCE
            or asset.attributes != {"format": value["format"], "layer": value["layer"]}):
        raise SurfaceRejected("surface content or interpretation does not match the artifact")
    return value


class LayerSupportMechanism:
    """Recompute an exact finite graph edge using the audited Lean definitions."""

    mechanism_id = "hypermath-foundations/finite-layer-support-1"

    def __init__(self, runner: LeanSurfaceRunner) -> None:
        self.runner = runner
        self.mechanism_digest = _digest(_bytes({
            "domain": _DOMAIN, "source_inventory": runner.inventory,
            "coordinate": runner.coordinate,
        }))

    def evaluate(self, binding, evidence):
        vstd = _verifier()
        try:
            observations = self._check(binding, evidence)
        except SurfaceUnavailable as exc:
            return vstd.MechanismDecision(vstd.MechanismOutcome.UNKNOWN, str(exc))
        except (SurfaceRejected, KeyError, TypeError, ValueError) as exc:
            return vstd.MechanismDecision(
                vstd.MechanismOutcome.FAIL, f"finite layer support rejected: {type(exc).__name__}",
            )
        return vstd.MechanismDecision(
            vstd.MechanismOutcome.PASS,
            "Exact ordered surface operation and ground-record checking reproduced in Lean",
            observations,
        )

    def _check(self, binding, evidence):
        self.runner.assert_current()
        if (binding.predicate != "vstd.graph.support"
                or binding.mechanism_id != self.mechanism_id
                or binding.mechanism_digest != self.mechanism_digest
                or tuple(binding.trust_roots) != tuple(sorted(_TRUST_ROOTS))
                or dict(binding.parameters) != _parameters(self.runner)):
            raise SurfaceRejected("proposition does not name this exact domain and dependency scope")
        if len(evidence) != 1 or len(evidence[0]) > _MAX_EVIDENCE_BYTES:
            raise SurfaceUnavailable("graph evidence exceeds the mechanism bound")
        payload = json.loads(evidence[0])
        if _bytes(payload) != evidence[0]:
            raise SurfaceRejected("graph evidence must be canonical JSON without duplicate keys")
        _portable(payload)
        if set(payload) != {"format", "graph", "surfaces"} or payload["format"] != _DOMAIN:
            raise SurfaceRejected("unexpected graph evidence format")
        models = _models()
        graph = models.ProvenanceHypergraph.from_dict(
            payload["graph"], allow_legacy_identifier_overlap=False,
        )
        if len(graph.artifacts) > _MAX_NODES or len(graph.transformations) > _MAX_EDGES:
            raise SurfaceUnavailable("graph exceeds the node or edge resource bound")
        if graph.validate_structure() or _bytes(graph.to_dict()) != _bytes(payload["graph"]):
            raise SurfaceRejected("malformed or noncanonical graph")
        expected = binding.expected
        if not isinstance(expected, dict) or set(expected) != {
            "historical_graph_digest", "inputs", "output",
            "prerequisite_trust_event_digests", "transformation_id",
        }:
            raise SurfaceRejected("support claim lacks its exact topology coordinate")
        if expected["historical_graph_digest"] != _canonical_digest(graph.to_dict()):
            raise SurfaceRejected("graph digest mismatch")
        edge = graph.transformations[expected["transformation_id"]]
        ordered_ids = [port.artifact_id for port in edge.inputs]
        if (expected["inputs"] != sorted(set(ordered_ids))
                or expected["output"] != binding.subject_id
                or [(p.artifact_id, p.role) for p in edge.outputs] != [(binding.subject_id, "result")]
                or [p.role for p in edge.inputs] != [f"operand:{i}" for i in range(len(ordered_ids))]
                or edge.software_provenance != self.runner.coordinate
                or edge.transformation_type is not models.TransformationType.EVIDENCE_BINDING
                or edge.status != "COMPLETED"):
            raise SurfaceRejected("edge identity, ports or source coordinate do not match")
        operation = edge.parameters.get("operation")
        if edge.parameters != {"domain": _DOMAIN, "operation": operation} or operation not in {
            "lift", "compose",
        }:
            raise SurfaceRejected("unsupported transformation parameters")
        if len(ordered_ids) != {"lift": 1, "compose": 2}[operation]:
            raise SurfaceRejected("transformation lost or added operands")
        if not isinstance(payload["surfaces"], dict) or set(payload["surfaces"]) != set(graph.artifacts):
            raise SurfaceRejected("surface inventory differs from graph artifacts")

        inputs = [_retained_surface(graph, payload["surfaces"], key) for key in ordered_ids]
        claimed_output = _retained_surface(graph, payload["surfaces"], binding.subject_id)
        result = self.runner.call(operation, inputs)
        if result["surface"] != claimed_output:
            raise SurfaceRejected("output is not the exact operation on its ordered operands")
        return {
            "operation": operation, "ordered_inputs": ordered_ids,
            "input_layers": [item["layer"] for item in inputs],
            "output_layer": claimed_output["layer"], "ordered_claims": result["claims"],
            "scope": "finite surface operation and source-relative ground-record acceptance",
            "source_inventory_digest": self.runner.coordinate["source_inventory_digest"],
        }


class LayerGraph:
    """Build checked finite surfaces, then freeze their graph and earn edge support.

    ``finalize`` returns local evidence objects. No files are published, and no
    native self-derivation or arithmetic-completeness status is promoted.
    """

    def __init__(self, foundation_root: str | Path, *, timeout: int = 60) -> None:
        self.runner = LeanSurfaceRunner(foundation_root, timeout=timeout)
        self.graph = _models().ProvenanceHypergraph()
        self.surfaces: dict[str, dict] = {}
        self._edges: list[str] = []
        self._frozen = False

    def _require_open(self):
        if self._frozen:
            raise ValueError("this graph is frozen; create a new construction for further changes")
        self.runner.assert_current()

    def _retain(self, result):
        models = _models()
        value = surface_payload(result["surface"])
        raw = _bytes(value)
        identifier = "surface:" + _digest(raw).removeprefix("sha256:")
        if identifier not in self.surfaces:
            if len(self.surfaces) >= _MAX_NODES:
                raise SurfaceUnavailable("graph node bound exceeded")
            self.graph.add_artifact(models.ArtifactNode(
                artifact_id=identifier, label=f"Finite derivation surface at layer {value['layer']}",
                artifact_type=models.ArtifactType.EXECUTION_EVIDENCE,
                content_digest=_digest(raw).removeprefix("sha256:"), byte_size=len(raw),
                mime_type="application/json", status=models.ArtifactStatus.VALID,
                evidence_class=models.EvidenceClassification.REPRODUCED,
                attributes={"format": value["format"], "layer": value["layer"]},
            ))
            self.surfaces[identifier] = value
        return identifier

    def primitive(self, rule: str = "groundSelf", *, depth: int = 0) -> str:
        self._require_open()
        return self._retain(self.runner.call("primitive", rule=rule, depth=depth))

    def add_surface(self, surface: dict) -> str:
        self._require_open()
        return self._retain(self.runner.call("inspect", [surface]))

    def lift(self, source: str) -> str:
        return self._derive("lift", [source])

    def compose(self, first: str, second: str) -> str:
        return self._derive("compose", [first, second])

    def _derive(self, operation, identifiers):
        self._require_open()
        if len(self._edges) >= _MAX_EDGES:
            raise SurfaceUnavailable("graph edge bound exceeded")
        inputs = [self.surfaces[key] for key in identifiers]
        result = self.runner.call(operation, inputs)
        target = self._retain(result)
        identifier = "operation:" + _digest(_bytes([operation, identifiers, target])).removeprefix("sha256:")
        if identifier not in self.graph.transformations:
            models = _models()
            self.graph.add_transformation(models.TransformationHyperedge(
                transformation_id=identifier, label=f"Finite surface {operation}",
                transformation_type=models.TransformationType.EVIDENCE_BINDING,
                inputs=[models.HyperedgePort(key, f"operand:{i}") for i, key in enumerate(identifiers)],
                outputs=[models.HyperedgePort(target, "result")],
                software_provenance=dict(self.runner.coordinate),
                parameters={"domain": _DOMAIN, "operation": operation},
                execution_environment={"lean_toolchain": self.runner.coordinate["lean_toolchain"]},
                evidence_class=models.EvidenceClassification.REPRODUCED, status="COMPLETED",
            ))
            self._edges.append(identifier)
        return target

    def finalize(self, *, recorded_at: str) -> dict:
        self._require_open()
        vstd = _verifier()
        if (self.graph.validate_structure() or not self.graph.verify_acyclicity()
                or set(self.surfaces) != set(self.graph.artifacts)
                or len(self._edges) != len(set(self._edges))
                or set(self._edges) != set(self.graph.transformations)):
            raise SurfaceRejected("graph structure does not validate")
        for identifier in self.graph.artifacts:
            value = _retained_surface(self.graph, self.surfaces, identifier)
            if not self.graph.incoming_hyperedges(identifier):
                checked = self.runner.call("inspect", [value])
                if checked["surface"] != value:
                    raise SurfaceRejected("genesis surface is not canonical")
        payload = {"format": _DOMAIN, "graph": self.graph.to_dict(), "surfaces": self.surfaces}
        _portable(payload)
        raw = _bytes(payload)
        if len(raw) > _MAX_EVIDENCE_BYTES:
            raise SurfaceUnavailable("graph evidence exceeds the byte resource bound")
        store = vstd.EvidenceStore()
        reference = store.add(raw)
        session = vstd.VerificationSession(store)
        mechanism = LayerSupportMechanism(self.runner)
        session.register(mechanism)
        ledger = vstd.AssuranceLedger(self.graph)
        events = {}
        for identifier in self._edges:
            edge = self.graph.transformations[identifier]
            sources = sorted({port.artifact_id for port in edge.inputs})
            prerequisites = sorted(events[key].digest() for key in sources if key in events)
            target = edge.outputs[0].artifact_id
            binding = vstd.BoundProposition(
                subject_id=target, predicate="vstd.graph.support",
                expected={"historical_graph_digest": ledger.graph_digest, "inputs": sources,
                          "output": target, "prerequisite_trust_event_digests": prerequisites,
                          "transformation_id": identifier},
                mechanism_id=mechanism.mechanism_id, mechanism_digest=mechanism.mechanism_digest,
                evidence_refs=(reference,), trust_roots=_TRUST_ROOTS,
                bounds=vstd.EvidenceBounds(1, _MAX_EVIDENCE_BYTES), parameters=_parameters(self.runner),
            )
            event = ledger.record_trust(
                target, sources, binding, transformation_id=identifier,
                prerequisite_trust_event_digests=prerequisites, session=session, recorded_at=recorded_at,
            )
            if event.outcome is vstd.MechanismOutcome.UNKNOWN:
                raise SurfaceUnavailable(event.details)
            if event.outcome is not vstd.MechanismOutcome.PASS:
                raise SurfaceRejected(event.details)
            events[target] = event
        if len(ledger.current_trust_events()) != len(self._edges):
            raise SurfaceRejected("not every recorded edge has current support")
        self._frozen = True
        return {
            "format": _DOMAIN, "coordinate": dict(self.runner.coordinate),
            "graph": json.loads(_bytes(self.graph.to_dict())),
            "surfaces": json.loads(_bytes(self.surfaces)), "assurance": ledger.to_dict(),
            "source_inventory": dict(self.runner.inventory),
            "scope": "finite operation preservation; not native or arithmetic completeness",
            "mathematical_claims": {name: "UNKNOWN" for name in (
                "native_self_derivation", "source_adequacy", "ordinal_interpretation",
                "arithmetic_completeness",
            )},
        }
