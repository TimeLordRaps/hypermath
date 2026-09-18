"""Bounded transport to the Lean finite-surface definitions; no Python proof checker."""

from __future__ import annotations

import json
import re
import tempfile
from pathlib import Path
from typing import Any

from .audit import _find_lake, _redactor, _run_process, _snapshot, _subject, run_audit
from .vstd import _bytes, _digest

MAX_CODE_BITS = 8191
MAX_LAYER = 16
MAX_REQUEST_BYTES = 65536


class SurfaceRejected(ValueError):
    """Malformed representation or a negative result from the finite checker."""


class SurfaceUnavailable(RuntimeError):
    """A bound, dependency or execution failure prevents a checking result."""


def surface_payload(value: Any) -> dict[str, Any]:
    """Check transport shape only; validity is delegated to Lean."""
    if not isinstance(value, dict) or set(value) != {"format", "layer", "code"}:
        raise SurfaceRejected("a surface requires exactly format, layer and code")
    if value["format"] != "hypermath-surface-1":
        raise SurfaceRejected("unsupported surface format")
    if type(value["layer"]) is not int or value["layer"] < 0:
        raise SurfaceRejected("layer must be a nonnegative integer")
    if value["layer"] > MAX_LAYER:
        raise SurfaceUnavailable("surface exceeds the finite layer resource bound")
    if not isinstance(value["code"], str) or not re.fullmatch("[01]+", value["code"]):
        raise SurfaceRejected("surface code must be a nonempty binary prefix string")
    if len(value["code"]) > MAX_CODE_BITS:
        raise SurfaceUnavailable("surface exceeds the tree-size resource bound")
    return dict(value)


class LeanSurfaceRunner:
    """Audit the source once, then execute it with exact input/source binding.

    Construction checks may use a dirty development checkout. Its exact source
    inventory and dirty state remain visible; this is not clean audit replay.
    """

    def __init__(self, foundation_root: str | Path, *, timeout: int = 60) -> None:
        if type(timeout) is not int or not 1 <= timeout <= 300:
            raise ValueError("timeout must be an integer from 1 to 300 seconds")
        self.root = Path(foundation_root).resolve(strict=True)
        self.timeout = timeout
        self.audit = run_audit(self.root, timeout=timeout)
        if (not self.audit["execution"]["completed"]
                or self.audit["checks"]["assumption_policy"]["status"] != "PASS"
                or not self.audit["inputs"]["stable"]):
            raise SurfaceUnavailable("foundation execution and exact source policy must pass")
        if self.audit["subject"]["repository"].removesuffix(".git") != (
            "https://github.com/TimeLordRaps/hypermath"
        ):
            raise SurfaceUnavailable("foundation repository identity does not match Hypermath")
        self.inventory = dict(self.audit["inputs"]["after"])
        self.coordinate = {
            "repository": self.audit["subject"]["repository"],
            "revision": self.audit["subject"]["revision"],
            "dirty": self.audit["subject"]["dirty"],
            "source_inventory_digest": _digest(_bytes(self.inventory)),
            "lean_toolchain": self.audit["toolchain"]["requested"],
        }
        self.assert_current()

    def assert_current(self) -> None:
        try:
            inventory = _snapshot(self.root)
            subject = _subject(self.root)
        except (OSError, ValueError) as exc:
            raise SurfaceUnavailable("source identity can no longer be inspected") from exc
        if inventory != self.inventory or subject != self.audit["subject"]:
            raise SurfaceUnavailable("source or executing mechanism changed after the audit")

    def call(self, operation: str, inputs=(), *, rule: str = "", depth: int = 0) -> dict:
        if operation not in {"primitive", "inspect", "lift", "compose"}:
            raise SurfaceRejected("unsupported surface operation")
        if type(depth) is not int or depth < 0:
            raise SurfaceRejected("term depth must be a nonnegative integer")
        if operation == "primitive" and rule not in {"groundSelf", "diff", "sim", "box"}:
            raise SurfaceRejected("primitive needs a supported rule and natural term depth")
        if depth > 32:
            raise SurfaceUnavailable("primitive term depth exceeds the resource bound")
        operands = [surface_payload(value) for value in inputs]
        if len(operands) != {"primitive": 0, "inspect": 1, "lift": 1, "compose": 2}[operation]:
            raise SurfaceRejected("incorrect operand count")
        request = _bytes({"operation": operation, "inputs": operands, "rule": rule, "depth": depth})
        if len(request) > MAX_REQUEST_BYTES:
            raise SurfaceUnavailable("surface request exceeds the byte bound")
        self.assert_current()
        try:
            with tempfile.TemporaryDirectory(prefix="hypermath-surface-") as temporary:
                path = Path(temporary) / "request.json"
                path.write_bytes(request)
                code, output = _run_process(
                    [_find_lake(None), "env", "lean", "--run", "SurfaceBridge.lean", str(path)],
                    self.root / "lean4", self.timeout, _redactor(self.root),
                )
        except (OSError, ValueError) as exc:
            raise SurfaceUnavailable(f"surface execution unavailable: {type(exc).__name__}") from exc
        self.assert_current()
        if code != 0:
            raise SurfaceUnavailable(f"surface execution did not complete: exit {code}")
        lines = [line.removeprefix("HYPERMATH_SURFACE_RESULT:") for line in output.splitlines()
                 if line.startswith("HYPERMATH_SURFACE_RESULT:")]
        if len(lines) != 1:
            raise SurfaceUnavailable("surface execution did not return one result")
        try:
            response = json.loads(lines[0])
            if not isinstance(response, dict):
                raise SurfaceUnavailable("surface response is not an object")
            if response.get("status") == "LIMIT":
                raise SurfaceUnavailable(response["reason"])
            if response.get("status") == "REJECTED":
                raise SurfaceRejected(response["reason"])
            if response.get("status") != "OK":
                raise SurfaceUnavailable("unexpected surface response status")
            result = response["result"]
            surface_payload(result["surface"])
            if type(result["valid"]) is not bool:
                raise SurfaceUnavailable("surface checker omitted a Boolean result")
            if not result["valid"]:
                raise SurfaceRejected("ground-record checking rejected this surface")
            if not isinstance(result["claims"], list) or not all(
                isinstance(item, str) and re.fullmatch("[01]+", item) for item in result["claims"]
            ):
                raise SurfaceUnavailable("accepted surface omitted its ordered claims")
            return result
        except (KeyError, TypeError, json.JSONDecodeError) as exc:
            raise SurfaceUnavailable("malformed surface execution response") from exc
