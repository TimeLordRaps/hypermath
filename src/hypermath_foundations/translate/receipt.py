"""Machine-readable receipt: what was translated, what was not, and why. Canonical JSON + SHA-256."""

from __future__ import annotations

import hashlib
import json
from collections import Counter

from .project import sha256


def canonical(obj) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def build(proj, lean_text: str | None, lean_log: list, mm_text: str | None, mm_status: dict | None,
          lean_version: str | None, mm_tool: str | None) -> dict:
    entries = []
    for i, e in enumerate(proj.entries):
        row = {"kind": e.kind, "name": e.name, "file": e.file, "line": e.line, "status": e.status}
        if e.reason:
            row["reason"] = e.reason
        if e.proof:
            row["instantiates"] = e.proof[0]
        if mm_status is not None and i in mm_status:
            row["metamath"] = mm_status[i]
        entries.append(row)
    rec = {
        "tool": "hmtrans", "schema": 1,
        "sources": [{"file": f, "sha256": h} for f, h in proj.sources],
        "counts": {f"{k}/{s}": n for (k, s), n in sorted(Counter((e.kind, e.status) for e in proj.entries).items())},
        "entries": entries,
        "lean": None if lean_text is None else {
            "version": lean_version, "output_sha256": sha256(lean_text),
            "kernel_repairs": [{"action": a, "entry": proj.entries[i].name, "message": m} for a, i, m in lean_log],
            "sorry_obligations": sum(
                1 for ln in lean_text.splitlines() if ln.strip() == "by sorry"),
        },
        "metamath": None if mm_text is None else {"verifier": mm_tool, "output_sha256": sha256(mm_text)},
        "guarantees": [
            "Every non-translated entry names its reason; nothing is dropped silently.",
            "Lean output compiled with no errors against the stated version; `sorry` entries are admitted obligations.",
            "Metamath output has no logical axioms: proved derives certify instantiation and sort/arity only.",
            "Translation fidelity (that the Lean statement means what the .hm statement means) is NOT established by either checker.",
        ],
    }
    rec["receipt_sha256"] = hashlib.sha256(canonical(rec).encode()).hexdigest()
    return rec
