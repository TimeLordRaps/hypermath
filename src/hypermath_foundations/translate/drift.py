"""Compare each `.hm` derive's status tag with the hand-written Lean mechanization.

`FORM` in `.hm` is a claim; a Lean theorem without `sorry` is evidence. This module reads
`lean4/Hypermath/*.lean` as text (no Lean run) and reports, per derive, one of:
  proved   a theorem of the expected name exists and contains no `sorry`
  sorry    it exists and contains `sorry` (an admitted obligation)
  missing  no theorem of that name in the supplied Lean files
A textual match on names, not a semantic one: it does not show the Lean statement equals the
`.hm` close, and a theorem that depends on a `sorry` elsewhere still reads `proved`.
"""

from __future__ import annotations

import re

from .lean import Namer

_DECL = re.compile(r"^(?:theorem|lemma|axiom|def|noncomputable def|opaque|inductive|structure|instance|namespace|end|section)\b", re.M)
_THM = re.compile(r"^(?:private\s+)?(?:theorem|lemma)\s+([\w'.]+)", re.M)


def lean_theorems(texts: list[str]) -> dict[str, bool]:
    """name -> contains_sorry, over every theorem/lemma in the supplied texts."""
    out: dict[str, bool] = {}
    for text in texts:
        starts = [m.start() for m in re.finditer(r"^(?:private\s+)?(?:theorem|lemma|axiom|def|noncomputable|opaque|inductive|structure|instance|end\b|namespace|section|scoped|open|variable)", text, re.M)]
        starts.append(len(text))
        for a, b in zip(starts, starts[1:]):
            chunk = text[a:b]
            m = _THM.match(chunk)
            if m:
                body = re.sub(r"--[^\n]*", "", chunk)
                out[m.group(1).split(".")[-1]] = bool(re.search(r"\bsorry\b", body))
    return out


_CLAIM_DEF = re.compile(r"^def\s+(\w+)Claim\s*:\s*Prop", re.M)
_NEG_THM = re.compile(r"^theorem\s+\w+\s*:\s*¬\s*(\w+)Claim\b", re.M)


def refuted_claims(texts: list[str]) -> set[str]:
    """Names `X` such that some file defines `X`Claim and proves `¬ XClaim`.

    Reading: X's statement fails in a model the same repo constructs for its axioms, so X is not
    derivable from those axioms *as formalized in Lean*. It says nothing about the native
    semantics, which the countermodel file itself disclaims.
    """
    out: set[str] = set()
    for t in texts:
        out |= set(_CLAIM_DEF.findall(t)) & set(_NEG_THM.findall(t))
    return out


def drift(proj, lean_texts: list[str]) -> list[dict]:
    thm = lean_theorems(lean_texts)
    refuted = refuted_claims(lean_texts)
    nm = Namer({e.name for e in proj.entries if e.kind == "relation"})
    rows = []
    for e in proj.entries:
        if e.kind != "derive":
            continue
        tag = getattr(e.decl, "status", "?")
        lean = nm(e.name)
        state = "missing" if lean not in thm else ("sorry" if thm[lean] else "proved")
        gone = lean in refuted
        rows.append({"derive": e.name, "file": e.file, "line": e.line, "hm_tag": tag, "lean_name": lean,
                     "lean": "refuted-in-countermodel" if gone else state,
                     "disagrees": tag == "FORM" and (gone or state != "proved")})
    return rows


def summary(rows: list[dict]) -> dict:
    from collections import Counter
    return dict(Counter((r["hm_tag"], r["lean"]) for r in rows))
