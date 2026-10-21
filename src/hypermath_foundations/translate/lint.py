"""Source lint: report `.hm` defects the translator found, grouped by cause.

Reports only the *first* problem per declaration (the parser stops there), so a
declaration may surface a second defect after the first is fixed. The report says so.
"""

from __future__ import annotations

import re
from collections import defaultdict

_UNDECLARED = re.compile(r"name '([^']+)' is used but not declared")
_JUXTA = re.compile(r"'([^']+)' is applied by juxtaposition but has no declared arity")
_PLUS = re.compile(r"unexpected '([^']+)'")


STATUS_WORDS = {"FORM", "FRAME", "OPEN", "HYPER"}


def lint(proj) -> dict:
    """`close_names_a_derive`: the word is another block's name or a status tag used as the
    close (a reference, not an operation). Only genuinely unknown words are `undeclared_words`."""
    block_names = {e.name for e in proj.entries}
    undeclared: dict = defaultdict(list)
    references: dict = defaultdict(list)
    prose, comment_only = [], []
    for e in proj.entries:
        if e.status != "untranslated":
            continue
        r = e.reason
        m = _UNDECLARED.search(r) or _JUXTA.search(r)
        if m and (m.group(1) in block_names or m.group(1) in STATUS_WORDS):
            references[m.group(1)].append((e.file, e.line, e.kind, e.name))
        elif m:
            undeclared[m.group(1)].append((e.file, e.line, e.kind, e.name))
        elif "comments only" in r:
            comment_only.append((e.file, e.line, e.name))
        elif e.kind in ("close", "derive") and "prose" in r or "translatable fragment" in r:
            prose.append((e.file, e.line, e.kind, e.name))
    return {"undeclared_words": dict(undeclared), "close_names_a_block": dict(references), "comment_only_closes": comment_only,
            "prose_statements": prose}


def format_report(rep: dict) -> str:
    out = []
    if rep["undeclared_words"]:
        out.append("Words used but never declared (first problem per declaration):")
        for w, where in sorted(rep["undeclared_words"].items()):
            out.append(f"  {w}")
            for f, ln, kind, name in where:
                out.append(f"    {f}:{ln}  {kind} {name}")
    if rep["close_names_a_block"]:
        out.append("Closes that name another block or a status tag instead of stating a formula:")
        for w, where in sorted(rep["close_names_a_block"].items()):
            out.append(f"  {w}  <- " + ", ".join(f"{f}:{ln} {name}" for f, ln, _, name in where))
    if rep["comment_only_closes"]:
        out.append("Closes whose content is in comments only (no formula line):")
        out += [f"  {f}:{ln}  {n}" for f, ln, n in rep["comment_only_closes"]]
    out.append(f"Statements in prose / outside the translatable fragment: {len(rep['prose_statements'])}")
    return "\n".join(out)
