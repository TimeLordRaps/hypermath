"""Lean 4 emitter and the kernel-check loop.

Conventions follow hypermath's own `L0Ground.lean` header: `apply` becomes `f2f`,
`==` is displayed as `≡`, primitives and opaques are `axiom` (a Lean `opaque`
would ask for an `Inhabited` default), `Prop` is Lean's, FORM derives are
`theorem … := by sorry` unless the derive is a bare instantiation of one axiom.

The kernel is the oracle: `kernel_check` compiles the output, attributes each
error to the entry that owns the line, falls a rejected proof term back to
`sorry`, and demotes any other rejected entry to `untranslated` with Lean's message.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from . import expr as ex
from .ast import And, App, Exists, Forall, Iff, Implies, Name, Not, Opaque, Or, Primitive, Relation

RENAMES = {"apply": "f2f"}
NOTATION = {"~~": ("Similar", "~~"), "=~": ("Congruent", "=~"), "==": ("Simulation", "≡")}
LEAN_RESERVED = {
    "end", "fun", "at", "from", "open", "in", "do", "by", "have", "show", "let", "match", "with",
    "if", "then", "else", "at", "variable", "universe", "section", "namespace", "theorem",
    "axiom", "def", "instance", "class", "structure", "inductive", "where", "deriving",
    "import", "export", "macro", "syntax", "notation", "infix", "local", "set", "id", "exact",
    "calc", "using", "forall", "exists", "sorry", "Type", "Sort", "Prop", "true", "false",
}


class Namer:
    def __init__(self, relations: set[str]):
        self.relations = relations
        self.cache: dict[str, str] = {}
        self.used: dict[str, str] = {}

    def __call__(self, name: str) -> str:
        if name in self.cache:
            return self.cache[name]
        base = RENAMES.get(name)
        if base is None:
            parts = re.split(r"[-_]", name)
            base = parts[0] + "".join(p[:1].upper() + p[1:] for p in parts[1:])
            if name in self.relations:
                base = base[:1].upper() + base[1:]
            if base in LEAN_RESERVED:
                base += "_"
            base = re.sub(r"[^A-Za-z0-9_']", "_", base)
        cand, i = base, 1
        while cand in self.used and self.used[cand] != name:
            i += 1
            cand = f"{base}{i}"
        self.used[cand] = name
        self.cache[name] = cand
        return cand


def render(e, nm: Namer, prec: int = 0) -> str:
    if isinstance(e, Name):
        return nm(e.name)
    if isinstance(e, App):
        if e.fn == "=":
            s = f"{render(e.args[0], nm, 51)} = {render(e.args[1], nm, 51)}"
            return f"({s})" if prec > 50 else s
        if e.fn == "!=":
            return f"¬ ({render(e.args[0], nm, 51)} = {render(e.args[1], nm, 51)})"
        if not e.args:
            return nm(e.fn)
        return "(" + " ".join([nm(e.fn)] + [render(a, nm, 1024) for a in e.args]) + ")" if prec >= 1024 \
            else " ".join([nm(e.fn)] + [render(a, nm, 1024) for a in e.args])
    if isinstance(e, Not):
        s = f"¬ {render(e.e, nm, 1024)}"
        return f"({s})" if prec >= 1024 else s
    ops = {And: (35, "∧"), Or: (30, "∨"), Implies: (25, "→"), Iff: (20, "↔")}
    if type(e) in ops:
        p, sym = ops[type(e)]
        s = f"{render(e.left, nm, p + 1)} {sym} {render(e.right, nm, p if isinstance(e, Implies) else p + 1)}"
        return f"({s})" if prec > p else s
    if isinstance(e, (Forall, Exists)):
        q = "∀" if isinstance(e, Forall) else "∃"
        bs = " ".join(f"({nm(n)} : {nm(t)})" for n, t in e.binders)
        body = render(e.body, nm, 0)
        if e.guard is not None:
            g = render(e.guard, nm, 36 if isinstance(e, Exists) else 26)
            body = f"{g} ∧ {body}" if isinstance(e, Exists) else f"{g} → {body}"
        s = f"{q} {bs}, {body}"
        return f"({s})" if prec > 0 else s
    raise TypeError(f"cannot render {e!r}")


def _doc(text: str) -> str:
    text = " ".join((text or "").split()).replace("-/", "- /")
    return f"/-- {text} -/\n" if text else ""


def _sig(sig, nm: Namer) -> str:
    return " → ".join([p if p in ("Prop", "Type") else nm(p) for p in sig.params] + [sig.result if sig.result in ("Prop", "Type") else nm(sig.result)])


@dataclass
class Emitted:
    text: str
    spans: list = field(default_factory=list)  # (first_line, last_line, entry_index)
    names: dict = field(default_factory=dict)


def instance_term(entry, proj, nm: Namer, by_name: dict) -> str | None:
    """`ax a1 … an` when the derive is a bare instantiation and binders line up."""
    if entry.proof is None:
        return None
    ax_name, binds = entry.proof
    ax = by_name.get(ax_name)
    if ax is None or ax.status != "translated" or not isinstance(ax.expr, Forall) or ax.expr.guard is not None:
        return None
    order = [n for n, _ in ax.expr.binders]
    given = dict(binds)
    if set(order) != set(given):
        return None
    arities = {n: len(s.params) for n, s in proj.sigs.items()}
    try:
        args = [render(ex.parse_expr(given[v], proj.infix, arities), nm, 1024) for v in order]
    except ex.ExprError:
        return None
    return " ".join([nm(ax_name)] + args)


def emit(proj, namespace: str = "Hypermath", demoted: dict | None = None, no_proof: set | None = None) -> Emitted:
    demoted, no_proof = demoted or {}, no_proof or set()
    rel_names = {e.name for e in proj.entries if e.kind == "relation"}
    nm = Namer(rel_names)
    by_name = {e.name: e for e in proj.entries if e.kind in ("axiom", "derive")}
    out = [
        f"-- Generated by hmtrans from: {', '.join(f for f, _ in proj.sources)}",
        "-- Do not edit; regenerate. `sorry` marks an admitted proof obligation, not a proof.",
        f"namespace {namespace}", "",
    ]
    res = Emitted("")
    notations = set()

    def put(idx: int, lines: str):
        first = len(out) + 1
        out.extend(lines.rstrip("\n").split("\n"))
        res.spans.append((first, len(out), idx))
        out.append("")

    # Lean needs declaration before use; `.hm` does not (L2 uses `congruent-path` before
    # its `opaque`). Vocabulary goes first, then statements, each in source order.
    vocab = [i for i, e in enumerate(proj.entries) if e.kind in ("primitive", "opaque", "relation")]
    rest = [i for i, e in enumerate(proj.entries) if e.kind not in ("primitive", "opaque", "relation")]
    for idx in vocab + rest:
        e = proj.entries[idx]
        if idx in demoted or e.status not in ("translated", "admitted"):
            continue
        d = e.decl
        if isinstance(d, (Primitive, Opaque)):
            put(idx, f"{_doc(d.doc)}axiom {nm(d.name)} : {_sig(d.sig, nm)}")
        elif isinstance(d, Relation):
            put(idx, f"{_doc(d.doc)}axiom {nm(d.name)} : {_sig(d.sig, nm)}")
            if d.symbol in NOTATION and len(d.sig.params) == 2 and d.symbol not in notations:
                notations.add(d.symbol)
                rel, shown = NOTATION[d.symbol]
                res.spans.append((len(out) + 1, len(out) + 1, idx))
                out.append(f'scoped notation:50 a " {shown} " b => {nm(d.name)} a b')
                out.append("")
        elif e.kind in ("axiom", "close"):
            put(idx, f"{_doc(d.doc)}axiom {nm(e.name)} : {render(e.expr, nm)}")
        elif e.kind == "derive":
            term = None if idx in no_proof else instance_term(e, proj, nm, by_name)
            proof = term if term else "by sorry"
            put(idx, f"{_doc(d.doc)}theorem {nm(d.name)} : {render(e.expr, nm)} :=\n  {proof}")
    out.append(f"end {namespace}")
    res.text = "\n".join(out) + "\n"
    res.names = dict(nm.cache)
    return res


_ERR = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning): (?P<msg>.*)$")


def run_lean(text: str, lean_bin: str, timeout: int = 120) -> tuple[int, list[tuple[int, str]], str]:
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "Out.lean"
        p.write_text(text, encoding="utf-8")
        r = subprocess.run([lean_bin, str(p)], capture_output=True, text=True, timeout=timeout)
    errs, cur = [], None
    for ln in (r.stdout + r.stderr).splitlines():
        m = _ERR.match(ln)
        if m:
            cur = [int(m["line"]), m["msg"]] if m["sev"] == "error" else None
            if cur:
                errs.append(cur)
        elif cur is not None:
            cur[1] += "\n" + ln
    return r.returncode, [(a, b) for a, b in errs], r.stdout + r.stderr


def kernel_check(proj, lean_bin: str, namespace: str = "Hypermath", max_rounds: int = 25):
    """Compile, attribute errors to entries, repair or demote, repeat to a fixed point.

    Returns (Emitted, kernel_log) where kernel_log lists every repair:
    ("proof->sorry"|"demoted", entry_index, message). Final output compiles with no errors.
    """
    demoted: dict[int, str] = {}
    no_proof: set[int] = set()
    log = []
    for _ in range(max_rounds):
        out = emit(proj, namespace, demoted, no_proof)
        code, errs, raw = run_lean(out.text, lean_bin)
        if not errs:
            if code != 0:
                raise RuntimeError("lean exited non-zero with no attributable error:\n" + raw)
            for idx, why in demoted.items():
                proj.entries[idx].status = "untranslated"
                proj.entries[idx].reason = "rejected by the Lean kernel: " + why
            for idx in no_proof:
                proj.entries[idx].proof = None
            return out, log
        progressed = False
        for line, msg in errs:
            owner = next((i for a, b, i in out.spans if a <= line <= b), None)
            if owner is None:
                raise RuntimeError(f"Lean error outside any entry (line {line}): {msg}")
            e = proj.entries[owner]
            if e.kind == "derive" and owner not in no_proof and e.proof is not None:
                no_proof.add(owner)
                log.append(("proof->sorry", owner, msg.splitlines()[0]))
            elif owner not in demoted:
                demoted[owner] = msg.splitlines()[0]
                log.append(("demoted", owner, msg.splitlines()[0]))
            else:
                continue
            progressed = True
        if not progressed:
            raise RuntimeError("kernel_check made no progress:\n" + raw)
    raise RuntimeError("kernel_check did not converge")
