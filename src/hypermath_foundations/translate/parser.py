"""Block parser for `.hm`: top-level keyword blocks, comments as documentation.

Column-zero comment lines are section banners and end the current block;
indented lines and blank lines belong to the block above them. Anything that is
not a recognised declaration is kept as a `Raw` block.
"""

from __future__ import annotations

import re

from . import expr as ex
from .ast import Axiom, Close, Derive, Module, Opaque, Primitive, Raw, Relation, Sig, Span, Step

TOP = ("primitive", "opaque", "relation", "axiom", "derive", "non-derive", "close", "graduation")


def split_comment(line: str) -> tuple[str, str]:
    """(code, comment) with `--` as the comment marker; quotes protect it."""
    in_q = False
    for i, c in enumerate(line):
        if c == '"':
            in_q = not in_q
        elif not in_q and line.startswith("--", i):
            return line[:i], line[i + 2:]
    return line, ""


def parse_sig(text: str) -> Sig:
    parts = [p.strip() for p in re.split(r"->", text.strip()) if p.strip()]
    return Sig(tuple(parts[:-1]), parts[-1]) if parts else Sig((), "")


_PRIM = re.compile(r"^(primitive|opaque|relation)\s+(\S+?)\s*(::|:)\s*(.+?)\s*$")
_AXIOM = re.compile(r"^axiom\s+(\S+?)\s*:\s*(.*)$")
_DERIVE = re.compile(r"^derive\s+(\S+)\s+as\s+(\w+)\s*:")
_NONDERIVE = re.compile(r"^non-derive\s+(\S+?)\s*:")
_CLOSE_AS = re.compile(r"^close\s+(\S+)\s+as\s+(\S+?)\s*:")
_CLOSE_IN = re.compile(r"^close\s+(\S+)\s+in\s+(\S+)\s+as\s+(\w+)\s*:")
_STEP = re.compile(r"^\s*step\s+(\d+)\s*:\s*(.*)$")
_CLOSE_LINE = re.compile(r"^\s*close\s*:\s*(.*)$")
_CITE = re.compile(
    r"^(?P<name>[A-Za-z_□][\w'-]*)"
    r"(?:\s+with\s+(?P<binds>.+?))?"
    r"(?:\s*(?:->|—)\s*(?P<res>.+?))?\s*\.?\s*$"
)


def _blocks(lines):
    """Yield (start_line_index, [raw lines]) for every top-level block."""
    cur = None
    for i, raw in enumerate(lines):
        if raw.strip() == "":
            if cur is not None:
                cur[1].append(raw)
            continue
        if raw[0].isspace():
            if cur is not None:
                cur[1].append(raw)
            continue
        code, _ = split_comment(raw)
        if code.strip() == "":  # column-zero comment: a banner, ends the block
            if cur is not None:
                yield cur
                cur = None
            continue
        if cur is not None:
            yield cur
        cur = (i, [raw])
    if cur is not None:
        yield cur


def _doc_and_code(body_lines):
    doc, code = [], []
    for raw in body_lines:
        c, cm = split_comment(raw)
        if cm.strip() and not c.strip():
            doc.append(cm.strip())
        elif c.strip():
            code.append(c.rstrip())
            if cm.strip():
                doc.append(cm.strip())
    return "\n".join(doc), code


def _parse_binds(text: str):
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    pairs = []
    for part in out:
        m = re.match(r"^\s*([A-Za-z_][\w'-]*)\s*:=\s*(.+?)\s*\.?\s*$", part)
        if not m:
            return None
        pairs.append((m.group(1), m.group(2)))
    return tuple(pairs)


def _step(n: int, text: str) -> Step:
    m = _CITE.match(text.strip())
    if m:
        binds = _parse_binds(m.group("binds")) if m.group("binds") else ()
        if binds is not None:
            return Step(n, text, m.group("name"), binds, m.group("res"))
    return Step(n, text)


def parse(text: str, file: str = "<memory>", known: dict | None = None, infix: dict | None = None) -> Module:
    """Parse one file. `known` and `infix` carry declarations from files before it."""
    lines = text.splitlines()
    mod = Module(file=file)
    mod.sigs.update(known or {})
    mod.infix.update(infix or {})
    blocks = list(_blocks(lines))
    for start, raw in blocks:  # signatures first: juxtaposition needs arities
        m = _PRIM.match(split_comment(raw[0])[0].strip())
        if m:
            mod.sigs[m.group(2)] = parse_sig(m.group(4))
    arities = {n: len(sig.params) for n, sig in mod.sigs.items()}

    # relation symbols first, so infix operators resolve in every later body
    for start, raw in blocks:
        head, trailing = split_comment(raw[0])
        m = _PRIM.match(head.strip())
        if m and m.group(1) == "relation":
            sym = re.search(r"\(([^)\s]+)\)", trailing)
            if sym:
                mod.infix[sym.group(1)] = m.group(2)

    for start, raw in blocks:
        span = Span(file, start + 1)
        head_code, head_comment = split_comment(raw[0])
        head = head_code.strip()
        doc, code = _doc_and_code(raw[1:])
        kw = head.split()[0] if head.split() else ""

        m = _PRIM.match(head)
        if m and kw in ("primitive", "opaque", "relation"):
            kind, name, _, sig = m.groups()
            if kind == "primitive":
                mod.decls.append(Primitive(name, parse_sig(sig), doc, span))
            elif kind == "opaque":
                mod.decls.append(Opaque(name, parse_sig(sig), doc, span))
            else:
                s = re.search(r"\(([^)\s]+)\)", head_comment)
                mod.decls.append(Relation(name, parse_sig(sig), s.group(1) if s else None, doc, span))
            continue

        m = _AXIOM.match(head)
        if m:
            body_text = "\n".join(([m.group(2)] if m.group(2).strip() else []) + [c.strip() for c in code])
            body, err = None, None
            if body_text.strip():
                try:
                    body = ex.parse_axiom_body(body_text, mod.infix, arities)
                except ex.ExprError as e:
                    err = str(e)
            else:
                err = "axiom has no code body (statement is in comments only)"
            mod.decls.append(Axiom(m.group(1), body, err, doc, span, body_text))
            continue

        m = _DERIVE.match(head)
        if m:
            steps, close_parts, last = [], [], None
            for c in code:
                sm, cm = _STEP.match(c), _CLOSE_LINE.match(c)
                if sm:
                    steps.append([int(sm.group(1)), sm.group(2).strip()])
                    last = "step"
                elif cm:
                    close_parts.append(cm.group(1).strip())
                    last = "close"
                elif last == "step" and steps:
                    steps[-1][1] += " " + c.strip()
                elif last == "close" and close_parts:
                    close_parts[-1] += " " + c.strip()
            mod.decls.append(Derive(m.group(1), m.group(2), tuple(_step(n, t) for n, t in steps),
                                    " ".join(close_parts), doc, span))
            continue

        m = _CLOSE_IN.match(head)
        if m:
            mod.decls.append(Close(m.group(1), m.group(2), m.group(3), "\n".join(c.strip() for c in code), doc, span))
            continue
        m = _CLOSE_AS.match(head)
        if m:
            mod.decls.append(Close(m.group(1), m.group(2), None, "\n".join(c.strip() for c in code), doc, span))
            continue

        full = "\n".join(raw).rstrip()
        m = _NONDERIVE.match(head)
        if m:
            mod.decls.append(Raw("non-derive", m.group(1), full, span))
            continue
        name = "graduation" if kw == "graduation" else (head.split()[1].rstrip(":") if len(head.split()) > 1 else kw)
        mod.decls.append(Raw(kw, name, full, span))
    return mod
