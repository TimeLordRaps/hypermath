"""Analysis: decide, per declaration, what can be translated and say why not."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field

from . import expr as ex
from . import parser
from .ast import Axiom, Close, Derive, Exists, Forall, Name, Num, Opaque, Primitive, Raw, Relation

BUILTIN_SORTS = {"Prop", "Type"}
LOGIC = {"=", "!="}


@dataclass
class Entry:
    kind: str
    name: str
    file: str
    line: int
    status: str  # translated | admitted | untranslated | builtin
    reason: str = ""
    decl: object = None
    expr: object = None  # the parsed statement, when there is one
    proof: tuple | None = None  # (axiom name, ((var, term_text), ...)) for a bare instantiation
    doc: str = ""


@dataclass
class Project:
    entries: list = field(default_factory=list)
    sigs: dict = field(default_factory=dict)
    infix: dict = field(default_factory=dict)
    sources: list = field(default_factory=list)  # (file, sha256)
    sorts: set = field(default_factory=set)


def _infer_sorts(e, free: list, sigs: dict):
    """Sort of each free variable, read off the parameter position it first occupies.

    Returns (sorts, None) or ({}, reason) when a variable occurs in no typed position or in
    two positions of different sorts: the translator never guesses a sort.
    """
    from .ast import And, App, Iff, Implies, Not, Or

    found: dict = {}
    clash: list = []

    def walk(x):
        if isinstance(x, App):
            sig = sigs.get(x.fn)
            for i, a in enumerate(x.args):
                if isinstance(a, Name) and a.name in free and sig and i < len(sig.params):
                    old = found.setdefault(a.name, sig.params[i])
                    if old != sig.params[i]:
                        clash.append(a.name)
                walk(a)
        elif isinstance(x, Not):
            walk(x.e)
        elif isinstance(x, (And, Or, Implies, Iff)):
            walk(x.left)
            walk(x.right)

    walk(e)
    if clash:
        return {}, f"variable {clash[0]!r} is used at two different sorts"
    missing = [n for n in free if n not in found]
    if missing:
        return {}, f"cannot infer a sort for variable {missing[0]!r}"
    return found, None


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def check_expr(e, sigs: dict, sorts: set, bound: frozenset = frozenset()) -> str | None:
    """None when every name resolves with the right arity, else the reason it does not."""
    from .ast import And, App, Iff, Implies, Not, Or

    if isinstance(e, Num):
        return "numerals are not supported"
    if isinstance(e, Name):
        if e.name in bound:
            return None
        sig = sigs.get(e.name)
        if sig is None:
            return f"name {e.name!r} is used but not declared in the source"
        if sig.params:
            return f"{e.name!r} has arity {len(sig.params)} but is used without arguments"
        return None
    if isinstance(e, App):
        if e.fn in LOGIC:
            return None if len(e.args) == 2 else f"{e.fn!r} needs two arguments"
        sig = sigs.get(e.fn)
        if sig is None and e.fn not in bound:
            return f"name {e.fn!r} is used but not declared in the source"
        if sig is not None and len(e.args) != len(sig.params):
            return f"arity mismatch: {e.fn!r} takes {len(sig.params)} argument(s), given {len(e.args)}"
        for a in e.args:
            r = check_expr(a, sigs, sorts, bound)
            if r:
                return r
        return None
    if isinstance(e, Not):
        return check_expr(e.e, sigs, sorts, bound)
    if isinstance(e, (And, Or, Implies, Iff)):
        return check_expr(e.left, sigs, sorts, bound) or check_expr(e.right, sigs, sorts, bound)
    if isinstance(e, (Forall, Exists)):
        for n, t in e.binders:
            if t not in sorts and t not in BUILTIN_SORTS:
                return f"binder {n!r} has undeclared sort {t!r}"
        inner = bound | {n for n, _ in e.binders}
        if e.guard is not None:
            r = check_expr(e.guard, sigs, sorts, inner)
            if r:
                return r
        return check_expr(e.body, sigs, sorts, inner)
    return f"unsupported expression {type(e).__name__}"


def _norm(text: str) -> str:
    return "".join(text.split())


def _instance_proof(d: Derive, entries_by_name: dict):
    """A bare instantiation: one step citing an axiom, whose result is the close."""
    if len(d.steps) != 1:
        return None
    s = d.steps[0]
    if not s.cites or not s.binds or s.result is None:
        return None
    ax = entries_by_name.get(s.cites)
    if ax is None or ax.kind != "axiom" or ax.status != "translated" or not isinstance(ax.expr, Forall):
        return None
    if {v for v, _ in s.binds} != {n for n, _ in ax.expr.binders} or ax.expr.guard is not None:
        return None
    if _norm(s.result) != _norm(d.close_text):
        return None
    order = [n for n, _ in ax.expr.binders]
    by = dict(s.binds)
    return (s.cites, tuple((n, by[n]) for n in order))


def analyze(files: list) -> Project:
    """`files` is [(path, text), ...] in dependency order (L0 before L1, ...)."""
    proj = Project()
    by_name: dict = {}
    for path, text in files:
        proj.sources.append((path, sha256(text)))
        mod = parser.parse(text, path, known=proj.sigs, infix=proj.infix)
        proj.sigs, proj.infix = mod.sigs, mod.infix
        for d in mod.decls:
            if isinstance(d, Primitive) and d.sig.result == "Type" and not d.sig.params:
                proj.sorts.add(d.name)
        proj.sorts |= BUILTIN_SORTS
        for d in mod.decls:
            e = _entry(d, proj, by_name)
            proj.entries.append(e)
            by_name.setdefault(e.name, e)
    return proj


def _entry(d, proj: Project, by_name: dict) -> Entry:
    span = d.span
    base = dict(file=span.file, line=span.line, decl=d, doc=getattr(d, "doc", ""))
    if isinstance(d, (Primitive, Opaque, Relation)):
        kind = type(d).__name__.lower()
        if isinstance(d, Primitive) and d.name == "Prop" and d.sig.result == "Type":
            return Entry(kind, d.name, status="builtin", reason="Prop is built in to the targets", **base)
        bad = [t for t in (*d.sig.params, d.sig.result) if t not in proj.sorts and t not in BUILTIN_SORTS]
        if bad:
            return Entry(kind, d.name, status="untranslated",
                         reason=f"signature mentions undeclared sort {bad[0]!r}", **base)
        return Entry(kind, d.name, status="translated", **base)
    if isinstance(d, Axiom):
        if d.error:
            reason = d.error
            if "comments only" in reason:
                reason = "the statement is in comments only; the block has no code"
            return Entry("axiom", d.name, status="untranslated", reason=reason, **base)
        why = check_expr(d.body, proj.sigs, proj.sorts)
        if why:
            return Entry("axiom", d.name, status="untranslated", reason=why, **base)
        return Entry("axiom", d.name, status="translated", expr=d.body, **base)
    if isinstance(d, Derive):
        if not d.close_text.strip():
            return Entry("derive", d.name, status="untranslated", reason="the block has no `close:` statement", **base)
        try:
            body = ex.parse_statement(d.close_text, proj.infix, {n: len(s.params) for n, s in proj.sigs.items()})
        except ex.ExprError as err:
            return Entry("derive", d.name, status="untranslated",
                         reason=f"`close: {d.close_text.strip()}` is not a proposition in the translatable fragment: {err}", **base)
        why = check_expr(body, proj.sigs, proj.sorts)
        if why:
            return Entry("derive", d.name, status="untranslated",
                         reason=f"`close:` is not a proposition in the declared vocabulary: {why}", **base)
        return Entry("derive", d.name, status="admitted", expr=body,
                     proof=_instance_proof(d, by_name), **base)
    if isinstance(d, Close):
        name = f"close-{d.target}"
        if not d.body_text.strip():
            return Entry("close", name, status="untranslated",
                         reason="the semantic content is in comments only; the block has no code", **base)
        try:
            body = ex.parse_statement(d.body_text, proj.infix, {n: len(s.params) for n, s in proj.sigs.items()})
        except ex.ExprError as err:
            return Entry("close", name, status="untranslated",
                         reason=f"the close is stated in prose, not as a formula: {err}", **base)
        free = sorted(n for n in ex.free_names(body) if n not in proj.sigs)
        sorts, why = _infer_sorts(body, free, proj.sigs)
        if why is None:
            why = check_expr(body, proj.sigs, proj.sorts, frozenset(free))
        if why:
            return Entry("close", name, status="untranslated",
                         reason=f"the close formula is not in the declared vocabulary: {why}", **base)
        stmt = Forall(tuple((n, sorts[n]) for n in free), None, body) if free else body
        return Entry("close", name, status="translated", expr=stmt, **base)
    if isinstance(d, Raw):
        why = {"graduation": "graduation criteria are meta-level statements about layers, not formulas"}.get(
            d.kind, f"`{d.kind}` blocks are not modelled by the translator")
        return Entry(d.kind, d.name, status="untranslated", reason=why, **base)
    return Entry("unknown", getattr(d, "name", "?"), status="untranslated", reason="unrecognised node", **base)
