"""Metamath emitter (a deliberately small, independently checkable subset).

What it states: the typed vocabulary (sorts, function symbols, relations, connectives),
every translated axiom whose only quantifier is the outermost `for-all` (Metamath's free
variables are implicitly universal; a `where` guard becomes an antecedent), and every
derive that is a bare instantiation of such an axiom, with a real substitution proof.

What it does NOT state: logical axioms. The database has no inference rules for the
connectives, so a Metamath-verified derive certifies sort/arity correctness and the
instantiation, nothing about logic. Statements with nested quantifiers are omitted with
a reason rather than approximated. Admitted (unproved) derives are omitted: Metamath
has no `sorry` that mmverify accepts.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from . import expr as ex
from .ast import And, App, Exists, Forall, Iff, Implies, Name, Not, Opaque, Or, Primitive, Relation

CONN = {Not: ("wn", "-.", 1), And: ("wa", "/\\", 2), Or: ("wo", "\\/", 2),
        Implies: ("wi", "->", 2), Iff: ("wb", "<->", 2)}


class Omit(Exception):
    pass


def v(name: str, sort: str) -> str:
    return f"{name}@{sort}"


class Builder:
    def __init__(self, proj):
        self.proj = proj
        self.sorts = {e.name for e in proj.entries if e.kind == "primitive" and e.decl.sig.result == "Type"}
        self.vars: dict[str, str] = {}  # symbol -> sort ("wff" for scheme vars), declaration order
        self.consts: list[str] = []
        self.sig = {n: s for n, s in proj.sigs.items()}

    def var(self, name: str, sort: str) -> str:
        sym = v(name, sort)
        self.vars.setdefault(sym, sort)
        return sym

    # statements ------------------------------------------------------------
    def term(self, e, env: dict) -> str:
        if isinstance(e, Name):
            if e.name in env:
                return self.var(e.name, env[e.name])
            return e.name
        if isinstance(e, App):
            if e.fn in ("=", "!="):
                raise Omit("equality")
            return "( " + " ".join([e.fn] + [self.term(a, env) for a in e.args]) + " )" if e.args else e.fn
        raise Omit(f"not a term: {type(e).__name__}")

    def wff(self, e, env: dict) -> str:
        if isinstance(e, App):
            if e.fn == "=":
                return f"( {self.term(e.args[0], env)} = {self.term(e.args[1], env)} )"
            if e.fn == "!=":
                return f"( -. ( {self.term(e.args[0], env)} = {self.term(e.args[1], env)} ) )"
            return self.term(e, env)
        if isinstance(e, Name):
            return e.name
        if type(e) in CONN:
            _, sym, n = CONN[type(e)]
            kids = [e.e] if n == 1 else [e.left, e.right]
            return "( " + (sym + " " if n == 1 else "") + (f" {sym} ".join(self.wff(k, env) for k in kids) if n == 2
                                                           else self.wff(kids[0], env)) + " )"
        raise Omit("nested quantifier" if isinstance(e, (Forall, Exists)) else type(e).__name__)

    def statement(self, e) -> tuple[str, dict]:
        env: dict = {}
        if isinstance(e, Forall):
            env = dict(e.binders)
            body = self.wff(e.body, env)
            if e.guard is not None:
                body = f"( {self.wff(e.guard, env)} -> {body} )"
            return body, env
        return self.wff(e, env), env


def build(proj) -> tuple[str, dict]:
    """Return (database text, {entry_index: "stated"|"proved"|reason-omitted})."""
    b = Builder(proj)
    status: dict[int, str] = {}
    body: list[str] = []
    labels: dict[str, str] = {}  # symbol -> syntax-axiom label

    def sorts_of(sig):
        return list(sig.params), sig.result

    def syntax_axiom(name, sig):
        params, res = sorts_of(sig)
        label = f"sy.{name}"
        labels[name] = label
        names = []
        for i, p in enumerate(params):
            sym = b.var(f"a{i}", p)
            names.append(sym)
        shown = "( " + " ".join([name] + names) + " )" if names else name
        typecode = "wff" if res == "Prop" else res
        body.append(f"{label} $a {typecode} {shown} $.")

    consts = ["wff", "|-", "(", ")", "=", "-.", "->", "/\\", "\\/", "<->"]
    for idx, e in enumerate(proj.entries):
        d = e.decl
        if e.status not in ("translated", "admitted"):
            continue
        if isinstance(d, Primitive) and d.sig.result == "Type" and not d.sig.params:
            consts.append(d.name)
            status[idx] = "stated"
        elif isinstance(d, (Primitive, Opaque, Relation)):
            if d.name not in consts:
                consts.append(d.name)
            for s in (*d.sig.params, d.sig.result):
                if s not in ("Prop", "Type") and s not in consts:
                    consts.append(s)
            syntax_axiom(d.name, d.sig)
            status[idx] = "stated"
    for sort in sorted(b.sorts):
        if sort not in consts:
            consts.append(sort)
        sym1, sym2 = b.var("p", sort), b.var("q", sort)
        body.append(f"weq.{sort} $a wff ( {sym1} = {sym2} ) $.")
    wv = ["ph@wff", "ps@wff"]
    for s in wv:
        b.vars.setdefault(s, "wff")
    for lbl, sym, n in CONN.values():
        body.append(f"{lbl} $a wff ( {sym} {'ph@wff' if n == 1 else 'ph@wff ' + sym + ' ps@wff'} ) $.")
    # statements
    stated: dict[str, tuple] = {}  # axiom name -> (label, env, ordered vars)
    for idx, e in enumerate(proj.entries):
        if e.kind not in ("axiom", "close") or e.status != "translated":
            continue
        try:
            stmt, env = b.statement(e.expr)
        except Omit as o:
            status[idx] = f"omitted: {o}"
            continue
        label = f"ax.{e.name}"
        body.append(f"{label} $a |- {stmt} $.")
        stated[e.name] = (label, env, stmt)
        status[idx] = "stated"
    # header with every variable declared once, before any use
    head = ["$c " + " ".join(consts) + " $."]
    ordered = list(b.vars)
    if ordered:
        head.append("$v " + " ".join(ordered) + " $.")
    for sym in ordered:
        head.append(f"f.{sym.replace(chr(64), chr(46))} $f {b.vars[sym]} {sym} $.")
    base = "\n".join(head + body) + "\n"
    return base, {"stated": stated, "status": status, "vars": ordered, "b": b}


def _term_proof(e, env, ctx) -> list[str]:
    if isinstance(e, Name):
        if e.name in env:
            raise Omit("free variable in instance")
        return [f"sy.{e.name}"]
    if isinstance(e, App):
        out = []
        for a in e.args:
            out += _term_proof(a, env, ctx)
        return out + [f"sy.{e.fn}"]
    raise Omit("not a term")


def instance_proofs(proj, ctx) -> dict[int, str]:
    """`$p` lines for derives that are bare instantiations of a stated axiom."""
    arities = {n: len(s.params) for n, s in proj.sigs.items()}
    b: Builder = ctx["b"]
    out: dict[int, str] = {}
    for idx, e in enumerate(proj.entries):
        if e.kind != "derive" or e.status != "admitted" or e.proof is None:
            continue
        ax_name, binds = e.proof
        if ax_name not in ctx["stated"]:
            continue
        label, env, stmt = ctx["stated"][ax_name]
        ent = {a.name: a for a in proj.entries if a.name == ax_name and a.kind == "axiom"}[ax_name]
        if ent.expr.guard is not None:
            continue
        given = dict(binds)
        try:
            if set(given) != set(env):
                raise Omit("binders differ")
            subst = {n: ex.parse_expr(given[n], proj.infix, arities) for n in env}
            # mandatory hypotheses are the $f of the axiom's variables, in global order
            used = [s for s in ctx["vars"] if s in {v(n, env[n]) for n in env} and f" {s} " in f" {stmt} "]
            proof: list[str] = []
            for sym in used:
                name = sym.rsplit("@", 1)[0]
                proof += _term_proof(subst[name], {}, ctx)
            # the claimed statement, rendered with the same renderer
            goal = _subst_stmt(e.expr, b)
            out[idx] = f"th.{e.name} $p |- {goal} $= {' '.join(proof + [label])} $."
        except (Omit, ex.ExprError):
            continue
    return out


def _subst_stmt(expr, b: Builder) -> str:
    return b.wff(expr, {})


def verify(text: str, mmverify: str, timeout: int = 120) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "out.mm"
        p.write_text(text, encoding="utf-8")
        r = subprocess.run([sys.executable, mmverify, str(p)], capture_output=True, text=True, timeout=timeout)
    return r.returncode == 0 and "error" not in (r.stdout + r.stderr).lower(), r.stdout + r.stderr


def emit_checked(proj, mmverify: str) -> tuple[str, dict]:
    """Database with each derive kept only if mmverify accepts it; returns (text, status)."""
    base, ctx = build(proj)
    ok, log = verify(base, mmverify)
    if not ok:
        raise RuntimeError("base database rejected by mmverify:\n" + log[-2000:])
    keep = []
    for idx, line in instance_proofs(proj, ctx).items():
        good, msg = verify(base + line + "\n", mmverify)
        ctx["status"][idx] = "proved" if good else f"rejected by mmverify: {msg.strip().splitlines()[-1] if msg.strip() else ''}"
        if good:
            keep.append(line)
    for idx, e in enumerate(proj.entries):
        if e.kind == "derive" and idx not in ctx["status"]:
            ctx["status"][idx] = "omitted: not a bare instantiation of a stated axiom" if e.status == "admitted" else "omitted"
    text = base + "\n".join(keep) + ("\n" if keep else "")
    ok, log = verify(text, mmverify)
    if not ok:
        raise RuntimeError("final database rejected by mmverify:\n" + log[-2000:])
    return text, ctx["status"]
