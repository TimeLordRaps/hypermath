"""Expressions of the typed fragment: a small Pratt parser with located errors."""

from __future__ import annotations

import re

from .ast import And, App, Exists, Forall, Iff, Implies, Name, Not, Num, Or

KEYWORDS = {"for-all", "exists", "where", "and", "or", "not", "implies", "iff", "plus"}
SYMBOLS = ["<->", "->", ":=", "::", "~~", "=~", "==", "<=", ">=", "!=", "|-"]
SINGLE = "(),:=+*^<>[].|"
RELOPS = {"~~", "=~", "==", "=", "!="}


class ExprError(ValueError):
    def __init__(self, message: str, pos: int = 0):
        super().__init__(f"{message} (at column {pos})")
        self.pos = pos


_IDENT_START = re.compile(r"[A-Za-z_□]")
_IDENT_CHAR = re.compile(r"[A-Za-z0-9_'□]")


def tokenize(text: str):
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if _IDENT_START.match(c):
            j = i + 1
            while j < n:
                if _IDENT_CHAR.match(text[j]):
                    j += 1
                elif text[j] == "-" and j + 1 < n and _IDENT_CHAR.match(text[j + 1]):
                    j += 1  # a hyphen inside a name; `->` is never swallowed
                else:
                    break
            toks.append(("ident", text[i:j], i))
            i = j
            continue
        if c.isdigit():
            j = i
            while j < n and text[j].isdigit():
                j += 1
            toks.append(("num", text[i:j], i))
            i = j
            continue
        for s in SYMBOLS:
            if text.startswith(s, i):
                toks.append(("sym", s, i))
                i += len(s)
                break
        else:
            if c in SINGLE:
                toks.append(("sym", c, i))
                i += 1
            else:
                raise ExprError(f"unexpected character {c!r}", i)
    toks.append(("eof", "", n))
    return toks


class _P:
    def __init__(self, text: str, infix: dict, arities: dict | None = None):
        self.toks, self.i, self.infix = tokenize(text), 0, infix
        self.arities = arities or {}

    @property
    def tok(self):
        return self.toks[self.i]

    def at(self, kind: str, value: str | None = None) -> bool:
        t = self.tok
        return t[0] == kind and (value is None or t[1] == value)

    def at_kw(self, word: str) -> bool:
        return self.at("ident", word)

    def eat(self, kind: str, value: str | None = None):
        if not self.at(kind, value):
            raise ExprError(f"expected {value or kind}, found {self.tok[1] or 'end of text'!r}", self.tok[2])
        t = self.tok
        self.i += 1
        return t

    # grammar -----------------------------------------------------------------
    def expr(self):
        if self.at_kw("for-all") or self.at_kw("exists"):
            return self.quant()
        return self.iff()

    def iff(self):
        left = self.implies()
        if self.at("sym", "<->") or self.at_kw("iff"):
            self.i += 1
            return Iff(left, self.iff())
        return left

    def implies(self):
        left = self.or_()
        if self.at("sym", "->") or self.at_kw("implies"):
            self.i += 1
            return Implies(left, self.implies())
        return left

    def or_(self):
        left = self.and_()
        while self.at_kw("or"):
            self.i += 1
            left = Or(left, self.and_())
        return left

    def and_(self):
        left = self.not_()
        while self.at_kw("and"):
            self.i += 1
            left = And(left, self.not_())
        return left

    def not_(self):
        if self.at_kw("not"):
            self.i += 1
            return Not(self.not_())
        return self.rel()

    def rel(self):
        left = self.add()
        if self.tok[0] == "sym" and self.tok[1] in RELOPS:
            op = self.tok[1]
            self.i += 1
            right = self.add()
            fn = self.infix.get(op, op)
            return App(fn, (left, right))
        return left

    def add(self):
        left = self.app()
        while self.at_kw("plus"):
            self.i += 1
            left = App("plus", (left, self.app()))
        return left

    def app(self):
        t = self.tok
        if t[0] == "ident" and t[1] in KEYWORDS - {"for-all", "exists"}:
            raise ExprError(f"unexpected keyword {t[1]!r}", t[2])
        if t[0] == "ident" and t[1] in ("for-all", "exists"):
            return self.quant()
        if t[0] == "num":
            self.i += 1
            return Num(int(t[1]))
        if self.at("sym", "("):
            self.i += 1
            e = self.expr()
            self.eat("sym", ")")
            return e
        if t[0] != "ident":
            raise ExprError(f"unexpected {t[1] or 'end of text'!r}", t[2])
        self.i += 1
        arity = self.arities.get(t[1], 0)
        if self.at("sym", "("):
            mark = self.i
            call = self._call(t[1])
            if arity < 2 or len(call.args) == arity:
                return call
            self.i = mark  # `compose (compose p q) r`: the parens were an argument, not a call
        if arity > 0 and self._starts_atom():
            # juxtaposition, resolved only because the name's declared arity says
            # how many arguments follow.
            args = []
            for _ in range(arity):
                if not self._starts_atom():
                    raise ExprError(f"{t[1]!r} has declared arity {arity} but only {len(args)} "
                                    f"argument(s) were given", t[2])
                args.append(self._atom_arg())
            return App(t[1], tuple(args))
        if self._starts_atom():
            raise ExprError(f"{t[1]!r} is applied by juxtaposition but has no declared arity", t[2])
        return Name(t[1])

    def _starts_atom(self) -> bool:
        t = self.tok
        return (t[0] == "ident" and t[1] not in KEYWORDS) or t[0] == "num" or (t[0] == "sym" and t[1] == "(")

    def _atom_arg(self):
        if not self._starts_atom():
            raise ExprError(f"expected an argument, found {self.tok[1] or 'end of text'!r}", self.tok[2])
        t = self.tok
        if t[0] == "num":
            self.i += 1
            return Num(int(t[1]))
        if t[1] == "(":
            self.i += 1
            e = self.expr()
            self.eat("sym", ")")
            return e
        self.i += 1
        # `p (q r)` after a juxtaposed head: `p` is a variable and the paren opens the
        # next argument, unless `p` is itself a declared function.
        if self.at("sym", "(") and self.arities.get(t[1], 0) > 0:
            return self._call(t[1])
        return Name(t[1])

    def _call(self, fn: str):
        args = ()
        while self.at("sym", "("):
            self.i += 1
            group = []
            if not self.at("sym", ")"):
                group.append(self.expr())
                while self.at("sym", ","):
                    self.i += 1
                    group.append(self.expr())
            self.eat("sym", ")")
            args += tuple(group)  # step(x)(y) flattens to step(x, y)
        return App(fn, args)

    def binders(self):
        out = []
        if self.at("sym", "("):
            while self.at("sym", "("):
                self.i += 1
                out.extend(self._names_and_type())
                self.eat("sym", ")")
        else:
            out.extend(self._names_and_type())
        return tuple(out)

    def _names_and_type(self):
        names = []
        while self.tok[0] == "ident" and self.tok[1] not in KEYWORDS:
            names.append(self.tok[1])
            self.i += 1
        if not names:
            raise ExprError("expected a bound name", self.tok[2])
        self.eat("sym", "::")
        ty = self.eat("ident")[1]
        return [(n, ty) for n in names]

    def quant(self):
        kind = self.eat("ident")[1]
        binders = self.binders()
        guard = None
        if self.at_kw("where"):
            self.i += 1
            guard = self.expr()
            # `exists x :: T where P` is the common spelling of "exists x. P": with
            # nothing after the clause, the clause is the body.
            if kind == "exists" and (self.at("eof") or self.at("sym", ")")):
                return Exists(binders, None, guard)
        if self.at("sym", ":") or self.at("sym", ","):
            self.i += 1
        body = self.expr()
        return (Forall if kind == "for-all" else Exists)(binders, guard, body)


def parse_expr(text: str, infix: dict | None = None, arities: dict | None = None):
    p = _P(text, infix or {}, arities)
    e = p.expr()
    if not p.at("eof"):
        raise ExprError(f"unexpected {p.tok[1]!r}", p.tok[2])
    return e


def parse_statement(text: str, infix: dict | None = None, arities: dict | None = None):
    """An expression, optionally followed by a postfix `for-all x y :: T` binder."""
    p = _P(text, infix or {}, arities)
    e = p.expr()
    if p.at_kw("for-all"):
        p.i += 1
        binders = p.binders()
        e = Forall(binders, None, e)
    if not p.at("eof"):
        raise ExprError(f"unexpected {p.tok[1]!r}", p.tok[2])
    return e


def parse_axiom_body(text: str, infix: dict | None = None, arities: dict | None = None):
    """Whole body as one statement, else one statement per line, joined by `and`."""
    try:
        return parse_statement(text, infix, arities)
    except ExprError as whole:
        lines = [ln for ln in text.splitlines() if ln.strip()]
        if len(lines) < 2:
            raise whole
        parts = []
        for ln in lines:
            try:
                parts.append(parse_statement(ln, infix, arities))
            except ExprError:
                raise whole
        body = parts[0]
        for q in parts[1:]:
            body = And(body, q)
        return body


def free_names(e, bound: frozenset = frozenset()) -> set:
    if isinstance(e, Name):
        return set() if e.name in bound else {e.name}
    if isinstance(e, Num):
        return set()
    if isinstance(e, App):
        out = set() if e.fn in bound else {e.fn}
        for a in e.args:
            out |= free_names(a, bound)
        return out
    if isinstance(e, Not):
        return free_names(e.e, bound)
    if isinstance(e, (And, Or, Implies, Iff)):
        return free_names(e.left, bound) | free_names(e.right, bound)
    if isinstance(e, (Forall, Exists)):
        inner = bound | {n for n, _ in e.binders}
        out = free_names(e.body, inner)
        if e.guard is not None:
            out |= free_names(e.guard, inner)
        return out
    raise TypeError(f"not an expression: {e!r}")
