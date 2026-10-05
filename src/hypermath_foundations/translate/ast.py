"""Syntax tree for the translatable fragment of `.hm`, plus carriers for the rest."""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Span:
    file: str
    line: int  # 1-based, first line of the declaration


@dataclass(frozen=True)
class Sig:
    """`A -> B -> C` is params (A, B), result C. A constant has no params."""

    params: tuple[str, ...]
    result: str


# ------------------------------------------------------------------ expressions


@dataclass(frozen=True)
class Name:
    name: str


@dataclass(frozen=True)
class Num:
    value: int


@dataclass(frozen=True)
class App:
    fn: str
    args: tuple


@dataclass(frozen=True)
class Not:
    e: object


@dataclass(frozen=True)
class And:
    left: object
    right: object


@dataclass(frozen=True)
class Or:
    left: object
    right: object


@dataclass(frozen=True)
class Implies:
    left: object
    right: object


@dataclass(frozen=True)
class Iff:
    left: object
    right: object


@dataclass(frozen=True)
class Forall:
    binders: tuple  # ((name, type), ...)
    guard: object | None
    body: object


@dataclass(frozen=True)
class Exists:
    binders: tuple
    guard: object | None
    body: object


# ----------------------------------------------------------------- declarations


@dataclass(frozen=True)
class Primitive:
    name: str
    sig: Sig
    doc: str
    span: Span


@dataclass(frozen=True)
class Opaque:
    name: str
    sig: Sig
    doc: str
    span: Span


@dataclass(frozen=True)
class Relation:
    name: str
    sig: Sig
    symbol: str | None
    doc: str
    span: Span


@dataclass(frozen=True)
class Axiom:
    name: str
    body: object | None
    error: str | None  # why the body could not be parsed; None when it was
    doc: str
    span: Span
    text: str = ""


@dataclass(frozen=True)
class Step:
    n: int
    text: str
    cites: str | None = None
    binds: tuple = ()  # ((var, term_text), ...)
    result: str | None = None


@dataclass(frozen=True)
class Derive:
    name: str
    status: str
    steps: tuple
    close_text: str
    doc: str
    span: Span


@dataclass(frozen=True)
class Close:
    target: str
    via: str  # the relation named by `as`, or the language named by `in`
    status: str | None
    body_text: str  # code lines only; "" when the block holds comments alone
    doc: str
    span: Span

    @property
    def name(self) -> str:
        return self.target


@dataclass(frozen=True)
class Raw:
    """Anything the translator does not model. Kept verbatim, never dropped."""

    kind: str
    name: str
    text: str
    span: Span


@dataclass
class Module:
    file: str
    decls: list = field(default_factory=list)
    infix: dict = field(default_factory=dict)  # relation symbol -> relation name
    sigs: dict = field(default_factory=dict)  # declared name -> Sig, including inherited ones
