"""Independent Python check of lean4/RecursionRescue.lean's table and of the search that found it.

The model (f2f, congruence classes) is parsed from the reviewed lean4/FiniteActionCountermodel.lean and the
table (ordinalApplyRec) from lean4/RecursionRescue.lean, so the check evaluates the very definitions the
Lean kernel accepted, with a different mechanism. It does not replace the kernel proof.
"""
import re
from itertools import product
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1] / "lean4"
FORMS = ["a0", "a1", "a2", "b0", "b1", "b2"]


def _block(text: str, header: str) -> str:
    start = text.index(header)
    end = text.find("\n\n", start)
    return text[start:end if end != -1 else len(text)]


def _model():
    src = (LEAN / "FiniteActionCountermodel.lean").read_text(encoding="utf-8")
    f2f = dict(re.findall(r"\| \.(\w+) => \.(\w+)", _block(src, "def f2f : Form")))
    cls = {k: int(v) for k, v in re.findall(r"\| \.(\w+) => (\d+)", _block(src, "def congruenceClass"))}
    assert set(f2f) == set(cls) == set(FORMS)
    return f2f, cls


def _table():
    src = (LEAN / "RecursionRescue.lean").read_text(encoding="utf-8")
    block = _block(src, "def ordinalApplyRec")
    table = {(p, x): r for p, x, r in re.findall(r"\| \.(\w+), \.(\w+) => \.(\w+)", block)}
    for p, r in re.findall(r"\| \.(\w+), _ => \.(\w+)", block):
        for x in FORMS:
            table[(p, x)] = r
    assert len(table) == 36
    return table


def _iterate(f2f, n, x):
    for _ in range(n):
        x = f2f[x]
    return x


def _claims(f2f, cls, g):
    zero = all(cls[g[("a0", x)]] == cls[x] for x in FORMS)
    succ = all(cls[g[(f2f[p], x)]] == cls[f2f[g[(p, x)]]] for p in FORMS for x in FORMS)
    length = {n: _iterate(f2f, n, "a0") for n in range(24)}
    path = all(
        cls[length[p + q]] == cls[g[(length[q], length[p])]] for p in range(12) for q in range(12)
    )
    return zero, succ, path


def test_the_table_in_the_lean_file_satisfies_the_three_claims():
    f2f, cls = _model()
    assert _claims(f2f, cls, _table()) == (True, True, True)


def test_the_constant_interpretation_of_the_countermodel_violates_the_zero_identity():
    f2f, cls = _model()
    constant = {(p, x): "a0" for p in FORMS for x in FORMS}
    zero, _succ, _path = _claims(f2f, cls, constant)
    assert not zero


def test_a_single_wrong_table_entry_is_rejected():
    f2f, cls = _model()
    table = _table()
    table[("a1", "a1")] = "a1" if table[("a1", "a1")] != "a1" else "a2"
    assert _claims(f2f, cls, table) != (True, True, True)


def test_exhaustive_search_counts_and_joint_satisfiability():
    f2f, cls = _model()
    per_x = {}
    for x in FORMS:
        sols = []
        for vals in product(FORMS, repeat=6):
            g = dict(zip(FORMS, vals))
            if cls[g["a0"]] == cls[x] and all(cls[g[f2f[p]]] == cls[f2f[g[p]]] for p in FORMS):
                sols.append(g)
        per_x[x] = sols
    assert {x: len(s) for x, s in per_x.items()} == {
        "a0": 12, "a1": 24, "a2": 12, "b0": 12, "b1": 24, "b2": 12}
    chain = sorted({_iterate(f2f, p, "a0") for p in range(12)})
    found = False
    for combo in product(*(per_x[x] for x in chain)):
        g = dict(zip(chain, combo))
        if all(
            cls[_iterate(f2f, p + q, "a0")] == cls[g[_iterate(f2f, p, "a0")][_iterate(f2f, q, "a0")]]
            for p in range(12) for q in range(12)
        ):
            found = True
            break
    assert found
