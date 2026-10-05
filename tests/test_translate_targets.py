import os
import re
from pathlib import Path

import pytest

from hypermath_foundations.translate import lean, metamath, project, receipt

L0 = """\
primitive Form :: Type
primitive ground :: Form
primitive apply :: Form -> Form
opaque struct-distinct :: Form -> Form -> Prop
relation Similar :: Form -> Form -> Prop   -- (~~)

axiom ax-diff:
    for-all x :: Form:
        struct-distinct(apply(x), ground)

axiom ax-guarded:
    for-all x :: Form where struct-distinct(x, ground):
        x ~~ x

axiom ax-nested:
    for-all x :: Form:
        exists y :: Form: struct-distinct(x, y)

derive d-inst as FORM:
    step 1: ax-diff with x := ground
            -> struct-distinct(apply(ground), ground)
    close: struct-distinct(apply(ground), ground)

derive d-unproved as FORM:
    step 1: ax-diff with x := ground
            -> struct-distinct(apply(ground), ground)
    step 2: ax-diff with x := apply(ground)
            -> struct-distinct(apply(apply(ground)), ground)
    close: struct-distinct(apply(ground), ground)
"""


REPO = Path(__file__).resolve().parents[1]
LAYERS = ["L0_ground.hm", "L1_relations.hm", "L2_operations.hm", "L3_ordinatics.hm"]


def lean_bin():
    """Kernel tests run only when HM_LEAN names a `lean` binary; otherwise they skip."""
    return os.environ.get("HM_LEAN") or None


def mm_tool():
    return os.environ.get("HM_MMVERIFY")


def proj():
    return project.analyze([("l0.hm", L0)])


def test_lean_text_follows_hypermath_conventions():
    t = lean.emit(proj()).text
    assert "axiom Form : Type" in t and "axiom f2f : Form → Form" in t  # apply -> f2f
    assert "axiom structDistinct : Form → Form → Prop" in t
    assert 'scoped notation:50 a " ~~ " b => Similar a b' in t
    assert "axiom axDiff : ∀ (x : Form), structDistinct (f2f x) ground" in t
    assert "theorem dInst : structDistinct (f2f ground) ground :=\n  axDiff ground" in t
    assert "theorem dUnproved" in t and "by sorry" in t  # two steps: admitted, not proved


def test_vocabulary_is_emitted_before_statements_that_use_it():
    src = "axiom a1:\n    for-all x :: Form:\n        later(x)\nprimitive Form :: Type\nopaque later :: Form -> Prop\n"
    t = lean.emit(project.analyze([("f.hm", src)])).text
    assert t.index("axiom later") < t.index("axiom a1")


def test_rendering_is_precedence_correct():
    src = ("primitive Form :: Type\nopaque p :: Form -> Prop\nopaque q :: Form -> Prop\n"
           "axiom a:\n    for-all x :: Form:\n        (p(x) or q(x)) and not p(x)\n")
    t = lean.emit(project.analyze([("f.hm", src)])).text
    assert "(p x ∨ q x) ∧ ¬ (p x)" in t


@pytest.mark.skipif(not lean_bin(), reason="HM_LEAN is unset")
def test_kernel_accepts_fixture_output_and_rejects_a_broken_one():
    p = proj()
    out, log = lean.kernel_check(p, lean_bin())
    code, errs, _ = lean.run_lean(out.text, lean_bin())
    assert code == 0 and not errs
    broken = out.text.replace("structDistinct (f2f x) ground", "structDistinct (f2f x) nonsense")
    code, errs, _ = lean.run_lean(broken, lean_bin())
    assert code != 0 and errs  # the oracle can say no


@pytest.mark.skipif(not lean_bin(), reason="HM_LEAN is unset")
def test_bad_instance_proof_falls_back_to_sorry_not_to_silent_acceptance():
    p = proj()
    e = next(e for e in p.entries if e.name == "d-inst")
    e.proof = ("ax-diff", (("x", "apply(ground)"),))  # wrong instance for the stated close
    out, log = lean.kernel_check(p, lean_bin())
    assert ("proof->sorry", p.entries.index(e), log[0][2]) in log
    assert "theorem dInst : structDistinct (f2f ground) ground :=\n  by sorry" in out.text


@pytest.mark.skipif(not mm_tool(), reason="HM_MMVERIFY is unset")
def test_metamath_subset_is_verified_and_honest_about_omissions():
    text, st = metamath.emit_checked(proj(), mm_tool())
    names = {proj().entries[i].name: s for i, s in st.items()}
    assert names["d-inst"] == "proved"
    assert names["ax-nested"].startswith("omitted: nested quantifier")
    assert names["d-unproved"].startswith("omitted")
    assert "th.d-inst $p" in text and "th.d-unproved" not in text


@pytest.mark.skipif(not mm_tool(), reason="HM_MMVERIFY is unset")
def test_mmverify_rejects_a_wrong_theorem():
    text, _ = metamath.emit_checked(proj(), mm_tool())
    bad = text.replace("th.d-inst $p |- ( struct-distinct ( apply ground ) ground )",
                       "th.d-inst $p |- ( struct-distinct ground ground )")
    ok, _ = metamath.verify(bad, mm_tool())
    assert not ok


def test_receipt_is_deterministic_and_self_hashed():
    p = proj()
    a = receipt.build(p, None, [], None, None, None, None)
    b = receipt.build(proj(), None, [], None, None, None, None)
    assert a == b and len(a["receipt_sha256"]) == 64
    assert a["counts"]["axiom/translated"] == 3 and a["counts"]["derive/admitted"] == 2
    assert any("fidelity" in g for g in a["guarantees"])


# -- differential against the hand-written mechanization (L0 only) -------------------

HAND = REPO / "lean4" / "Hypermath" / "L0Ground.lean"


def test_l0_vocabulary_and_axioms_match_the_hand_written_lean():
    src = (REPO / "L0_ground.hm").read_text(encoding="utf-8")
    t = lean.emit(project.analyze([("L0_ground.hm", src)])).text
    sig = lambda s: dict(re.findall(r"^axiom (\w+) : (.+)$", s, re.M))  # noqa: E731
    ours, hand = sig(t), sig(HAND.read_text(encoding="utf-8"))
    # every vocabulary declaration we generate for L0 exists in the hand-written file
    # with the identical type (the hand file adds §VIII+ material we do not generate).
    for name in ("Form", "ground", "f2f", "structDistinct", "structContinues", "structOrbits",
                 "Similar", "Congruent", "Simulation"):
        assert ours[name] == hand[name], name
    for name in ("axDiff", "axSim", "axBox", "axGroundSelf"):
        assert ours[name].replace("∀ (x : Form),", "∀ x : Form,") == hand[name], name


def test_translated_close_becomes_a_named_lean_axiom_and_a_metamath_statement():
    src = L0 + "\nclose struct-distinct as not-simulation:\n    struct-distinct(x, y) <-> not (x == y)\n"
    src = src.replace("relation Similar :: Form -> Form -> Prop   -- (~~)", "relation Similar :: Form -> Form -> Prop   -- (~~)\nrelation Simulation :: Form -> Form -> Prop   -- (==)")
    p = project.analyze([("l0.hm", src)])
    t = lean.emit(p).text
    assert "axiom closeStructDistinct : ∀ (x : Form) (y : Form), structDistinct x y ↔ ¬ (Simulation x y)" in t
    assert t.count("axiom structDistinct :") == 1  # the close must not shadow the predicate
    base, ctx = metamath.build(p)
    assert "ax.close-struct-distinct $a |-" in base


def test_lint_groups_undeclared_words_with_locations():
    from hypermath_foundations.translate import lint
    src = L0 + "\naxiom ax-bad:\n    for-all x :: Form:\n        struct-distinct(mystery(x), ground)\n"
    rep = lint.lint(project.analyze([("l0.hm", src)]))
    assert "mystery" in rep["undeclared_words"]
    assert rep["undeclared_words"]["mystery"][0][3] == "ax-bad"
    assert "mystery" in lint.format_report(rep)


def test_lint_separates_references_to_other_blocks_from_undeclared_operations():
    from hypermath_foundations.translate import lint
    src = L0 + "\nderive d-ref as FORM:\n    step 1: ax-diff with x := ground\n            -> struct-distinct(apply(ground), ground)\n    close: d-inst\n"
    src = src.replace("derive d-ref", "derive d-inst as FORM:\n    step 1: ax-diff with x := ground\n            -> struct-distinct(apply(ground), ground)\n    close: struct-distinct(apply(ground), ground)\nderive d-ref")
    rep = lint.lint(project.analyze([("l0.hm", src)]))
    assert "d-inst" in rep["close_names_a_block"] and "d-inst" not in rep["undeclared_words"]


def test_drift_reads_sorry_from_lean_text():
    from hypermath_foundations.translate import drift
    p = proj()
    lean_txt = ("theorem dInst : True := trivial\n\n"
                "-- a comment mentioning sorry\n"
                "theorem dUnproved : True := by\n  sorry\n")
    rows = {r["derive"]: r for r in drift.drift(p, [lean_txt])}
    assert rows["d-inst"]["lean"] == "proved" and not rows["d-inst"]["disagrees"]
    assert rows["d-unproved"]["lean"] == "sorry" and rows["d-unproved"]["disagrees"]
    assert drift.drift(p, [""])[0]["lean"] == "missing"


def test_drift_flags_a_claim_the_repo_itself_refutes_in_a_countermodel():
    from hypermath_foundations.translate import drift
    src = L0 + "\nderive d-claim as FORM:\n    step 1: ax-diff with x := ground\n            -> struct-distinct(apply(ground), ground)\n    close: struct-distinct(apply(ground), ground)\n"
    p = project.analyze([("l0.hm", src)])
    lean_txt = ("theorem dClaim : True := trivial\n"
                "def dClaimClaim : Prop := True\ntheorem x_fails : ¬ dClaimClaim := by sorry\n")
    row = [r for r in drift.drift(p, [lean_txt]) if r["derive"] == "d-claim"][0]
    assert row["lean"] == "refuted-in-countermodel" and row["disagrees"]


# -- the repository's own L0-L3 sources and lean4/ directory -------------------------


def real_project():
    return project.analyze([(n, (REPO / n).read_text(encoding="utf-8")) for n in LAYERS])


def test_real_layers_every_declaration_has_a_status_and_untranslated_ones_a_reason():
    p = real_project()
    assert p.entries
    for e in p.entries:
        assert e.status in {"translated", "admitted", "untranslated", "builtin"}, e
        if e.status == "untranslated":
            assert e.reason, f"{e.file}:{e.line} {e.name} dropped without a reason"
    counts = receipt.build(p, None, [], None, None, None, None)["counts"]
    assert sum(counts.values()) == len(p.entries)


def test_real_layers_receipt_is_deterministic_and_binds_the_source_digests():
    a = receipt.build(real_project(), None, [], None, None, None, None)
    b = receipt.build(real_project(), None, [], None, None, None, None)
    assert a == b
    assert [s["file"] for s in a["sources"]] == LAYERS
    assert all(len(s["sha256"]) == 64 for s in a["sources"])


def test_real_layers_drift_report_reads_the_repo_lean4_directory():
    from hypermath_foundations.translate import drift
    lean_files = [p.read_text(encoding="utf-8") for p in sorted((REPO / "lean4").rglob("*.lean"))
                  if ".lake" not in p.parts]
    assert lean_files
    rows = drift.drift(real_project(), lean_files)
    assert rows and all(r["lean"] for r in rows)
    flagged = {r["derive"] for r in rows if r["lean"] == "refuted-in-countermodel"}
    # The repository's own FiniteActionCountermodel.lean refutes these three claims
    # without recursion laws; this test records that fact, it does not change the tags.
    assert {"ordinal-zero-identity", "ordinal-succ-applies",
            "path-length-arithmetic"} <= flagged


def test_real_layers_lint_runs_and_reports_known_source_defects():
    from hypermath_foundations.translate import lint
    rep = lint.lint(real_project())
    assert lint.format_report(rep)
    assert {"additionally", "plus"} <= set(rep["undeclared_words"])


@pytest.mark.skipif(not lean_bin(), reason="HM_LEAN is unset")
def test_real_layers_generated_lean_compiles_with_the_kernel():
    out, _ = lean.kernel_check(real_project(), lean_bin())
    code, errs, _ = lean.run_lean(out.text, lean_bin())
    assert code == 0 and not errs


@pytest.mark.skipif(not mm_tool(), reason="HM_MMVERIFY is unset")
def test_real_layers_metamath_subset_verifies():
    text, status = metamath.emit_checked(real_project(), mm_tool())
    assert text and status is not None


def test_translate_subcommand_is_reachable_from_the_package_cli(tmp_path, capsys):
    from hypermath_foundations.__main__ import main
    assert main(["translate", "--lint", *[str(REPO / n) for n in LAYERS]]) == 0
    assert "additionally" in capsys.readouterr().out
    out = tmp_path / "out"
    assert main(["translate", *[str(REPO / n) for n in LAYERS], "--out", str(out)]) == 0
    import json
    rec = json.loads((out / "receipt.json").read_text(encoding="utf-8"))
    assert rec["lean"] is None and rec["metamath"] is None  # nothing was checked
