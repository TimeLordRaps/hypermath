from hypermath_foundations.translate import project

L0 = """\
primitive Form :: Type
primitive Prop :: Type
primitive ground :: Form
primitive apply :: Form -> Form
opaque struct-distinct :: Form -> Form -> Prop
relation similar :: Form -> Form -> Prop    -- (~~)
axiom ax-diff:
    for-all x :: Form:
        struct-distinct(apply(x), ground)
axiom ax-undeclared:
    for-all x :: Form:
        mystery(x, ground)
axiom ax-arity:
    for-all x :: Form:
        struct-distinct(x)
axiom ax-comment-only:
    -- the statement is only prose
derive d-instance as FORM:
    step 1: ax-diff with x := ground
            -> struct-distinct(apply(ground), ground)
    close: struct-distinct(apply(ground), ground)
derive d-prose as FORM:
    step 1: some prose
    close: relation(~~)
derive d-multi as FORM:
    step 1: ax-diff with x := ground
    step 2: more
    close: struct-distinct(apply(ground), ground)
close struct-continues as similar:
    -- comments only
graduation L0 -> L1:
    name: "x"
"""


def entries():
    return {e.name: e for e in project.analyze([("l0.hm", L0)]).entries}


def test_declarations_are_translated_and_prop_is_a_builtin():
    e = entries()
    assert e["Form"].status == "translated" and e["ground"].status == "translated"
    assert e["Prop"].status == "builtin"
    assert e["similar"].status == "translated"


def test_axiom_with_resolved_names_is_translated():
    assert entries()["ax-diff"].status == "translated"


def test_undeclared_name_is_untranslated_with_the_name_in_the_reason():
    e = entries()["ax-undeclared"]
    assert e.status == "untranslated" and "mystery" in e.reason


def test_wrong_arity_is_untranslated():
    e = entries()["ax-arity"]
    assert e.status == "untranslated" and "arity" in e.reason


def test_comment_only_axiom_is_untranslated():
    e = entries()["ax-comment-only"]
    assert e.status == "untranslated" and "comments" in e.reason


def test_derive_is_admitted_by_default_and_proved_only_by_exact_instantiation():
    e = entries()
    assert e["d-instance"].status == "admitted" and e["d-instance"].proof == ("ax-diff", (("x", "ground"),))
    assert e["d-multi"].status == "admitted" and e["d-multi"].proof is None  # two steps: not a bare instance


def test_derive_whose_close_is_not_a_proposition_is_untranslated():
    e = entries()["d-prose"]
    assert e.status == "untranslated" and "relation" in e.reason


def test_close_and_graduation_are_untranslated_with_reasons():
    e = entries()
    assert e["close-struct-continues"].status == "untranslated" and e["close-struct-continues"].reason
    assert e["graduation"].status == "untranslated" and "graduation" in e["graduation"].reason


def test_names_declared_in_an_earlier_file_resolve_in_a_later_one():
    proj = project.analyze([("l0.hm", L0), ("l1.hm", "axiom a1:\n    for-all x :: Form:\n        similar(x, x)\n")])
    assert {e.name: e.status for e in proj.entries}["a1"] == "translated"


def test_undeclared_infix_word_is_flagged_as_a_source_defect():
    src = "primitive Form :: Type\nprimitive ground :: Form\nopaque congruent :: Form -> Form -> Prop\n" \
          "axiom s:\n    for-all a :: Form:\n        congruent(a plus ground, a)\n"
    e = {x.name: x for x in project.analyze([("t.hm", src)]).entries}["s"]
    assert e.status == "untranslated" and "plus" in e.reason


CLOSE_SRC = L0 + """
close struct-distinct as not-simulation:
    -- prose stays documentation
    struct-distinct(x, y) <-> not (x ~~ y)

close struct-continues as similar:
    -- comments only: stays untranslated
"""


def test_close_with_a_formula_line_is_translated_with_inferred_universal_binders():
    from hypermath_foundations.translate.ast import Forall
    e = {x.name: x for x in project.analyze([("l0.hm", CLOSE_SRC)]).entries}
    c = e["close-struct-distinct"]
    assert c.status == "translated" and c.kind == "close"
    assert isinstance(c.expr, Forall) and dict(c.expr.binders) == {"x": "Form", "y": "Form"}
    assert e["close-struct-continues"].status == "untranslated"


def test_close_formula_with_an_ambiguous_variable_sort_is_refused():
    src = L0 + "\nclose struct-distinct as z:\n    x ~~ x\n"
    e = {x.name: x for x in project.analyze([("l0.hm", src)]).entries}
    assert e["close-struct-distinct"].status == "translated"  # x only in Form positions: fine
    src = L0 + "\nopaque other :: Form -> Form -> Prop\nclose other as z:\n    other(x, y) <-> mystery(x)\n"
    e = {x.name: x for x in project.analyze([("l0.hm", src)]).entries}
    assert e["close-other"].status == "untranslated" and "mystery" in e["close-other"].reason
