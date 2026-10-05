from hypermath_foundations.translate import parser
from hypermath_foundations.translate.ast import Axiom, Close, Derive, Raw, Relation

SRC = """\
-- banner comment
primitive Form :: Type
    -- the ground type
primitive ground :: Form
primitive apply :: Form -> Form
    -- sole operation
opaque struct-distinct :: Form -> Form -> Prop
relation similar :: Form -> Form -> Prop    -- (~~)
primitive deriver : Form
axiom ax-diff:
    -- doc line
    for-all x :: Form:
        struct-distinct(apply(x), ground)
derive d1 as FORM:
    -- doc
    step 1: ax-diff with x := ground
            -> struct-distinct(apply(ground), ground)
    close: struct-distinct(apply(ground), ground)
close struct-continues as similar:
    -- only comments here
graduation L0 -> L1:
    name: "x"
    requires for L1:
        NC-1: whatever
"""


def kinds(decls):
    return [(type(d).__name__, getattr(d, "name", None)) for d in decls]


def test_declaration_kinds_and_names():
    decls = parser.parse(SRC, "t.hm").decls
    assert kinds(decls) == [
        ("Primitive", "Form"), ("Primitive", "ground"), ("Primitive", "apply"),
        ("Opaque", "struct-distinct"), ("Relation", "similar"), ("Primitive", "deriver"),
        ("Axiom", "ax-diff"), ("Derive", "d1"), ("Close", "struct-continues"), ("Raw", "graduation"),
    ]


def test_signatures_both_colon_forms():
    d = {x.name: x for x in parser.parse(SRC, "t.hm").decls if hasattr(x, "sig")}
    assert d["apply"].sig.params == ("Form",) and d["apply"].sig.result == "Form"
    assert d["struct-distinct"].sig.params == ("Form", "Form") and d["struct-distinct"].sig.result == "Prop"
    assert d["ground"].sig.params == () and d["ground"].sig.result == "Form"
    assert d["deriver"].sig.result == "Form"  # single-colon form


def test_relation_symbol_comes_from_the_trailing_comment():
    rel = [x for x in parser.parse(SRC, "t.hm").decls if isinstance(x, Relation)][0]
    assert rel.symbol == "~~"


def test_docs_attach_to_their_declaration_and_spans_are_one_based():
    mod = parser.parse(SRC, "t.hm")
    apply_ = [d for d in mod.decls if getattr(d, "name", "") == "apply"][0]
    assert "sole operation" in apply_.doc
    assert apply_.span.line == 5 and apply_.span.file == "t.hm"


def test_axiom_body_is_parsed_and_a_derive_keeps_steps_and_close():
    mod = parser.parse(SRC, "t.hm")
    ax = [d for d in mod.decls if isinstance(d, Axiom)][0]
    assert ax.error is None and ax.body is not None
    dv = [d for d in mod.decls if isinstance(d, Derive)][0]
    assert dv.status == "FORM" and len(dv.steps) == 1
    assert dv.steps[0].cites == "ax-diff"
    assert dv.steps[0].binds == (("x", "ground"),)
    assert dv.close_text == "struct-distinct(apply(ground), ground)"


def test_a_close_with_no_code_is_recorded_as_comment_only():
    cl = [d for d in parser.parse(SRC, "t.hm").decls if isinstance(d, Close)][0]
    assert cl.via == "similar" and cl.body_text == ""


def test_graduation_blocks_are_kept_raw_not_guessed_at():
    raw = [d for d in parser.parse(SRC, "t.hm").decls if isinstance(d, Raw)][0]
    assert raw.kind == "graduation" and "NC-1" in raw.text


def test_unknown_top_level_keyword_is_raw_and_never_dropped():
    mod = parser.parse("termformer foo:\n    stuff\nlaw bar:\n    more\n", "t.hm")
    assert [(r.kind, r.name) for r in mod.decls] == [("termformer", "foo"), ("law", "bar")]


def test_line_numbers_survive_blank_lines_and_trailing_comments():
    mod = parser.parse("\n\nopaque p :: Form -> Prop   -- trailing\n", "t.hm")
    assert mod.decls[0].span.line == 3


def test_known_signatures_and_infix_carry_across_files():
    l0 = parser.parse("opaque compose :: Form -> Form -> Form\nrelation similar :: Form -> Form -> Prop  -- (~~)\n", "l0.hm")
    l1 = parser.parse(
        "axiom a:\n    similar(compose x (compose y z), x)\n    x ~~ y\n",
        "l1.hm", known=l0.sigs, infix=l0.infix)
    ax = l1.decls[0]
    assert ax.error is None, ax.error


def test_modules_expose_their_declared_signatures():
    m = parser.parse("primitive ground :: Form\nopaque f :: Form -> Form -> Prop\n", "t.hm")
    assert m.sigs["ground"].params == () and m.sigs["f"].params == ("Form", "Form")
