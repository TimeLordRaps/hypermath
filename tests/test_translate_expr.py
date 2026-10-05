import pytest

from hypermath_foundations.translate import expr
from hypermath_foundations.translate.ast import (
    And,
    App,
    Exists,
    Forall,
    Iff,
    Implies,
    Name,
    Not,
    Or,
)


def p(text, infix=None):
    return expr.parse_expr(text, infix or {"~~": "similar", "=~": "congruent", "==": "simulation"})


def test_application_and_nesting():
    e = p("struct-distinct(apply(x), ground)")
    assert e == App("struct-distinct", (App("apply", (Name("x"),)), Name("ground")))


def test_hyphenated_names_do_not_swallow_the_arrow():
    e = p("a-b -> c")
    assert e == Implies(Name("a-b"), Name("c"))


def test_curried_call_flattens():
    assert p("step(x)(y)") == App("step", (Name("x"), Name("y")))


def test_infix_relations_resolve_through_the_table():
    assert p("x ~~ y") == App("similar", (Name("x"), Name("y")))
    assert p("apply(x) == x") == App("simulation", (App("apply", (Name("x"),)), Name("x")))


def test_precedence_not_and_or_implies():
    e = p("not a and b or c -> d")
    assert e == Implies(Or(And(Not(Name("a")), Name("b")), Name("c")), Name("d"))


def test_iff_and_implies_words():
    assert p("a implies b") == Implies(Name("a"), Name("b"))
    assert p("a <-> b") == Iff(Name("a"), Name("b"))


def test_quantifier_forms_binder_styles():
    a = p("for-all x :: Form:\n  f(x)")
    assert a == Forall((("x", "Form"),), None, App("f", (Name("x"),)))
    b = p("for-all (a b :: Form), exists c :: Form,\n similar(c, a) and similar(c, b)")
    assert isinstance(b, Forall) and b.binders == (("a", "Form"), ("b", "Form"))
    assert isinstance(b.body, Exists) and b.body.binders == (("c", "Form"),)
    c = p("for-all n :: Form where g(n): not (n == k)")
    assert c.guard == App("g", (Name("n"),)) and isinstance(c.body, Not)


def test_postfix_binder_wraps_the_statement():
    e = expr.parse_statement("simulation(x, y) -> congruent(x, y)    for-all x y :: Form", {})
    assert e == Forall((("x", "Form"), ("y", "Form")), None,
                       Implies(App("simulation", (Name("x"), Name("y"))), App("congruent", (Name("x"), Name("y")))))


def test_exists_where_form():
    e = p("exists x y :: Form where struct-distinct(x, y) and k(x)")
    assert isinstance(e, Exists) and e.binders == (("x", "Form"), ("y", "Form"))


def test_plus_is_an_infix_word():
    assert p("congruent(a plus ground, a)") == App("congruent", (App("plus", (Name("a"), Name("ground"))), Name("a")))


def test_garbage_raises_a_located_error():
    with pytest.raises(expr.ExprError) as e:
        p("a b c")
    assert "no declared arity" in str(e.value)


def test_unterminated_paren_raises():
    with pytest.raises(expr.ExprError):
        p("f(x, y")


def test_free_names_exclude_binders():
    e = p("for-all x :: Form: struct-distinct(apply(x), ground)")
    assert expr.free_names(e) == {"struct-distinct", "apply", "ground"}


def test_power_notation_is_rejected_not_guessed():
    with pytest.raises(expr.ExprError):
        p("apply^n(x) =~ y")


def test_juxtaposition_resolves_only_through_a_declared_arity():
    e = expr.parse_expr("compose p (compose q r)", {}, {"compose": 2})
    assert e == App("compose", (Name("p"), App("compose", (Name("q"), Name("r")))))


def test_juxtaposition_after_an_undeclared_name_is_an_error_not_a_guess():
    with pytest.raises(expr.ExprError):
        expr.parse_expr("additionally a b", {}, {"compose": 2})


def test_juxtaposition_stops_at_connectives():
    e = expr.parse_expr("f a b and g c", {}, {"f": 2, "g": 1})
    assert e == And(App("f", (Name("a"), Name("b"))), App("g", (Name("c"),)))


def test_declared_constants_are_not_applications():
    assert expr.parse_expr("similar(x, ground)", {}, {"similar": 2, "ground": 0}) == App(
        "similar", (Name("x"), Name("ground")))
