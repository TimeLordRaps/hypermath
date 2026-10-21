"""Regressions for certificate, representation and value-map audit failures."""

from __future__ import annotations

from fractions import Fraction

from hypermath_foundations.abstraction import (
    FormTerm,
    QuadrilateralFiltration,
    SemanticEquivalence,
    SubstanceWitness,
)
from hypermath_foundations.calculus_bridge import MetamathDatabase
from hypermath_foundations.meta_fractal import OrdinalPolynomial
from hypermath_foundations.objectification import ProofTrajectory


def _bound_witness(source: FormTerm, target: FormTerm) -> SubstanceWitness:
    middle = "checked-middle"
    trace = (source.digest(), middle, target.digest())
    return SubstanceWitness(
        source_digest=source.digest(),
        target_digest=target.digest(),
        step_count=2,
        energy_bound=2,
        state_trace=trace,
        allowed_transitions=frozenset(zip(trace, trace[1:])),
    )


def test_semantic_equivalence_binds_its_own_endpoints() -> None:
    source = FormTerm.f2f(FormTerm.ground())
    target = FormTerm.f2f(source)
    proof = QuadrilateralFiltration.syntax_to_abstraction(source, target)
    forged = SemanticEquivalence(
        lhs=FormTerm.ground(),
        rhs=FormTerm.ground(),
        abstraction_proof=proof,
        substance_witness=_bound_witness(source, target),
        certified=True,
    )

    assert not forged.is_sound()


def test_length_correct_trace_without_legal_edges_is_rejected() -> None:
    source = FormTerm("source")
    target = FormTerm("target")
    witness = SubstanceWitness(
        source_digest=source.digest(),
        target_digest=target.digest(),
        step_count=1,
        energy_bound=1,
        state_trace=(source.digest(), target.digest()),
        allowed_transitions=frozenset(),
        is_valid=True,
    )

    assert not witness.verify_conservation()


def test_wrap_map_evaluates_the_whole_polynomial_exactly() -> None:
    assert OrdinalPolynomial((0, 1)).wrap_map() == Fraction(-1, 2)
    assert OrdinalPolynomial((2, 3, 1)).wrap_map() == Fraction(3, 4)
    assert OrdinalPolynomial((7,)).wrap_map() == Fraction(7)


def test_trajectory_continuity_is_not_step_legality() -> None:
    source = FormTerm("source")
    target = FormTerm("target")
    trajectory = ProofTrajectory.single_step(source, target, "increment")

    assert not trajectory.verify_steps({})
    assert not trajectory.verify_steps({"increment": lambda _a, _b: False})
    assert trajectory.verify_steps({"increment": lambda a, b: a == source and b == target})


def test_metamath_checker_rejects_cyclic_and_forward_theorem_support() -> None:
    db = MetamathDatabase()
    db.add_constant("|-")
    db.add_constant("P")
    db.add_theorem("forward", ["|-", "P"], ["later"])
    db.add_theorem("later", ["|-", "P"], ["forward"])

    assert not db.verify_proof("forward")
    assert not db.verify_proof("later")


def test_metamath_checker_requires_declared_essential_hypothesis() -> None:
    db = MetamathDatabase()
    db.add_constant("wff")
    db.add_constant("|-")
    db.add_variable("ph")
    db.add_floating("wph", "wff", "ph")
    db.add_essential("eph", ["|-", "ph"])
    db.add_axiom("repeat", ["|-", "ph"], essentials=("eph",))
    db.add_theorem("missing", ["|-", "ph"], ["wph", "repeat"])

    assert not db.verify_proof("missing")


def test_metamath_checker_enforces_disjoint_substitutions() -> None:
    db = MetamathDatabase()
    db.add_constant("wff")
    db.add_constant("|-")
    db.add_variable("x")
    db.add_variable("y")
    db.add_floating("wx", "wff", "x")
    db.add_floating("wy", "wff", "y")
    db.add_disjoint("x", "y")
    db.add_axiom("pair", ["|-", "x", "y"])
    db.add_theorem("bad", ["|-", "x", "x"], ["wx", "wx", "pair"])

    assert not db.verify_proof("bad")
