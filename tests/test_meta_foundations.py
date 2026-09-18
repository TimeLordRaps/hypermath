# Copyright 2026 Tyler Roost / TimeLordRaps
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Deep regression tests for Hypermath foundational meta-features.

Covers:
  1. Abstraction & Quadrilateral Filtration (~=, ~~, =~, ==, SubstanceWitness)
  2. Objectification (Equivalence classes, Proof trajectories, Homotopy)
  3. Meta-Fractalization (Ordinatics polynomials, Hyperset theory, AFA, Hyperkernel)
  4. Metamath & Formal Calculi Bridge (5 calculi pathways, RPN proof validation)
"""

from __future__ import annotations

import math

import pytest

from hypermath_foundations import (
    AbstractionChain,
    AbstractionProof,
    AccessiblePointedGraph,
    ConstructiveMembership,
    FiltrationRetraceError,
    FormTerm,
    HyperCalculus,
    Hyperkernel,
    LanguageCalculus,
    MathCalculus,
    MetaCalculus,
    MetamathDatabase,
    ObjectificationError,
    ObjectifiedClass,
    OrdinalCalculus,
    OrdinalPolynomial,
    ProofTrajectory,
    QuadrilateralFiltration,
    QuineAtom,
    SubstanceWitness,
    TrajectoryHomotopy,
    TrajectoryStep,
    form_to_metamath,
)

# ============================================================================
# 1. Abstraction & Quadrilateral Filtration Tests
# ============================================================================

def test_form_term_creation_and_serialization():
    g = FormTerm.ground()
    f1 = FormTerm.f2f(g)
    f2 = FormTerm.box(f1)
    comp = FormTerm.compose(f1, f2)

    assert comp.depth() == 3
    assert comp.size() == 6
    assert not g.is_variable()
    v = FormTerm.var("X")
    assert v.is_variable()

    # Serialization round-trip
    d = comp.to_dict()
    restored = FormTerm.from_dict(d)
    assert comp == restored
    assert comp.digest() == restored.digest()
    assert str(comp) == "compose(f2f(ground), box(f2f(ground)))"


def test_syntax_continuation_similarity():
    g = FormTerm.ground()
    f1 = FormTerm.f2f(g)
    f2 = FormTerm.f2f(f1)
    b1 = FormTerm.box(g)

    # Reflexivity
    assert QuadrilateralFiltration.syntax_similarity(f1, f1)
    # Same operator similarity
    assert QuadrilateralFiltration.syntax_similarity(f1, f2)
    # Different operators without variables are not similar
    assert not QuadrilateralFiltration.syntax_similarity(f1, b1)

    # Non-transitivity: f1 ~~ f2 and f2 ~~ var(Y) and var(Y) ~~ b1,
    # but f1 !~~ b1 directly
    y = FormTerm.var("Y")
    assert QuadrilateralFiltration.syntax_similarity(f2, y)
    assert QuadrilateralFiltration.syntax_similarity(y, b1)
    assert not QuadrilateralFiltration.syntax_similarity(f1, b1)


def test_abstraction_equivalence_properties():
    t1 = FormTerm.f2f(FormTerm.ground())
    t2 = FormTerm.f2f(FormTerm.f2f(FormTerm.ground()))
    t3 = FormTerm.f2f(FormTerm.box(FormTerm.ground()))

    # Reflexivity
    p_refl = QuadrilateralFiltration.abstraction_reflexive(t1)
    assert p_refl.verify()
    assert p_refl.lhs == t1 and p_refl.rhs == t1

    # Off-branch: Syntax (~~) -> Abstraction (~=)
    p_off = QuadrilateralFiltration.syntax_to_abstraction(t1, t2)
    assert p_off.verify()

    # Symmetry
    p_sym = QuadrilateralFiltration.abstraction_symmetric(p_off)
    assert p_sym.verify()
    assert p_sym.lhs == t2 and p_sym.rhs == t1

    # Transitivity: (t1 ~= t2) and (t2 ~= t3) => (t1 ~= t3)
    p_off2 = QuadrilateralFiltration.syntax_to_abstraction(t2, t3)
    p_trans = QuadrilateralFiltration.abstraction_transitive(p_off, p_off2)
    assert p_trans.verify()
    assert p_trans.lhs == t1 and p_trans.rhs == t3

    # Invalid transitivity mismatch raises ValueError
    p_diff = QuadrilateralFiltration.abstraction_reflexive(FormTerm.ground())
    with pytest.raises(ValueError, match="Transitivity mismatch"):
        QuadrilateralFiltration.abstraction_transitive(p_off, p_diff)


def test_substance_witness_and_conditional_retrace():
    t1 = FormTerm.f2f(FormTerm.ground())
    t2 = FormTerm.f2f(FormTerm.f2f(FormTerm.ground()))
    proof = QuadrilateralFiltration.syntax_to_abstraction(t1, t2)

    # Valid substance witness
    witness = SubstanceWitness(
        source_digest=t1.digest(),
        target_digest=t2.digest(),
        step_count=2,
        energy_bound=10,
        state_trace=("s0", "s1", "s2"),
        is_valid=True,
    )
    assert witness.verify_conservation()

    # Successful conditional retrace around substance
    equiv = QuadrilateralFiltration.conditional_retrace(proof, witness)
    assert equiv.is_sound()
    assert equiv.certified

    # Retrace failure: conservation violation (steps > energy bound)
    invalid_energy = SubstanceWitness(
        source_digest=t1.digest(),
        target_digest=t2.digest(),
        step_count=5,
        energy_bound=2,
        state_trace=("s0", "s1", "s2", "s3", "s4", "s5"),
    )
    with pytest.raises(FiltrationRetraceError, match="Substance witness failed conservation"):
        QuadrilateralFiltration.conditional_retrace(proof, invalid_energy)

    # Retrace failure: digest mismatch
    mismatched = SubstanceWitness(
        source_digest="bad_digest",
        target_digest=t2.digest(),
        step_count=1,
        energy_bound=5,
        state_trace=("s0", "s1"),
    )
    with pytest.raises(FiltrationRetraceError, match="Substance witness endpoints do not bind"):
        QuadrilateralFiltration.conditional_retrace(proof, mismatched)


def test_downstream_compositionality_chain():
    # Construct a chain of 5 abstraction steps
    terms = [FormTerm(f"form_{i}") for i in range(6)]
    chain = AbstractionChain(terms[0])
    for next_term in terms[1:]:
        chain.extend(next_term)

    assert chain.length() == 5
    composed_proof = chain.collapse()
    assert composed_proof.verify()
    assert composed_proof.lhs == terms[0]
    assert composed_proof.rhs == terms[-1]


# ============================================================================
# 2. Objectification Tests (Equivalence Classes & Proof Trajectories)
# ============================================================================

def test_objectified_equivalence_class():
    rep = FormTerm.f2f(FormTerm.ground())
    m1 = FormTerm.f2f(FormTerm.f2f(FormTerm.ground()))
    m2 = FormTerm.f2f(FormTerm.box(FormTerm.ground()))

    eq_class = ObjectifiedClass(
        representative=rep,
        relation_name="abstraction",
        members=frozenset([rep, m1, m2]),
    )

    assert eq_class.contains(rep)
    assert eq_class.contains(m1)
    assert not eq_class.contains(FormTerm.ground())

    # Universal property morphism factoring: constant function factors cleanly
    def constant_depth_parity(t: FormTerm) -> int:
        return 0  # invariant across class

    assert eq_class.factor_morphism(constant_depth_parity) == 0

    # Non-constant morphism fails universal property factoring
    def non_constant_func(t: FormTerm) -> int:
        return t.depth()

    with pytest.raises(ObjectificationError, match="not well-defined"):
        eq_class.factor_morphism(non_constant_func)

    # Direct product of classes
    other_rep = FormTerm.ground()
    other_class = ObjectifiedClass(representative=other_rep, relation_name="ground_rel")
    prod_class = eq_class.direct_product(other_class)
    assert prod_class.representative == FormTerm.compose(rep, other_rep)
    assert len(prod_class.members) == 3


def test_proof_trajectory_algebra_and_composition():
    s0 = FormTerm("state_0")
    s1 = FormTerm("state_1")
    s2 = FormTerm("state_2")

    t1 = ProofTrajectory.single_step(s0, s1, rule="rule_alpha")
    t2 = ProofTrajectory.single_step(s1, s2, rule="rule_beta")

    assert t1.length() == 1
    assert t1.start == s0 and t1.end == s1

    # Associative trajectory composition
    composed = t1.compose(t2)
    assert composed.length() == 2
    assert composed.start == s0 and composed.end == s2
    assert composed.intermediate_states() == [s0, s1, s2]

    # Endpoint mismatch rejection
    s_other = FormTerm("state_other")
    t_invalid = ProofTrajectory.single_step(s_other, s2, rule="rule_gamma")
    with pytest.raises(ObjectificationError, match="endpoint mismatch"):
        t1.compose(t_invalid)

    # Trajectory inversion
    inverted = composed.invert()
    assert inverted.start == s2 and inverted.end == s0
    assert inverted.length() == 2
    assert inverted.steps[0].rule == "inv(rule_beta)"

    # Identity trajectory
    id_s0 = ProofTrajectory.identity(s0)
    assert id_s0.length() == 0
    composed_id = id_s0.compose(t1)
    assert composed_id.start == t1.start and composed_id.end == t1.end


def test_trajectory_homotopy():
    s0 = FormTerm("init")
    s1 = FormTerm("mid_a")
    s2 = FormTerm("goal")
    s1_prime = FormTerm("mid_b")

    # Two parallel trajectories commuting via independent operations
    tau1 = ProofTrajectory.single_step(s0, s1, rule="op_A").compose(
        ProofTrajectory.single_step(s1, s2, rule="op_B")
    )
    tau2 = ProofTrajectory.single_step(s0, s1_prime, rule="op_B").compose(
        ProofTrajectory.single_step(s1_prime, s2, rule="op_A")
    )

    # Identical endpoints allow homotopy
    homotopy = TrajectoryHomotopy(
        source_trajectory=tau1,
        target_trajectory=tau2,
        rewrite_rule="independent_commutation",
    )
    assert homotopy.certified

    # Check homotopy under commutation pair
    assert TrajectoryHomotopy.are_homotopic(
        tau1, tau2, commutation_pairs=[("op_A", "op_B")]
    )
    # Rejection: without commutation pair permitted
    assert not TrajectoryHomotopy.are_homotopic(
        tau1, tau2, commutation_pairs=[]
    )
    assert not TrajectoryHomotopy.are_homotopic(
        tau1, tau2, commutation_pairs=[("op_X", "op_Y")]
    )

    # Different endpoints reject homotopy
    tau_mismatched = ProofTrajectory.single_step(s0, FormTerm("other_goal"), rule="op_A")
    with pytest.raises(ObjectificationError, match="identical endpoints"):
        TrajectoryHomotopy(tau1, tau_mismatched, rewrite_rule="invalid")


# ============================================================================
# 3. Meta-Fractalization Tests (Ordinatics, Hypersets, AFA, Hyperkernel)
# ============================================================================

def test_ordinal_polynomial_arithmetic():
    # 2*w^2 + 3*w + 1
    p1 = OrdinalPolynomial((1, 3, 2))
    # w + 4
    p2 = OrdinalPolynomial((4, 1))

    assert p1.degree() == 2
    assert p2.degree() == 1
    assert str(p1) == "2*w^2 + 3*w + 1"
    assert str(p2) == "w + 4"

    # Natural Hessenberg addition: componentwise
    # (2*w^2 + 3*w + 1) (+) (w + 4) = 2*w^2 + 4*w + 5
    p_sum = p1.natural_add(p2)
    assert p_sum.coefficients == (5, 4, 2)
    assert str(p_sum) == "2*w^2 + 4*w + 5"

    # Natural multiplication
    # (w + 1) (x) (w + 2) = w^2 + 3*w + 2
    a = OrdinalPolynomial((1, 1))
    b = OrdinalPolynomial((2, 1))
    p_prod = a.natural_mul(b)
    assert p_prod.coefficients == (2, 3, 1)

    # Wrap map specialization
    assert p1.wrap_map() == -0.5

    # Embedding into FormTerm
    form_rep = p1.to_form()
    assert isinstance(form_rep, FormTerm)


def test_constructive_hyperset_and_quine_atom():
    # Quine Atom Omega = {Omega}
    quine = QuineAtom()
    assert quine.satisfies_self_membership()

    q_form = quine.to_form()
    assert ConstructiveMembership.is_member(q_form, q_form)

    # Circular 2-cycle: A in B and B in A
    node_b = FormTerm("cycle_node", (FormTerm("node_a"),))
    node_a = FormTerm("cycle_node", (node_b,))
    assert ConstructiveMembership.is_member(node_b, node_a)


def test_aczel_afa_and_bisimulation():
    # APG 1: Quine atom self-loop: v0 -> v0
    apg_quine = AccessiblePointedGraph(
        nodes=frozenset(["v0"]),
        edges=frozenset([("v0", "v0")]),
        root="v0",
    )
    dec1 = apg_quine.solve_decoration()
    assert dec1["v0"].symbol == "quine_atom"

    # APG 2: Another representation of Quine atom
    apg_quine2 = AccessiblePointedGraph(
        nodes=frozenset(["u0"]),
        edges=frozenset([("u0", "u0")]),
        root="u0",
    )
    # Bisimulation between the two Quine graphs holds!
    assert AccessiblePointedGraph.are_bisimilar(apg_quine, apg_quine2)

    # APG 3: Finite well-founded set: v0 -> v1 -> ground
    apg_finite = AccessiblePointedGraph(
        nodes=frozenset(["root", "leaf"]),
        edges=frozenset([("root", "leaf")]),
        root="root",
    )
    dec_finite = apg_finite.solve_decoration()
    assert "hyperset:root" in dec_finite["root"].symbol

    # Non-bisimilarity between circular and well-founded graphs
    assert not AccessiblePointedGraph.are_bisimilar(apg_quine, apg_finite)


def test_terminal_self_derivation_hyperkernel():
    # Construct a fixed-point Hyperkernel: Phi(S) == S
    fixed_state = FormTerm("stable_ground")
    kernel = Hyperkernel(
        state=fixed_state,
        derivation_rule=lambda s: s,  # Identity endofunctor fixed point
        decision_procedure=lambda s: s.symbol == "stable_ground",
    )

    assert kernel.verify_state()
    assert kernel.cyclical_completion()
    assert kernel.self_representation.symbol == "hyperkernel_rep"

    # Non-fixed point hyperkernel
    divergent_kernel = Hyperkernel(
        state=FormTerm("state_0"),
        derivation_rule=lambda s: FormTerm("state_1"),
        decision_procedure=lambda s: True,
    )
    assert not divergent_kernel.cyclical_completion()


# ============================================================================
# 4. Metamath & Formal Calculi Bridge Tests
# ============================================================================

def test_metamath_database_generation_and_proof_verification():
    db = MetamathDatabase()
    db.add_constant("wff")
    db.add_constant("|-")
    db.add_constant("->")
    db.add_variable("ph")
    db.add_variable("ps")

    db.add_floating("wph", "wff", "ph")
    db.add_floating("wps", "wff", "ps")
    db.add_axiom("ax-1", ["|-", "(", "ph", "->", "(", "ps", "->", "ph", ")", ")"])
    db.add_theorem(
        "th-ax1-inst",
        ["|-", "(", "ph", "->", "(", "ph", "->", "ph", ")", ")"],
        ["wph", "wph", "ax-1"],
    )

    emitted = db.emit()
    assert "$c" in emitted
    assert "$v" in emitted
    assert "wph $f wff ph $." in emitted
    assert "ax-1 $a" in emitted
    assert "th-ax1-inst $p" in emitted

    # Verify valid RPN proof
    assert db.verify_proof("th-ax1-inst")
    assert not db.verify_proof("non_existent")

    # Modus Ponens deduction verification
    db.add_constant("P")
    db.add_constant("Q")
    db.add_axiom("ax-p", ["|-", "P"])
    db.add_axiom("ax-imp", ["|-", "(", "P", "->", "Q", ")"])
    db.add_theorem("th-mp", ["|-", "Q"], ["ax-p", "ax-imp", "mp"])
    assert db.verify_proof("th-mp")

    # Rejections: conclusion mismatch, bogus step, dirty stack
    db.add_theorem("th-mismatch", ["|-", "ph"], ["wph", "wph", "ax-1"])
    assert not db.verify_proof("th-mismatch")

    db.add_theorem("th-bogus", ["|-", "FALSE"], ["bogus_token"])
    assert not db.verify_proof("th-bogus")

    db.add_theorem("th-dirty", ["|-", "ph"], ["wph", "wph"])
    assert not db.verify_proof("th-dirty")


def test_form_to_metamath_translation():
    term = FormTerm.f2f(FormTerm.ground())
    db = MetamathDatabase()
    tokens = form_to_metamath(term, db)
    assert tokens == ["f2f", "(", "ground", ")"]
    assert "f2f" in db.constants
    assert "ground" in db.constants


def test_calculus_pathway_1_language_calculus():
    lc = LanguageCalculus()
    lc.add_production("Expr", ["Num", "+", "Num"])
    lc.add_production("Num", ["1"])

    # Step-by-step reduction of "1 + 1"
    raw = ["1", "+", "1"]
    red1 = lc.parse_step(raw)
    assert red1 == ["Num", "+", "1"]
    full_reduction = lc.reduce(raw)
    assert full_reduction == ["Expr"]


def test_calculus_pathway_2_meta_calculus_symbolic_dynamics():
    mc = MetaCalculus()
    # Rewrite rule: f2f(box(x)) -> box(f2f(x))
    def commute_box(term: FormTerm) -> FormTerm:
        if term.symbol == "f2f" and term.args and term.args[0].symbol == "box":
            inner = term.args[0].args[0]
            return FormTerm.box(FormTerm.f2f(inner))
        return term

    mc.add_rewrite_rule("commute_box", commute_box)
    start_term = FormTerm.f2f(FormTerm.box(FormTerm.ground()))
    orbit = mc.compute_orbit(start_term, max_steps=5)

    assert len(orbit) == 2
    assert orbit[1] == FormTerm.box(FormTerm.f2f(FormTerm.ground()))

    # Cycle detection in periodic orbit
    has_cycle, cycle_start, period = mc.detect_cycle(orbit)
    assert not has_cycle  # terminates at fixed point

    # Simulated cyclic orbit
    c1 = FormTerm("cycle_a")
    c2 = FormTerm("cycle_b")
    cyclic_orbit = [c1, c2, c1, c2]
    has_cycle2, start2, period2 = mc.detect_cycle(cyclic_orbit)
    assert has_cycle2 and period2 == 2


def test_calculus_pathway_3_hyper_calculus_lie_derivations():
    # Translation group action: T_a(f)(x) = f(x + a)
    def f(x: float) -> float:
        return x ** 2
    t_2 = HyperCalculus.translation_group_action(f, 2.0)
    assert math.isclose(t_2(3.0), 25.0)  # (3 + 2)^2 = 25

    # Leibniz product verification
    # f(x) = x^2, g(x) = x^3 => D(f*g) = 2x*x^3 + x^2*3x^2 = 5x^4
    x = 2.0
    df_x = 4.0   # 2*2
    dg_x = 12.0  # 3*4
    leibniz_val = HyperCalculus.leibniz_product(lambda t: 2*t, f, lambda t: t**3, x, df_x, dg_x)
    assert math.isclose(leibniz_val, 5.0 * (x ** 4))

    # Lie bracket: [D1, D2] where D1 = d/dx, D2 = x * d/dx
    # [D1, D2](f) = D1(x f') - x D1(f') = f' + x f'' - x f'' = f'
    def d1(func):
        return lambda t: (func(t + 1e-5) - func(t - 1e-5)) / 2e-5

    def d2(func):
        return lambda t: t * d1(func)(t)

    bracket = HyperCalculus.lie_bracket(d1, d2, f)
    # At x = 3, f'(3) = 6
    assert math.isclose(bracket(3.0), 6.0, abs_tol=1e-3)


def test_calculus_pathway_4_ordinal_calculus():
    # Forward transfinite difference
    # f(w) = w^2 => Delta_w(f)(w) = (w+1)^2 - w^2 = 2w + 1
    def f(n: int) -> int:
        return n ** 2
    diff = OrdinalCalculus.transfinite_difference(f, 10)
    assert diff == 121 - 100 == 21

    # Formal limit derivative: d/dw (3*w^3 + 2*w^2 + 5*w + 7)
    # coeffs = (7, 5, 2, 3) => d/dw = (5, 4, 9) = 9*w^2 + 4*w + 5
    coeffs = (7, 5, 2, 3)
    deriv = OrdinalCalculus.limit_derivative(coeffs)
    assert deriv == (5, 4, 9)


def test_calculus_pathway_5_normal_math_calculus():
    # Derivative of f(x) = x^3 at x = 2: f'(2) = 12
    def f(x: float) -> float:
        return x ** 3
    df_2 = MathCalculus.derivative(f, 2.0)
    assert math.isclose(df_2, 12.0, rel_tol=1e-5)

    # Definite integral of f(x) = x^2 from 0 to 3: [x^3/3]_0^3 = 9
    integral_val = MathCalculus.definite_integral(lambda x: x ** 2, 0.0, 3.0)
    assert math.isclose(integral_val, 9.0, rel_tol=1e-4)

    # Leibniz product rule verification
    def g(x: float) -> float:
        return math.sin(x)
    assert MathCalculus.verify_leibniz_rule(f, g, 1.5)

    # Fundamental Theorem of Calculus verification: integral of 3x^2 from 1 to 4 == 4^3 - 1^3 = 63
    def f_prime(x: float) -> float:
        return 3.0 * (x ** 2)
    assert MathCalculus.verify_fundamental_theorem(f, f_prime, 1.0, 4.0)


# ============================================================================
# 5. Boundary and Edge Case Tests
# ============================================================================

def test_abstraction_chain_empty_collapse():
    term = FormTerm("lonely_term")
    chain = AbstractionChain(term)
    assert chain.length() == 0
    collapsed = chain.collapse()
    assert collapsed.verify()
    assert collapsed.rule_name == "reflexive"
    assert collapsed.lhs == term and collapsed.rhs == term


def test_ordinal_polynomial_edge_cases():
    zero = OrdinalPolynomial.zero()
    assert zero.degree() == 0
    assert str(zero) == "0"

    one = OrdinalPolynomial.one()
    assert one.degree() == 0
    assert str(one) == "1"

    omega = OrdinalPolynomial.omega()
    assert omega.degree() == 1
    assert str(omega) == "w"

    # Trailing zeros stripped
    p_trailing = OrdinalPolynomial((5, 0, 0))
    assert p_trailing.coefficients == (5,)

    with pytest.raises(ValueError, match="must be non-negative"):
        OrdinalPolynomial.from_int(-1)


def test_apg_boundary_and_validation():
    # Root not in nodes
    with pytest.raises(ValueError, match="Root.*must be in nodes"):
        AccessiblePointedGraph(nodes=frozenset(["a"]), edges=frozenset(), root="missing")

    # Edge referencing missing node
    with pytest.raises(ValueError, match="references node outside"):
        AccessiblePointedGraph(
            nodes=frozenset(["a"]), edges=frozenset([("a", "b")]), root="a"
        )

    # Isolated root node decoration is ground
    apg_iso = AccessiblePointedGraph(nodes=frozenset(["root"]), edges=frozenset(), root="root")
    dec = apg_iso.solve_decoration()
    assert dec["root"] == FormTerm.ground()


def test_math_calculus_boundary_cases():
    # Integral with a == b
    assert MathCalculus.definite_integral(lambda x: x ** 2, 5.0, 5.0) == 0.0

    # Constant derivative
    def linear(x: float) -> float:
        return 5.0 * x + 3.0
    deriv = MathCalculus.derivative(linear, 100.0)
    assert math.isclose(deriv, 5.0, abs_tol=1e-5)


def test_adversarial_break_and_repair_verification():
    # 1. APG bisimulation reflexivity on branching graphs
    branching_apg = AccessiblePointedGraph(
        nodes=frozenset(["root", "leaf", "mid", "child"]),
        edges=frozenset([("root", "leaf"), ("root", "mid"), ("mid", "child")]),
        root="root",
    )
    assert AccessiblePointedGraph.are_bisimilar(branching_apg, branching_apg)

    # 2. Bisimilarity of 1-cycle Quine atom and 2-cycle system
    apg_1cycle = AccessiblePointedGraph(
        nodes=frozenset(["q"]),
        edges=frozenset([("q", "q")]),
        root="q",
    )
    apg_2cycle = AccessiblePointedGraph(
        nodes=frozenset(["a", "b"]),
        edges=frozenset([("a", "b"), ("b", "a")]),
        root="a",
    )
    assert AccessiblePointedGraph.are_bisimilar(apg_1cycle, apg_2cycle)

    # 3. APG with unreachable nodes must be rejected
    with pytest.raises(ValueError, match="not accessible from root"):
        AccessiblePointedGraph(
            nodes=frozenset(["root", "orphan"]),
            edges=frozenset(),
            root="root",
        )

    # 4. ProofTrajectory continuity enforcement
    s0 = FormTerm("s0")
    s1 = FormTerm("s1")
    s2 = FormTerm("s2")
    s_orphan = FormTerm("orphan")
    with pytest.raises(ObjectificationError, match="step discontinuity"):
        ProofTrajectory(
            start=s0,
            end=s2,
            steps=(
                TrajectoryStep(0, s0, s1, "rule1"),
                TrajectoryStep(1, s_orphan, s2, "rule2"),
            ),
        )
    with pytest.raises(ObjectificationError, match="must have start == end"):
        ProofTrajectory(start=s0, end=s2, steps=())

    # 5. TrajectoryHomotopy commutation reachability
    t1 = ProofTrajectory.single_step(s0, s1, "A").compose(
        ProofTrajectory.single_step(s1, s2, "B")
    )
    t2 = ProofTrajectory.single_step(s0, FormTerm("alt"), "B").compose(
        ProofTrajectory.single_step(FormTerm("alt"), s2, "A")
    )
    # Reject when no commutation permitted
    assert not TrajectoryHomotopy.are_homotopic(t1, t2, commutation_pairs=[])
    # Reject when irrelevant commutation permitted
    assert not TrajectoryHomotopy.are_homotopic(t1, t2, commutation_pairs=[("X", "Y")])
    # Accept when exact commutation permitted
    assert TrajectoryHomotopy.are_homotopic(t1, t2, commutation_pairs=[("A", "B")])

    # 6. SubstanceWitness conservation rejection on zero steps with distinct digests
    zero_step_mismatch = SubstanceWitness(
        source_digest="digest_A",
        target_digest="digest_B",
        step_count=0,
        energy_bound=0,
        state_trace=("s0",),
    )
    assert not zero_step_mismatch.verify_conservation()

    # 7. AbstractionProof syntax_off_branch with variable continuation
    var_term = FormTerm.var("X")
    ground_term = FormTerm.ground()
    p_var = QuadrilateralFiltration.syntax_to_abstraction(var_term, ground_term)
    assert p_var.verify()

    # 8. AbstractionProof schema_congruence rejects arity mismatch
    p_arity_mismatch = AbstractionProof(
        lhs=FormTerm("op", (FormTerm.ground(),)),
        rhs=FormTerm("op", (FormTerm.ground(), FormTerm.ground())),
        rule_name="schema_congruence",
        justification="invalid arity match",
    )
    assert not p_arity_mismatch.verify()

    # 9. OrdinalPolynomial validation and natural multiplication with zero
    with pytest.raises(ValueError, match="non-negative integers"):
        OrdinalPolynomial((-2, 1))

    zero_poly = OrdinalPolynomial.zero()
    omega_poly = OrdinalPolynomial.omega()
    assert omega_poly.natural_mul(zero_poly) == zero_poly
    assert zero_poly.natural_mul(omega_poly) == zero_poly
    assert OrdinalPolynomial(()).coefficients == (0,)

    # 10. MathCalculus validation checks
    with pytest.raises(ValueError, match="strictly positive"):
        MathCalculus.derivative(lambda x: x, 1.0, h=0.0)
    with pytest.raises(ValueError, match="strictly positive"):
        MathCalculus.definite_integral(lambda x: x, 0.0, 1.0, subdivisions=0)

    # 11. OrdinalCalculus limit_derivative trailing zero canonicalization
    assert OrdinalCalculus.limit_derivative((7, 0, 0)) == (0,)

    # 12. HyperCalculus leibniz_product auto-evaluation using derivation d
    def d_op(x: float) -> float:
        return 3.0 * (x ** 2)

    def f_func(x: float) -> float:
        return x ** 3

    def g_func(x: float) -> float:
        return x ** 2

    res = HyperCalculus.leibniz_product(
        d=d_op, f=f_func, g=g_func, x=2.0, dg_x=4.0
    )
    # D(f*g)(2) = f'(2)*g(2) + f(2)*g'(2) = 12 * 4 + 8 * 4 = 48 + 32 = 80
    assert math.isclose(res, 80.0)

    # 13. ObjectifiedClass direct_product combines invariants
    c1 = ObjectifiedClass(
        representative=FormTerm("a"),
        relation_name="r1",
        invariants=(("inv1", "val1"),),
    )
    c2 = ObjectifiedClass(
        representative=FormTerm("b"),
        relation_name="r2",
        invariants=(("inv2", "val2"),),
    )
    prod = c1.direct_product(c2)
    assert prod.invariants == (("inv1", "val1"), ("inv2", "val2"))
