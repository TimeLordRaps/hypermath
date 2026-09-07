"""Reproduce finite counterexamples used in the mathematical audit.

These checks establish failures of specific proposed implications. They are
not models of every hypermath axiom or a proof about the completed framework.
Run with visible output: python -u scripts/check_audit_models.py
"""

from itertools import product


def check(name, function):
    print(f"START {name}", flush=True)
    function()
    print(f"PASS {name}", flush=True)


def overlap_is_not_shared_ground_or_transitivity():
    continuations = {"left": {0}, "ground": {0, 1}, "right": {1}}

    def similar(x, y):
        return bool(continuations[x] & continuations[y])

    assert similar("left", "ground")
    assert similar("ground", "right")
    assert not similar("left", "right")


def finite_reachability_needs_congruence_preservation():
    forms = range(4)
    apply = (1, 1, 3, 3)
    classes = (0, 1, 1, 2)

    def congruent(x, y):
        return classes[x] == classes[y]

    def simulation(x, y):
        return x == y

    def similar(x, y):
        return True

    # The selected relational assumptions from L0/L1, not the full theory.
    for x in forms:
        assert not simulation(apply[x], 0)  # ax-diff after structural close
        assert similar(apply[x], 0)  # ax-sim
        assert similar(apply[apply[x]], x)  # ax-box
    assert similar(0, 0)
    for x, y in product(forms, repeat=2):
        assert not simulation(x, y) or congruent(x, y)
        assert not congruent(x, y) or similar(x, y)

    def derives(x, y):
        seen = set()
        while x not in seen:
            if congruent(x, y):
                return True
            seen.add(x)
            x = apply[x]
        return False

    assert congruent(1, 2)
    assert not congruent(apply[1], apply[2])
    assert derives(0, 2) and derives(2, 3) and not derives(0, 3)


def double_return_does_not_identify_single_steps():
    # An involution has exact two-step return without one-step identity.
    flip = (1, 0)
    assert all(flip[flip[x]] == x for x in range(2))
    assert all(flip[x] != x for x in range(2))


def universal_asymmetry_conflicts_with_identity():
    # A representative nontrivial monoid; the contradiction uses only its unit.
    identity, element = (), ("a",)
    concatenate = lambda left, right: left + right
    assert element != identity
    assert concatenate(element, identity) == element
    assert concatenate(identity, element) == element
    assert concatenate(element, identity) == concatenate(identity, element)
    # Thus distinct operands can commute: the universal asymmetry claim fails.


def finite_growth_does_not_prevent_enumeration():
    # Arbitrarily large finite counts still admit natural-number block codes.
    offset = 0
    observed_codes = set()
    for depth in range(5):
        count = 2 ** (depth * depth - depth)
        codes = set(range(offset, offset + count))
        assert len(codes) == count
        assert observed_codes.isdisjoint(codes)
        observed_codes.update(codes)
        offset += count
    # This checks finite examples. The general disjoint-block proof is in the audit.
    assert len(observed_codes) == offset


if __name__ == "__main__":
    checks = [
        overlap_is_not_shared_ground_or_transitivity,
        finite_reachability_needs_congruence_preservation,
        double_return_does_not_identify_single_steps,
        universal_asymmetry_conflicts_with_identity,
        finite_growth_does_not_prevent_enumeration,
    ]
    for function in checks:
        check(function.__name__, function)
    print(f"Completed {len(checks)} named finite checks; no full-theory claim.", flush=True)
