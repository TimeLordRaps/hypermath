"""The average as a fold: iterated midpoints reproduce Conway's surreal birthdays.

Independent oracle: the closed-form birthday of a dyadic m/2^k (lowest terms, k >= 1) is floor(|x|) + 1 + k, and
of an integer n it is |n|. Checks (exact, Fraction arithmetic): fold day equals birthday for every number produced;
in every gap the simplest number strictly between its neighbours is the average; every inner gap repeats the
pattern of (0, 1) over the next days; the fold path toward 1/3 converges at rate 2^-n. A fold at one third instead
of the average fails the oracle.
"""
from fractions import Fraction as Q
from math import floor

DAYS = 9


def birthday(x: Q) -> int:
    if x.denominator == 1:
        return abs(x.numerator)
    k = x.denominator.bit_length() - 1
    return floor(abs(x)) + 1 + k


def fold_days(n, point=Q(1, 2)):
    born = {Q(0): 0}
    for day in range(1, n + 1):
        xs = sorted(born)
        new = [a + (b - a) * point for a, b in zip(xs, xs[1:])] + [xs[-1] + 1, xs[0] - 1]
        for v in new:
            born[v] = day
    return born


def test_fold_day_equals_conway_birthday():
    born = fold_days(DAYS)
    assert len(born) == 1023
    assert all(birthday(x) == d for x, d in born.items())


def test_a_fold_at_one_third_fails_the_birthday_oracle():
    born = fold_days(DAYS, point=Q(1, 3))
    assert not all(birthday(x) == d for x, d in born.items())


def test_simplest_number_in_every_gap_is_the_average():
    born = fold_days(DAYS)
    for day in range(DAYS - 1):
        xs = sorted(x for x, d in born.items() if d <= day)
        for a, b in zip(xs, xs[1:]):
            inside = [x for x in born if a < x < b]
            simplest = min(inside, key=lambda x: (birthday(x), abs(x)))
            assert simplest == (a + b) / 2


def test_every_inner_gap_repeats_the_unit_interval_pattern():
    born = fold_days(DAYS)
    d = 4
    ref = sorted(x for x, t in born.items() if 0 < x < 1 and t <= 1 + d)
    for day in range(1, DAYS - d):
        xs = sorted(x for x, t in born.items() if t <= day)
        for a, b in zip(xs, xs[1:]):
            if (a >= 0 and b <= 1) or a >= 1:
                inner = sorted((x - a) / (b - a) for x, t in born.items() if a < x < b and t <= day + d)
                assert inner == ref


def test_fold_path_to_one_third_converges_at_rate_two_to_minus_n():
    target, lo, hi, x = Q(1, 3), None, None, Q(0)
    for n in range(1, 40):
        if target > x:
            lo = x
            x = x + 1 if hi is None else (x + hi) / 2
        else:
            hi = x
            x = x - 1 if lo is None else (lo + x) / 2
        if n >= 3:
            assert abs(x - target) <= Q(1, 2 ** (n - 2))
