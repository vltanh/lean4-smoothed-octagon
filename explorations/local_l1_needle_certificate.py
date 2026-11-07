"""Exact supplementary certificate for the unequal-factor L1 example.

Domain/input: only the fixed positive six-arc tuple in
docs/LOCAL_FORWARD_SIX.md, word 012012, raw initial margins
(1, 1, 4761/3950), scale squared 1975/1684, factors
(11/10, 11/10, 121/100, 121/100, 11/10, 121/100).
The initial state is fixed. The endpoint coordinates are the first three
tangent-matrix entries and the first two final raw margins. Elapsed time
is free. Each of the twelve non-active insertions is an arbitrary partial
factor z in the corresponding whole closed arc, not a time sample.

Run from the repository root:
    python explorations/local_l1_needle_certificate.py

Tested with Python 3.12.14 and SymPy 1.14.0. No random inputs, optimization,
interval mesh, Lean, Lake, typechecking, or CI are used. The script checks
finite identities and rational bounds printed in
docs/LOCAL_FORWARD_NEEDLE_AUDIT.md. The hand proof there is the certificate;
symbolic equality output is supplementary and is not a proof premise.
An assertion failure prints its exact row and expression. This script
does not search for or rule out a distant endpoint-matching replacement,
and does not establish a universal statement on the L1 parameter domain.
"""

import platform

import sympy as s


L, z, H = s.symbols("L z H")
r = s.Rational(11, 10)
qs = [r, r, r * r, r * r, r, r * r]
logs = [L, L, 2 * L, 2 * L, L, 2 * L]
word = [0, 1, 2, 0, 1, 2]
p0 = [s.Integer(1), s.Integer(1), s.Rational(4761, 3950)]
invariant = p0[0] * p0[1] + p0[1] * p0[2] + p0[2] * p0[0]
lo, hi = s.Rational(9531, 100000), s.Rational(95311, 1000000)


def tangent(i, q):
    return [
        s.diag(q, 1 / q),
        s.Matrix([[1 / q, q - 1 / q], [0, q]]),
        s.Matrix([[1 / q, 0], [1 / q - q, q]]),
    ][i]


def tangent_derivative(i, q):
    return [
        s.diag(1, -1 / q**2),
        s.Matrix([[-1 / q**2, 1 + 1 / q**2], [0, 1]]),
        s.Matrix([[-1 / q**2, 0], [-1 / q**2 - 1, 1]]),
    ][i]


def first_jet(labels, factors, derivatives, logarithms):
    """Differentiate the displayed state/product/cost recurrences once."""
    p = list(p0)
    dp = [s.Integer(0)] * 3
    frame, dframe = s.eye(2), s.zeros(2)
    cost_derivative = s.Integer(0)
    for i, q, dq, logq in zip(labels, factors, derivatives, logarithms):
        a, b, c = p[i], p[(i + 1) % 3], p[(i - 1) % 3]
        da, db, dc = dp[i], dp[(i + 1) % 3], dp[(i - 1) % 3]
        integrand = (a + b) * (q - 1) + (a + c) * (1 - 1 / q) - a * logq
        dintegrand = (
            (da + db) * (q - 1)
            + (a + b) * dq
            + (da + dc) * (1 - 1 / q)
            + (a + c) * dq / q**2
            - da * logq
            - a * dq / q
        )
        cost_derivative += da * integrand + a * dintegrand
        dframe = (
            dframe * tangent(i, q) + frame * tangent_derivative(i, q) * dq
        ).applyfunc(s.cancel)
        frame = (frame * tangent(i, q)).applyfunc(s.cancel)
        p[(i + 1) % 3] = s.cancel((a + b) * q - a)
        p[(i - 1) % 3] = s.cancel((a + c) / q - a)
        dp[(i + 1) % 3] = s.cancel((da + db) * q + (a + b) * dq - da)
        dp[(i - 1) % 3] = s.cancel(
            (da + dc) / q - (a + c) * dq / q**2 - da
        )
    return (
        s.Matrix([dframe[0, 0], dframe[0, 1], dframe[1, 0], dp[0], dp[1]]),
        s.cancel(cost_derivative / (2 * invariant)),
    )


# a, b(L), c(L), d(L), positive numerator factor, positive denominator.
rows = {
    (0, 1): (-18117459470, 12611108760 - 40122415960 * L,
             62252117026 * L - 5637010786, -9058729735, 5, 154480008848),
    (0, 2): (3260768376925, -1478594316250,
             909938012265 - 13829191281815 * L,
             16320874555359 * L + 348178853677, 1, 5042942437600 * z**2),
    (1, 0): (494112531, -269515926, 1003060399 * L - 45761793,
             315277719 - 1003060399 * L, 1, 638347144 * z**2),
    (1, 2): (-2366799023490, 189943435000 * L + 1028895579000,
             2157861244990 * L + 39261561570, -1288151368317, 1, 3050980174748),
    (2, 0): (-554990530600, 2258091000000 * L + 10170650000,
             265188778800 - 1622309048800 * L, -335769271013, 1, 762745043687),
    (2, 1): (10985143147, -5549905306, 405427411 - 949717175 * L,
             949717175 * L + 5144477895, 1, 12607356094 * z**2),
    (3, 1): (-66460116039350, 4748585875000 * L + 25722389475000,
             127174443169950 * L + 2452835836550, -40628081792573,
             1, 92292150286127),
    (3, 2): (45866986, -22933493, 21916428 - 225809100 * L,
             225809100 * L + 1017065, 121, 6303678047 * z**2),
    (4, 0): (21516354759, -10645879077, 356923287 - 1899434350 * L,
             1899434350 * L + 10288955790, 1, 25214712188 * z**2),
    (4, 2): (-27176189205, 15763885950 - 50153019950 * L,
             82344511150 * L - 2516898615, -16305713523, 1, 38620002212),
    (5, 0): (-7173690429235, 32641749110718 * L + 696357707354,
             2001863626983 - 23250530390758 * L, -3578198245325,
             1, 12203920698992),
    (5, 1): (823520885, -374327675, 2006120798 * L - 256227763,
             630555438 - 2006120798 * L, 1, 1276694288 * z**2),
}


# Integer open bounds for 10^6 times f(1), f(q), f'(1), f'(q).
# A singleton (0, 0) denotes the exact zero identity.
bounds = {
    (0, 1): [(1355, 1357), (0, 0), (-13642, -13640), (-11953, -11950)],
    (0, 2): [(5214, 5216), (2315, 2317), (-32065, -32060), (-27444, -27440)],
    (1, 0): [(0, 0), (382, 384), (9958, 9961), (-3823, -3819)],
    (1, 2): [(1594, 1596), (0, 0), (-11777, -11775), (-18614, -18612)],
    (2, 0): [(336, 338), (0, 0), (11449, 11456), (-8603, -8597)],
    (2, 1): [(0, 0), (2198, 2201), (18228, 18229), (-3344, -3341)],
    (3, 1): [(1816, 1819), (0, 0), (6976, 6979), (-18229, -18228)],
    (3, 2): [(0, 0), (406, 409), (8597, 8603), (-10781, -10777)],
    (4, 0): [(0, 0), (1754, 1756), (18612, 18614), (14966, 14968)],
    (4, 2): [(347, 349), (0, 0), (4516, 4518), (-9961, -9958)],
    (5, 0): [(2104, 2107), (11507, 11508), (31650, 31657), (63945, 63952)],
    (5, 1): [(0, 0), (3114, 3118), (11950, 11953), (11660, 11666)],
}
second_bounds = {
    (0, 2): (r, 2191, 2192),
    (1, 0): (s.Integer(1), -90910, -90909),
    (1, 2): (r, -24353, -24352),
    (2, 0): (r * r, -14219, -14210),
    (2, 1): (s.Integer(1), -10439, -10438),
    (3, 1): (r * r, -38757, -38756),
    (3, 2): (s.Integer(1), 0, 0),
    (4, 2): (r, -100755, -100750),
    (5, 0): (s.Integer(1), 61501, 61511),
}


def formal_derivative(expr):
    return s.diff(expr, z) + s.diff(expr, H) / z


def at_endpoint(expr, at):
    logat = s.Integer(0) if at == 1 else L if at == r else 2 * L
    return s.cancel(expr.subs({z: at, H: logat}))


def check_affine_interval(expr, lower, upper, label):
    expr = s.cancel(expr)
    if lower == upper == 0:
        assert expr == 0, (label, expr)
        return
    assert s.diff(expr, L, 2) == 0, (label, "not affine", expr)
    values = [s.cancel(10**6 * expr.subs(L, endpoint)) for endpoint in (lo, hi)]
    assert min(values) > lower and max(values) < upper, (label, expr, values)


def main():
    print("Python", platform.python_version(), "SymPy", s.__version__)
    columns, gradient = [], []
    for index in range(6):
        endpoint, cost = first_jet(
            word, qs, [int(j == index) for j in range(6)], logs
        )
        columns.append(endpoint)
        gradient.append(cost)
    matrix = s.Matrix.hstack(*columns)
    gradient = s.Matrix(gradient)
    multiplier = gradient[:5, 0].T * matrix[:, :5].inv()
    minor = s.factor(matrix[:, :5].det())
    assert minor == -s.Rational(67030484100398003034549, 64896648437500000000000)
    assert all(s.cancel(e) == 0 for e in gradient.T - multiplier * matrix)
    print("rank-five minor:", minor)
    print("stationary multiplier:", multiplier.applyfunc(s.factor))

    for (arc, control), row in rows.items():
        a, b, c, d, numerator_factor, denominator = map(s.sympify, row)
        polynomial = a * z * H + b * z**2 + c * z + d
        labels = word[:arc] + [word[arc], control, word[arc]] + word[arc + 1:]
        factors = qs[:arc] + [z, s.Integer(1), qs[arc] / z] + qs[arc + 1:]
        logarithms = logs[:arc] + [H, 0, logs[arc] - H] + logs[arc + 1:]
        derivative = [0] * (arc + 1) + [1] + [0] * (6 - arc)
        endpoint, cost = first_jet(labels, factors, derivative, logarithms)
        defect = s.cancel(cost - (multiplier * endpoint)[0])
        assert s.cancel(defect - numerator_factor * polynomial / denominator) == 0, (arc, control)
        normalized = polynomial / abs(a)
        first = formal_derivative(normalized)
        second = formal_derivative(first)
        expressions = [
            at_endpoint(normalized, s.Integer(1)),
            at_endpoint(normalized, qs[arc]),
            at_endpoint(first, s.Integer(1)),
            at_endpoint(first, qs[arc]),
        ]
        for index, (expr, interval) in enumerate(zip(expressions, bounds[(arc, control)])):
            check_affine_interval(expr, *interval, (arc, control, index))
        if (arc, control) in second_bounds:
            point, lower, upper = second_bounds[(arc, control)]
            check_affine_interval(at_endpoint(second, point), lower, upper, (arc, control, 2, point))
        print("verified whole-arc identity and rational sign bounds:", arc, control, flush=True)

    # The logarithmic enclosure is itself reduced to rational arithmetic.
    lower_series = s.Rational(2648, 27783)
    upper_series = lower_series + s.Rational(1, 10187100)
    assert lo < lower_series < upper_series < hi
    print("All twelve identities, endpoint uniqueness, crossing bounds, and logarithm bounds pass.")
    print("Scope: one exact eligible L1 tuple; no distant-replacement or universal-optimality claim.")


if __name__ == "__main__":
    main()
