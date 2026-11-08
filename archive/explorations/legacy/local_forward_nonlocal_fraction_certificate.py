#!/usr/bin/env python3
"""Check the exact finite data for one nonlocal L1 replacement.

Command (from the repository root):
    python3 explorations/local_forward_nonlocal_fraction_certificate.py

Only Python's standard library is used. All arithmetic in the certificate is
fractions.Fraction arithmetic; no optimizer, floating-point evaluation,
symbolic differentiation package, random input, or word search is used.
Verified with Python 3.12.14; the running version is also printed.

Finite input:
  * source word 012012, factors (r, r, r^2, r^2, r, r^2), r = 11/10;
  * replacement word 012021, first factor fixed at 59/50;
  * the five rational center factors displayed in CENTER_NUMERATORS below;
  * fixed raw initial margins (1, 1, 4761/3950), physical scale^2 = 1975/1684;
  * the closed infinity-norm ball of radius 10^-15 in the last five factors.

The endpoint Jacobian is propagated by explicitly differentiating the matrix
product and margin recurrences. The script checks the proposed preconditioner,
residual enclosures, center margins, rational logarithm enclosures, and the
contraction and cost inequalities. A failed inequality raises ArithmeticError.

Scope: the uniform endpoint-Jacobian change bound 102400 per unit radius
and total physical-cost derivative bound 10^8 are proved in Sections 2–3
of LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md; this checks its independent appendix. They are not inferred from evaluating the center.
This checker verifies their stated rational consequences; it does not replace
that analytic proof or assert universal improvement for L1. No Lean, Lake,
typecheck, CI, or external dependency is invoked. The Python version is printed.
"""

from fractions import Fraction as Q
import platform


SOURCE_WORD = (0, 1, 2, 0, 1, 2)
REPLACEMENT_WORD = (0, 1, 2, 0, 2, 1)
INITIAL = (Q(1), Q(1), Q(4761, 3950))
SCALE_SQUARED = Q(1975, 1684)
R = Q(11, 10)
SOURCE_FACTORS = (R, R, R * R, R * R, R, R * R)
CENTER_NUMERATORS = (
    1121447939284173062,
    1314499725816582306,
    1132952499501451505,
    1133658541831577454,
    1090582634926571007,
)
CENTER_FACTORS = (Q(59, 50),) + tuple(
    Q(n, 10**18) for n in CENTER_NUMERATORS
)
TARGET_FRAME = (
    (Q(5757428401, 11000000000), Q(487996509, 10**9)),
    (-Q(81027219, 110000000), Q(12237929, 10**7)),
)
TARGET_MARGINS = (Q(56321, 39500), Q(9, 11), Q(1))
PRECONDITIONER = tuple(
    tuple(Q(n, 1000) for n in row)
    for row in (
        (-2615, -1603, 832, -213, 602),
        (3910, -1066, -5951, -3595, -2512),
        (326, 1146, 405, 840, 720),
        (-954, 3574, 4859, 4262, 1977),
        (4697, 3571, -1533, 358, -1014),
    )
)


def check(condition, message):
    """Do not depend on Python's optional assertion execution."""
    if not condition:
        raise ArithmeticError(message)


def zero_matrix(rows, columns):
    return tuple(tuple(Q(0) for _ in range(columns)) for _ in range(rows))


def identity(size):
    return tuple(tuple(Q(i == j) for j in range(size)) for i in range(size))


def matrix_product(left, right):
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(len(right))), Q(0))
            for j in range(len(right[0]))
        )
        for i in range(len(left))
    )


def matrix_sum(left, right):
    return tuple(
        tuple(x + y for x, y in zip(left_row, right_row))
        for left_row, right_row in zip(left, right)
    )


def transition(label, factor):
    inverse = 1 / factor
    return (
        ((factor, Q(0)), (Q(0), inverse)),
        ((inverse, factor - inverse), (Q(0), factor)),
        ((inverse, Q(0)), (inverse - factor, factor)),
    )[label]


def transition_derivative(label, factor):
    """Ordinary derivative with respect to the single factor."""
    inverse_derivative = -1 / (factor * factor)
    return (
        ((Q(1), Q(0)), (Q(0), inverse_derivative)),
        ((inverse_derivative, 1 - inverse_derivative), (Q(0), Q(1))),
        ((inverse_derivative, Q(0)), (inverse_derivative - 1, Q(1))),
    )[label]


def evaluate(word, factors, variable_arcs=()):
    """Return endpoint, tangent matrix, all margins, and exact Jacobian.

    Each member of variable_arcs is one independently varying factor. Matrix
    derivatives use (F T)' = F' T + F T'. The two changing margins are
    differentiated directly, before updating any of the old values.
    """
    frame = identity(2)
    margins = INITIAL
    stages = [margins]
    frame_partials = [zero_matrix(2, 2) for _ in variable_arcs]
    margin_partials = [(Q(0), Q(0), Q(0)) for _ in variable_arcs]

    for arc, (label, factor) in enumerate(zip(word, factors)):
        growing = (label + 1) % 3
        decreasing = (label - 1) % 3
        a, b, c = margins[label], margins[growing], margins[decreasing]
        transfer = transition(label, factor)
        next_frame_partials = []
        next_margin_partials = []

        for column, variable_arc in enumerate(variable_arcs):
            dq = Q(arc == variable_arc)
            d_transfer = (
                transition_derivative(label, factor)
                if dq else zero_matrix(2, 2)
            )
            next_frame_partials.append(matrix_sum(
                matrix_product(frame_partials[column], transfer),
                matrix_product(frame, d_transfer),
            ))
            derivative = margin_partials[column]
            da, db, dc = (
                derivative[label], derivative[growing], derivative[decreasing]
            )
            updated = list(derivative)
            updated[growing] = (da + db) * factor + (a + b) * dq - da
            updated[decreasing] = (
                (da + dc) / factor - (a + c) * dq / factor**2 - da
            )
            next_margin_partials.append(tuple(updated))

        frame = matrix_product(frame, transfer)
        updated = list(margins)
        updated[growing] = (a + b) * factor - a
        updated[decreasing] = (a + c) / factor - a
        margins = tuple(updated)
        stages.append(margins)
        frame_partials = next_frame_partials
        margin_partials = next_margin_partials

    endpoint = (frame[0][0], frame[0][1], frame[1][0], margins[0], margins[1])
    columns = tuple(
        (dframe[0][0], dframe[0][1], dframe[1][0], dp[0], dp[1])
        for dframe, dp in zip(frame_partials, margin_partials)
    )
    jacobian = tuple(
        tuple(column[row] for column in columns) for row in range(5)
    )
    return endpoint, frame, tuple(stages), jacobian


def invariant(margins):
    a, b, c = margins
    return a * b + b * c + c * a


def logarithm_bounds(value):
    """Twelve terms of 2 atanh(h), with a positive geometric tail bound."""
    h = (value - 1) / (value + 1)
    check(0 < h < Q(1, 5), "logarithm input outside the stated finite domain")
    lower = 2 * sum((h**(2 * k + 1) / (2 * k + 1) for k in range(12)), Q(0))
    upper = lower + 2 * h**25 / (25 * (1 - h * h))
    return lower, upper


def physical_cost_bounds(word, factors, stages):
    """Enclose normalized physical cost C/sqrt(12), not unscaled raw cost."""
    lower = upper = Q(0)
    for label, factor, margins in zip(word, factors, stages[:-1]):
        a = margins[label]
        b = margins[(label + 1) % 3]
        c = margins[(label - 1) % 3]
        algebraic = a * ((a + b) * (factor - 1) + (a + c) * (1 - 1 / factor)) / 8
        log_lower, log_upper = logarithm_bounds(factor)
        # The logarithm coefficient is negative: lower log gives upper cost.
        lower += algebraic - a * a * log_upper / 8
        upper += algebraic - a * a * log_lower / 8
    return SCALE_SQUARED * lower, SCALE_SQUARED * upper


def main():
    print(f"Python {platform.python_version()}; standard-library Fraction arithmetic only")
    print("Finite input: source 012012, r=11/10; replacement 012021, first factor=59/50")
    print("Five center factors are the displayed integers / 10^18; radius=1/10^15")

    source_end, source_frame, source_stages, _ = evaluate(SOURCE_WORD, SOURCE_FACTORS)
    center_end, _, center_stages, jacobian = evaluate(
        REPLACEMENT_WORD, CENTER_FACTORS, variable_arcs=(1, 2, 3, 4, 5)
    )
    check(source_frame == TARGET_FRAME, "source tangent endpoint mismatch")
    check(source_stages[-1] == TARGET_MARGINS, "source terminal margins mismatch")
    check(SCALE_SQUARED * invariant(INITIAL) == 4, "physical state normalization mismatch")
    for margins in source_stages + center_stages:
        check(invariant(margins) == invariant(INITIAL), "margin invariant not preserved")
    check(all(m > 0 for p in source_stages for m in p), "source leaves the strict star domain")
    check(all(m > Q(74, 100) for p in center_stages for m in p), "center margin bound fails")
    print("PASS source endpoint exactly equals the stated target; all center raw margins > 74/100")

    radius = Q(1, 10**15)
    check(1 < CENTER_FACTORS[0] < Q(4, 3), "fixed replacement factor outside (1,4/3)")
    check(all(1 < q - radius and q + radius < Q(4, 3) for q in CENTER_FACTORS[1:]),
          "factor ball is not contained in (1,4/3)^5")
    check(Q(74, 100) - 4860 * radius > Q(73, 100), "neighborhood margin bound fails")
    print("PASS the entire factor ball stays in (1,4/3)^5; 74/100 - 4860*radius > 73/100")

    residual = tuple(x - y for x, y in zip(center_end, source_end))
    residual_enclosures = ((148, 149), (-166, -165), (72, 73), (68, 69), (36, 37))
    for value, (low, high) in zip(residual, residual_enclosures):
        check(Q(low, 10**20) < value < Q(high, 10**20), "endpoint residual enclosure fails")
    check(max(map(abs, residual)) < Q(2, 10**18), "endpoint residual norm bound fails")
    print("PASS residual * 10^20 lies in (148,149), (-166,-165), (72,73), (68,69), (36,37)")
    print("PASS ||E(center)-target||_infinity < 2/10^18")

    inverse_norm = max(sum(map(abs, row), Q(0)) for row in PRECONDITIONER)
    check(inverse_norm == Q(8517, 500) and inverse_norm < 18, "preconditioner norm mismatch")
    product = matrix_product(PRECONDITIONER, jacobian)
    row_bounds = (3434, 3533, 7981, 4599, 4566)
    for i, bound in enumerate(row_bounds):
        row_error = sum((abs(Q(i == j) - product[i][j]) for j in range(5)), Q(0))
        check(row_error < Q(bound, 10**6) < Q(1, 100), "inverse-defect row bound fails")
    print("PASS ||B0||_infinity = 8517/500 < 18")
    print("PASS rows of |I-B0*A| sum to less than (3434,3533,7981,4599,4566)/10^6 < 1/100")

    center_displacement = max(
        abs(sum((row[j] * residual[j] for j in range(5)), Q(0)))
        for row in PRECONDITIONER
    )
    displacement_bound = Q(36, 10**18)
    check(center_displacement < displacement_bound, "center displacement bound fails")
    jacobian_change_bound = 102400 * radius
    contraction_bound = Q(1, 100) + 18 * jacobian_change_bound
    check(contraction_bound < Q(1, 50), "contraction bound fails")
    check(displacement_bound + contraction_bound * radius < radius, "self-map bound fails")
    print("PASS ||B0*(E(center)-target)||_infinity < 36/10^18")
    print("PASS 1/100 + 18*102400*radius < 1/50; 36/10^18 + contraction*radius < radius")

    source_lower, _ = physical_cost_bounds(SOURCE_WORD, SOURCE_FACTORS, source_stages)
    _, center_upper = physical_cost_bounds(REPLACEMENT_WORD, CENTER_FACTORS, center_stages)
    check(center_upper < Q(4622907, 10**7), "center cost upper bound fails")
    check(source_lower > Q(4623011, 10**7), "source cost lower bound fails")
    cost_error_bound = 10**8 * radius
    check(cost_error_bound == Q(1, 10**7), "physical cost error normalization mismatch")
    certified_gap = Q(4623011 - 4622907, 10**7) - cost_error_bound
    check(certified_gap == Q(103, 10**7) > Q(1, 10**5), "strict improvement bound fails")
    check(source_lower - center_upper - cost_error_bound > Q(1, 10**5),
          "direct rational cost-enclosure comparison fails")
    print("PASS 12-term log bounds: center cost < 4622907/10^7; source cost > 4623011/10^7")
    print("PASS cost error <= 10^8*radius; source minus corrected cost > 103/10^7 > 1/10^5")
    print("All finite rational certificate checks passed.")
    print("Scope: neighborhood derivative bounds come from the hand proof; no universal L1 claim or numerical search.")


if __name__ == "__main__":
    main()
