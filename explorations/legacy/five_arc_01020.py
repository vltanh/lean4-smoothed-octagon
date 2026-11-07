"""Exact exploratory algebra for the admissible-word orbit 01020.

Domain: 0 < u,v < 1 and u+v+uv > 1. These inequalities are mathematical
hypotheses, not conditions decided by this script. Tangent factors are
P(u),Q(u),4uv/((1-u^2)(1-v^2)),Q(v),P(v). All are strictly greater than
one on that domain. The initial state is the shape forced by the group
and state endpoints, as derived in docs/FIVE_ARC_PROGRESS.md.

Reproduction: python explorations/five_arc_01020.py
Used Python 3.12.14 and SymPy 1.14.0. All residuals use exact rational
expressions. No floating point optimization, sampled inequality, search
over longer words, or Lean execution occurs.

This script is exploratory/reproducibility support, not a proof
certificate. In particular it does not prove the logarithmic envelope
or the unrestricted Reinhardt conjecture. The independent hand proof,
including the cost cancellation and all inequalities, is in the doc.
"""

import sys

import sympy as sp


def factor_matrix(matrix):
    return matrix.applyfunc(sp.factor)


def tangent(i, q):
    if i == 0:
        return sp.diag(q, 1 / q)
    if i == 1:
        return sp.Matrix([[1 / q, q - 1 / q], [0, q]])
    return sp.Matrix([[1 / q, 0], [1 / q - q, q]])


def main():
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    u, v = sp.symbols("u v", positive=True)
    d = (1 - u) * (1 - v)
    N = d * (4 - d)
    A = (1 + u) * (1 - v)
    B = (1 - u) * (1 + v)
    p = (1 + u**2) / (2 * u)
    q = (1 + u**2) / (1 - u**2)
    r = 4 * u * v / ((1 - u**2) * (1 - v**2))
    s = (1 + v**2) / (1 - v**2)
    z = (1 + v**2) / (2 * v)
    letters = [0, 1, 0, 2, 0]
    factors = [p, q, r, s, z]
    R = sp.Matrix([[0, 1], [-1, 1]])

    product = sp.eye(2)
    for i, w in zip(letters, factors, strict=True):
        product = factor_matrix(product * tangent(i, w))
    print("tangent endpoint residual:", factor_matrix(product - R))
    print("positive half-factor denominator squared residual:",
          sp.factor(p * q * r * s * z - (q * s)**2))
    Hnum = sp.Matrix([
        [q * s, p * s * (1 - q)],
        [z * q * (s - 1), p * z * (r - (s - 1) * (q - 1))],
    ])
    H = sp.Matrix([[1, -u], [v, 1 - u * v]])
    print("half-factor holonomy residual:",
          factor_matrix(Hnum / (q * s) - H))

    K = R * H
    numerator = 2 * K - sp.trace(K) * sp.eye(2)
    controls = [
        sp.diag(1, -1),
        sp.Matrix([[-1, 2], [0, 1]]),
        sp.Matrix([[-1, 0], [-2, 1]]),
    ]
    print("state numerator determinant residual:",
          sp.factor(numerator.det() - N))
    print("initial positive-margin numerator residuals:", [
        sp.factor(-sp.trace(Z * numerator) - 2 * m)
        for Z, m in zip(controls, [A, d, B], strict=True)
    ])

    raw = [A, d, B]
    algebra = 0
    active = []
    for i, w in zip(letters, factors, strict=True):
        a = raw[i]
        b = raw[(i + 1) % 3]
        c = raw[(i - 1) % 3]
        active.append(sp.factor(a))
        algebra += a * ((a + b) * (w - 1) +
                        (a + c) * (1 - 1 / w)) / 2
        raw[(i + 1) % 3] = sp.factor((a + b) * w - a)
        raw[(i - 1) % 3] = sp.factor((a + c) / w - a)
    print("final raw state-twist residuals:", [
        sp.factor(x - y) for x, y in zip(raw, [B, A, d], strict=True)
    ])
    print("active raw-margin residuals:", [
        sp.factor(x - y)
        for x, y in zip(active, [A, d / u, d, d / v, B], strict=True)
    ])
    print("algebraic part of N*density residual:",
          sp.factor(algebra - 2 * d * (d + 2)))
    print("logarithmic coefficients of N*density:", [
        sp.factor(-a**2 / 2) for a in active
    ])


if __name__ == "__main__":
    main()

