#!/usr/bin/env python3
"""Exact algebra for MIXED_GLOBAL_SHORT_RUN_PERIOD.md.

Run: python explorations/mixed_global_short_run_certificate.py
The hand domain is a complete normal (--+)^m period, with positive
strict-star arcs and the actual twisted endpoints. This file checks only
the displayed identities, not PMP, uniform signs, global comparison for
m>=5, numerical examples, or a length catalogue. No Lean/Lake/CI.
"""
import platform

import sympy as s

a, b, c, h, u, v, w, K = s.symbols("a b c h u v w K", positive=True)
R = s.Matrix([[0, 1], [-1, 1]])
e1, e2 = s.Matrix([1, 0]), s.Matrix([0, 1])
checks = 0


def check(expr, label):
    global checks
    zero = s.zeros(*expr.shape) if isinstance(expr, s.MatrixBase) else s.Integer(0)
    if s.simplify(expr) != zero:
        raise AssertionError(label)
    checks += 1


def A(q, eps):
    return s.diag(q, 1 / q) * R ** (-eps)


product = w * A(K / (h * u), -1) * A(v / u, 1) * A(v / w, -1) * e2
check(product - K * e1 / h - h * (u * u + w * w - v * v) * e2 / K, "collapsed three-factor recurrence")
check(s.det(s.Matrix.hstack(-e1 / h, h * e2 / K)) + 1 / K, "negative centre Wronskian")

G = (
    3 * a * b - 4 - (a * a + b * b) * s.log(a + b)
    + a * a * s.log(a * a + 4) / 2
    + b * b * s.log(b * b + 4) / 2
)
check(a * s.diff(G, a) + b * s.diff(G, b) - 2 * G - 16 / (a * a + 4) - 16 / (b * b + 4), "signed-action Euler identity")

D = (a + b) ** 2 + (a + c) ** 2 - (b + c) ** 2
check(D + 2 * ((b - a) * (c - a) - 2 * a * a), "two-centre bridge constraint")
x, z = s.symbols("x z", positive=True)
check((x + 1) * (z + 1) - 2 * x * z + (x * z - x - z - 1), "paired product identity")
tau = s.symbols("tau", positive=True)
check(4 / (4 / (tau - 1) + 4) - (1 - 1 / tau), "cost in the scale parameter")
check(1 - 1 / (6 + 4 * s.sqrt(2)) - (s.sqrt(2) - s.Rational(1, 2)), "exact cost threshold")
check(s.Integer(545) ** 2 - 3 * s.Integer(308) ** 2 - 12433, "rational comparison numerator")
assert 12433 > 0

print(f"Python {platform.python_version()}, SymPy {s.__version__}.")
print(f"PASS: {checks} exact short-run recurrence, Euler and two-centre identities.")
print("The whole-period PMP interpretation and inequalities are hand arguments in the note.")
