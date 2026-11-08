#!/usr/bin/env python3
"""Exact identities for MIXED_GLOBAL_COSTATE_ELLIPTIC.md.

Run: python explorations/mixed_global_ellipticity_certificate.py
Domain of the hand theorem: finite positive strict-star normal PMP periods
with the actual twisted endpoints. Symbols below check only the displayed
local rational/differential identities; full PMP, run classification and
projective cyclic contradiction are proved in the note. No sampled inputs,
optimization, trajectory integration, word enumeration, Lean, Lake or CI.
"""
import platform

import sympy as s

a, p, n, t = s.symbols("a p n t", positive=True)
u, v, w = s.symbols("u v w", real=True)
sm, sp, K = a + p, a + n, a * a + 4
R = s.Matrix([[0, 1], [-1, 1]])
E = s.diag(1, -1)
J0 = s.Matrix([[0, -1], [1, 0]])
M = s.Matrix([[u, v], [w, -u]])
S = -J0 * M
checks = 0


def check(expr, label):
    global checks
    zero = s.zeros(*expr.shape) if isinstance(expr, s.MatrixBase) else s.Integer(0)
    if s.simplify(expr) != zero:
        raise AssertionError(label)
    checks += 1


def transfer(q, eps):
    return s.diag(q, 1 / q) * R ** (-eps)


# The four exact factor/column cases in a single prefix frame.
for before, after in ((1, 1), (-1, -1), (-1, 1), (1, -1)):
    q = sm**before * sp**after * K ** (-(before + after) // 2)
    A = transfer(q, after)
    V = (
        before * (R**before * E * R**(-before) + E) / sm
        + after * (E + A * E * A.inv()) / sp
        - (before + after) * a * E / K
    )
    ym = -s.Matrix([0, 1]) / sm if before == 1 else -s.Matrix([1, 0]) / sm
    yp = q * s.Matrix([1, 0]) / sp if after == 1 else s.Matrix([0, 1]) / (q * sp)
    dm = (ym.T * S * ym)[0]
    dp = (yp.T * S * yp)[0]
    e = (ym.T * S * yp)[0]
    if before == after:
        expected = (
            2 * s.Matrix([[-a / K, q * q / sp], [-1 / sm, a / K]])
            if after == 1
            else 2 * s.Matrix([[a / K, -1 / sm], [1 / (q * q * sp), -a / K]])
        )
        check(V - expected, f"column {before},{after}")
        check(s.det(s.Matrix.hstack(ym, yp)) - after / K, f"Wronskian {after}")
        check(e - u / K, f"Gram cross term {after}")
        check(dm * dp - e * e - M.det() / K**2, f"Gram determinant {after}")
        check(s.trace(M * V) - 2 * after * (sm * dm + sp * dp - 2 * a * e), f"stationarity {after}")
    else:
        nilpotent = s.Matrix([[0, 1], [0, 0]]) if after == 1 else s.Matrix([[0, 0], [1, 0]])
        check(V - 2 * (n - p) * nilpotent / sm**2, f"turn column {before},{after}")
        check(yp + ym, f"antiparallel turn vectors {before},{after}")
        check(s.trace(M * V) - 2 * after * (n - p) * dp, f"turn stationarity {before},{after}")
    Kappa = s.diag(1 / q, q) * M * s.diag(q, 1 / q)
    switch_value = Kappa[1, 0] if after == 1 else -Kappa[0, 1]
    check(switch_value - sp**2 * dp, f"switch Gram diagonal {before},{after}")

# Signed cyclic action and its turn secant.
b = s.symbols("b", positive=True)
G = (
    3 * a * b - 4 - (a * a + b * b) * s.log(a + b)
    + a * a * s.log(a * a + 4) / 2
    + b * b * s.log(b * b + 4) / 2
)
f = lambda z: z - 1 / z - s.log(z)
h = lambda z: s.log(z) - 1 + 1 / z
check(s.expand_log(s.diff(G, a) / a - 2 * f(1 + b / a) - h(K / a**2), force=True), "action derivative decomposition")
check(s.diff(f(t), t) - s.Rational(3, 4) - (t - 2) ** 2 / (4 * t**2), "strict secant lower bound")
check(1 - s.diff(f(t), t) - (t - 1) / t**2, "strict secant upper bound")

# Both physical switch derivative calculations, with the state constraint.
c = (4 - a * b) / (a + b)
state = s.Matrix([a, b])
f0 = s.Matrix([0, a + b])
f1 = s.Matrix([-a - b, 0])
f2 = s.Matrix([a + c, -b - c])
D0 = s.diag(-1, 1)
D1 = s.Matrix([[1, -2], [0, -1]])
D2 = s.Matrix([[1, 0], [2, -1]])
l0, l1, l2 = [z * (a + b + c) / 8 for z in (a, b, c)]
grad = lambda z: s.Matrix([s.diff(z, x) for x in state])
check(f1.jacobian(state) * f0 - f0.jacobian(state) * f1 - f0 - f1, "forward state bracket")
check(f2.jacobian(state) * f0 - f0.jacobian(state) * f2 + f0 + f2, "reverse state bracket")
check(D0 * D1 - D1 * D0 + D0 + D1 - 2 * s.Matrix([[0, 1], [0, 0]]), "forward group bracket")
check(D0 * D2 - D2 * D0 - D0 - D2 - 2 * s.Matrix([[0, 0], [1, 0]]), "reverse group bracket")
check(grad(l0).dot(f1) - grad(l1).dot(f0) + l0 + l1 + (a * a + a * b + b * b) / 4, "forward cost bracket")
check(grad(l0).dot(f2) - grad(l2).dot(f0) - l0 - l2 - (a * a + a * c + c * c) / 4, "reverse cost bracket")

# The two off-diagonal estimates use the same exact scalar expression.
r = sm * sp / K
ell = 1 / sm + 1 / sp
C = (p + a + n - a * a * ell + a**3 / K - a * s.log(r)) / 4
jm = (p * p + p * a + a * a) / (4 * sm**2)
jp = (a * a + a * n + n * n) / (4 * sp**2)
check(sm * jm + sp * jp - (p + n + a * a * ell) / 4, "weighted edge derivatives")
check((sm * jm + sp * jp - C) / (4 * a) - (-1 + 2 * a * ell - a * a / K + s.log(r)) / 16, "cross-Gram threshold")
check(jp / 2 - s.Rational(3, 32) - (a - n) ** 2 / (32 * sp**2), "forward diagonal threshold")

print(f"Python {platform.python_version()}, SymPy {s.__version__}.")
print(f"PASS: {checks} exact mixed-action, Gram and switching identities.")
print("The theorem also requires the hand full-PMP, run and projective-periodicity arguments.")
