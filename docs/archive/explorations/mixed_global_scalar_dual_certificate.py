#!/usr/bin/env python3
"""Exact identities for MIXED_GLOBAL_SCALAR_DUAL.md.

Run: python3 explorations/mixed_global_scalar_dual_certificate.py
Domain: the same signed factor formulas for actual positive physical
margins and real auxiliary variables with positive adjacent sums.
The prefix is determinant one, and its normalized primary multiplier
is positive elliptic in triangular coordinates. This script checks
algebraic identities only. Geometry, winding branches, PMP, endpoint
rank, and the bordered-Hessian inertia are hand arguments in the note.
It proves no negative subspace or remaining cost-case exclusion.

No numerical samples, optimizer, trajectory integration, growing word
catalogue, Lean, Lake, typechecking, or CI are used.
"""

import platform

import sympy as s

checks = 0


def check(expr, label):
    global checks
    zero = s.zeros(*expr.shape) if isinstance(expr, s.MatrixBase) else s.Integer(0)
    if s.simplify(expr) != zero:
        raise AssertionError(label)
    checks += 1


R = s.Matrix([[0, 1], [-1, 1]])
q, h, k = s.symbols("q h k", positive=True)
b = s.symbols("b", real=True)
M = s.Matrix([[b / 2, -h], [k, -b / 2]])
for eps in (1, -1):
    A = s.diag(q, 1 / q) * R ** (-eps)
    new = s.simplify(A.inv() * M * A)
    bn = 2 * new[0, 0]
    target = q * q * k if eps == 1 else h / (q * q)
    check((b + bn) / 2 - target, f"positive adjacent auxiliary sum {eps}")
    component = -new[0, 1] if eps == 1 else new[1, 0]
    check(component - target, f"next incoming component {eps}")

sm, sp = s.symbols("sm sp", positive=True)
Kb = b * b + 4
for ep, en in ((1, 1), (-1, -1), (-1, 1), (1, -1)):
    if ep == en == 1:
        q2 = sm * sp / Kb
        check((sm / 2) * (sp / (2 * q2)) - Kb / 4, "auxiliary ++ factor")
    elif ep == en == -1:
        q2 = Kb / (sm * sp)
        check((sm / 2) * (q2 * sp / 2) - Kb / 4, "auxiliary -- factor")
    elif ep == -1:
        q2 = sp / sm
        check(sm / 2 - sp / (2 * q2), "auxiliary -+ factor")
    else:
        q2 = sm / sp
        check(sm / 2 - q2 * sp / 2, "auxiliary +- factor")

# One signed formula covers the four local potential derivatives.
x, a, y = s.symbols("x a y", real=True)
ep, en = s.symbols("ep en", real=True)
delta = (ep + en) / 2
sm, sp, K = x + a, a + y, a * a + 4
phi = ep * sm * s.log(sm) + en * sp * s.log(sp)
phi -= delta * (a * s.log(K) + 4 * s.atan(a / 2))
ell = ep * s.log(sm) + en * s.log(sp) - delta * s.log(K)
check(s.diff(phi, a) - ell, "signed potential gradient")
diag = ep / sm + en / sp - 2 * delta * a / K
check(ep * x / sm + diag * a + en * y / sp - 8 * delta / K,
      "signed B scaling")
bm, bi, bp = s.symbols("bm bi bp", real=True)
ddiag = -ep * (bm + bi) / sm**2 - en * (bi + bp) / sp**2
ddiag -= 2 * delta * bi * (4 - a * a) / K**2
db_a = -ep * (bm + bi) * x / sm**2 + ddiag * a
db_a -= en * (bi + bp) * y / sp**2
bb = ep * bm / sm + diag * bi + en * bp / sp
check(db_a + bb + 16 * delta * a * bi / K**2,
      "signed directional scaling")

# Polynomial column identities; determinant one is imposed only after
# the general identity with det(P) has been checked.
A, B, C, D0 = s.symbols("A B C D0", real=True)
P = s.Matrix([[A, B], [C, D0]])


def auxiliary_and_kernel(mat):
    aa, bb, cc, dd = mat[0, 0], mat[0, 1], mat[1, 0], mat[1, 1]
    aux = -2 * (aa * bb + cc * dd)
    vec = s.Matrix([2 * (aa * dd + bb * cc), 2 * (cc * dd - aa * bb)])
    return aux, vec


b0, z0 = auxiliary_and_kernel(P)
check(z0.dot(z0) - b0 * b0 - 4 * P.det() ** 2, "nonvanishing kernel pair")
for eps in (1, -1):
    new = P * s.diag(q, 1 / q) * R ** (-eps)
    bn, zn = auxiliary_and_kernel(new)
    check(s.det(s.Matrix.hstack(z0, zn)) - 2 * eps * (b0 + bn) * P.det(),
          f"signed kernel Wronskian {eps}")

c, t = s.symbols("c t", positive=True)
j = (a * a + a * y + y * y) / (4 * sp**2)
d = c * t / (2 * sp**2)
for eps in (1, -1):
    beta = eps * (2 * d - j)
    block = eps * s.Matrix([[j + 2 * d, -c / sp], [-c / sp, c / (2 * t)]])
    check(block.det() + eps * c * beta / (2 * t), f"signed adjacent block {eps}")

    # Here t=bi+bp; division by physical a,y is permitted. There is
    # no division by either real auxiliary variable.
    ti, tn = 2 * bi / a, 2 * bp / y
    off = eps * (j + c * (bi + bp) / sp**2 - c * (ti + tn) / sp
                 + c * ti * tn / (2 * (bi + bp)))
    beta2 = eps * (c * (bi + bp) / sp**2 - j)
    square = 2 * eps * c * a * y * (bi / a - bp / y) ** 2
    square /= sp**2 * (bi + bp)
    check(off + beta2 + square, f"signed ratio graph {eps}")

CostGrad = s.symbols("CostGrad", real=True)
Ma = 2 * CostGrad + delta * (16 * c * bi - 8) * a / K**2
Ga = Ma - 2 * CostGrad + (2 * bi / a) * (
    -8 * c * delta / K + 8 * c * delta / (bi * bi + 4)
)
target = delta * (
    16 * c * bi * (a**4 + 8 * a*a - 4 * bi*bi)
    - 8 * a*a * (bi*bi + 4)
) / (a * K*K * (bi*bi + 4))
check(Ga - target, "signed ratio-graph scaling row")

print(f"Python {platform.python_version()}, SymPy {s.__version__}.")
print(f"PASS: {checks} exact signed scalar-dual identities.")
print("The full-period winding/index interface is a hand argument; the negative-subspace sign remains open.")
