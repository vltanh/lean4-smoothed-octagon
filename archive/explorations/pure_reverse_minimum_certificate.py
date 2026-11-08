#!/usr/bin/env python3
"""Exact algebra for GLOBAL_REVERSE_PERIOD_EXCLUSION.md.

Domain of the hand theorem: b,c>1, A,B,Z>0, AB+AZ+BZ=4,
Z>=A, B>=b*A+(b-1)*Z, B>=(2*c-1)*A.  The endpoint and cost
identities below hold symbolically without the determinant normalization
or inequalities.  No floating-point samples, root searches, or word-length
enumeration occur.  Positivity follows from the displayed hand argument,
not from SymPy assumptions or sampled numerical signs.

Run from the repository root:
    python explorations/pure_reverse_minimum_certificate.py

This checks a finite list of exact identities.  It does not verify the PMP
interface, the twisted seam, or a Lean proof; those are hand-proof inputs
and are stated explicitly in the accompanying note.
"""

import platform

import sympy as s


b, c, A, B, Z = s.symbols("b c A B Z", positive=True)
Lb, Lc = s.symbols("Lb Lc", real=True)
I = s.eye(2)
D = [
    s.Matrix([[-1, 0], [0, 1]]),
    s.Matrix([[1, -2], [0, -1]]),
    s.Matrix([[1, 0], [2, -1]]),
]
checks = 0


def zero(name, expression):
    """Check every entry of an exact symbolic scalar/matrix identity."""
    global checks
    entries = list(expression) if isinstance(expression, s.MatrixBase) else [expression]
    for entry in entries:
        assert s.factor(entry) == 0, (name, s.factor(entry))
    checks += 1
    print("PASS", name)


def factor(i, q):
    return ((q + 1 / q) * I + (1 / q - q) * D[i]) / 2


def half_factor(i, q):
    # Scalar multiple sqrt(q)*T_i(sqrt(q)); conjugations are unchanged.
    return ((q + 1) * I + (1 - q) * D[i]) / 2


def adjoint(matrix, vector):
    return matrix * vector * matrix.inv()


P = (B + Z) / b - Z
Q = b * A + (b - 1) * Z
E = (B - (c - 1) * A) / c
Y = s.Matrix([[-P, P + Z], [-P - Q, P]]) / 2
d0 = -A * b**3 * (c - 1)
w1 = B * (c - 1)
d1 = -(b**2 - 1) * (c - 1) * (A * b + B)
w2 = b * (A * (c - 1) + Z * (b - 1))
d2 = -b * (c - 1) * (b * B + (b - 1) * (c + 1) * Z)
d3 = -Z * b * c**2 * (b - 1)
labels = [0, 1, 2, 0, 1, 0]
factors = [s.S.One, s.S.One, b, s.S.One, c, s.S.One]
logs = [0, 0, Lb, 0, Lc, 0]
variation = [d0, w1, d1, w2, d2, d3]

print("Python", platform.python_version(), "; SymPy", s.__version__)
print("Exact formal four-arc/two-needle identities; no numerical sampling.")

F = I
G = I
delta_F = s.zeros(2)
delta_G = s.zeros(2)
for i, q, v in zip(labels, factors, variation):
    delta_F -= v * adjoint(F, D[i])
    delta_G -= v * adjoint(G, D[i]) / 2
    F = (F * factor(i, q)).applyfunc(s.factor)
    G = (G * half_factor(i, q)).applyfunc(s.factor)
zero("tangent product derivative", delta_F)
zero("state product stabilizer derivative", delta_G + 2 * b * (b - 1) * (c - 1) * Y)
zero("state commutator derivative", Y * delta_G - delta_G * Y)
zero("initial determinant invariant", P * Q + Q * Z + Z * P - (A * B + A * Z + B * Z))
zero("minimum inequality at first arc", b * (P - A) - (B - b * A - (b - 1) * Z))
zero("minimum inequality at last arc", c * (E - A) - (B - (2 * c - 1) * A))

# Differentiate the actual margin update and 8*J_i on each factor.
# The starting state is fixed while the factors vary.
margin = [P, Q, Z]
delta_margin = [s.S.Zero] * 3
delta_eight_J = s.S.Zero
for i, q, logarithm, v in zip(labels, factors, logs, variation):
    j, k = (i + 1) % 3, (i - 1) % 3
    active, growing, decreasing = margin[i], margin[j], margin[k]
    da, dg, dd = delta_margin[i], delta_margin[j], delta_margin[k]
    bracket = (active + growing) * (q - 1) + (active + decreasing) * (1 - 1 / q) - active * logarithm
    delta_bracket = (
        (da + dg) * (q - 1) + (active + growing) * q * v
        + (da + dd) * (1 - 1 / q) + (active + decreasing) * v / q
        - da * logarithm - active * v
    )
    delta_eight_J += da * bracket + active * delta_bracket
    margin[j] = (active + growing) * q - active
    margin[k] = (active + decreasing) / q - active
    delta_margin[j] = (da + dg) * q + (active + growing) * q * v - da
    delta_margin[k] = (da + dd) / q - (active + decreasing) * v / q - da
    margin = [s.factor(x) for x in margin]
    delta_margin = [s.factor(x) for x in delta_margin]
for i in range(3):
    zero("terminal margin derivative " + str(i), delta_margin[i])

eta_b, zeta_b = b - 1 - Lb, b * Lb - b + 1
eta_c, zeta_c = c - 1 - Lc, c * Lc - c + 1
N = b * (b - 1) * A * (A * c * eta_c - B * zeta_c) + (c - 1) * (
    b * A * (B + b * Z) * eta_b - B * (b * A + Z) * zeta_b
)
zero("exact cost derivative", delta_eight_J - 2 * Z * N)
constant = (b - 1) * (c - 1) * (b * c * A**2 + 3 * b * A * B + b**2 * A * Z + B * Z)
coefficient_b = -b * (c - 1) * ((b + 1) * A * B + b * A * Z + B * Z)
coefficient_c = -b * c * (b - 1) * A * (A + B)
zero("constant cost coefficient", N.subs({Lb: 0, Lc: 0}) - constant)
zero("log b cost coefficient", s.diff(N, Lb) - coefficient_b)
zero("log c cost coefficient", s.diff(N, Lc) - coefficient_c)

t, z, beta = s.symbols("t z beta", positive=True)
eta = t - 1 - s.log(t)
zeta = t * s.log(t) - t + 1
zero("eta derivative", s.diff(eta, t) - (1 - 1 / t))
denominator = t**2 + 4 * t + 1
logarithm_defect = s.log(t) - 3 * (t**2 - 1) / denominator
zero("strict logarithm comparison at one", logarithm_defect.subs(t, 1))
zero("strict logarithm comparison derivative", s.diff(logarithm_defect, t) - (t - 1)**4 / (t * denominator**2))
zero("ratio comparison identity", (t + 2) * zeta - (2 * t + 1) * eta - denominator * logarithm_defect)

eta_b = b - 1 - s.log(b)
zeta_b = b * s.log(b) - b + 1
T = b * (beta + b * z) * eta_b - beta * (b + z) * zeta_b
zero("monotonicity coefficient in beta", s.diff(T, beta) - (b * (eta_b - zeta_b) - z * zeta_b))
S = b * (b + (2 * b - 1) * z) * eta_b - (b**2 * (1 + z) + (b - 1) * z**2) * zeta_b
zero("minimum beta substitution", T.subs(beta, b + (b - 1) * z) - S)
residual = b * (b + (2 * b - 1) * z) * (b + 2) - (b**2 * (1 + z) + (b - 1) * z**2) * (2 * b + 1)
zero("strict negative polynomial factor", residual + (b - 1) * (b**2 + 2 * b * z * (z - 1) + z**2))

print(f"PASS all {checks} exact identities.")
