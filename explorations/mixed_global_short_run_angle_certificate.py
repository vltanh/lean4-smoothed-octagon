#!/usr/bin/env python3
"""Exact algebra accompanying MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md.

Domain: actual reverse-centre variables 0<r,t<1/2, 0<rho<r*t,
3/4<u<=1-r+r*r, 3/4<v<=1-t+t*t, and positive angle cosine in
[3/10,1/2).  The script checks identities and fixed rational comparisons;
the note proves all variable-domain signs, continuation of the scalar
comparison path, and the actual PMP/Casimir/geometric-winding interface.

Run: python3 explorations/mixed_global_short_run_angle_certificate.py
Dependencies: Python 3.12 and SymPy 1.14.  No numerical optimization,
sampling, Lean, Lake, typechecking, or CI is used.
"""

from fractions import Fraction

import sympy as sp


r, t, rho, u, v, z = sp.symbols("r t rho u v z", positive=True)
E_symbol = sp.symbols("E", real=True)
U = lambda x: 1 - x + x**2
E = (
    1 + r + t - rho + sp.log(rho / (r * t))
    - (1 - u) / r - (1 - v) / t
)
checks = 0


def identity(name, expression):
    global checks
    result = sp.factor(sp.simplify(sp.expand_log(expression, force=True)))
    assert result == 0, (name, result)
    checks += 1


def positive(name, value):
    global checks
    assert value > 0, (name, value)
    checks += 1


identity("centre rho derivative", sp.diff(E, rho) - (1 - rho) / rho)
identity("centre r derivative", sp.diff(E, r) - (U(r) - u) / r**2)
identity("centre t derivative", sp.diff(E, t) - (U(t) - v) / t**2)
identity("centre u derivative", sp.diff(E, u) - 1 / r)
identity("centre v derivative", sp.diff(E, v) - 1 / t)

B = -1 + 2 * r + 2 * t - rho + sp.log(rho / (r * t))
identity("upper-corner centre", E.subs({u: U(r), v: U(t)}) - B)
identity(
    "angle half bound",
    (B - 3 * rho).subs(rho, r * t * z)
    + (1 - 2 * r) * (1 - 2 * t)
    - 4 * r * t * (1 - z) - sp.log(z),
)

rho_u = rho / (1 - rho) * (E_symbol / (2 * u) - 1 / r)
Q = (1 - rho) ** 2 + rho * E_symbol - 2 * rho * u / r
identity(
    "fixed-angle logarithmic u derivative",
    1 / (2 * u) + rho_u / (1 - rho)
    - Q / (2 * u * (1 - rho) ** 2),
)
rho_r = -rho * (U(r) - u) / (r**2 * (1 - rho))
identity(
    "fixed-angle logarithmic r derivative",
    rho_r / (1 - rho)
    + rho * (U(r) - u) / (r**2 * (1 - rho) ** 2),
)
Q_lower = 1 + rho * (t + sp.log(rho / (r * t)) - 2 / r - 1 / (4 * t))
identity(
    "Q upper-lower substitution",
    Q.subs(E_symbol, E) - Q_lower
    - rho * (U(r) - u) / r - rho * (v - sp.Rational(3, 4)) / t,
)
q_base = 1 - z + z * sp.log(z) / 4
identity(
    "Q positive remainder",
    Q_lower.subs(rho, r * t * z) - q_base
    - z * (1 - 2 * t) * (1 - r * (1 + 2 * t) / 4)
    - z * (r * t - sp.Rational(1, 4)) * sp.log(z),
)
identity("Q base derivative", sp.diff(q_base, z) - (sp.log(z) - 3) / 4)
identity(
    "boundary path derivative",
    (rho_r + rho_u * sp.diff(U(r), r)).subs(u, U(r)) / rho
    - (1 - 2 * r) / (1 - rho) * (1 / r - E_symbol / (2 * U(r))),
)

B_sym = 1 - rho + sp.log(4 * rho)
identity(
    "symmetric centre",
    E.subs({r: sp.Rational(1, 2), t: sp.Rational(1, 2),
            u: sp.Rational(3, 4), v: sp.Rational(3, 4)}) - B_sym,
)
h = 1 - z / 4 + sp.log(z)
k = 4 / z - 1 + sp.log(z)
identity("symmetric product derivative", sp.diff(h * k, z) + (4 - z) ** 2 * sp.log(z) / (4 * z**2))
gamma_sym_sq = (sp.Rational(9, 4) - B_sym**2) / (16 * (1 - rho) ** 2)
identity(
    "symmetric Casimir derivative",
    sp.diff(gamma_sym_sq, rho)
    - (sp.Rational(9, 4) - B_sym * (1 / rho - 1 + sp.log(4 * rho)))
    / (8 * (1 - rho) ** 3),
)

positive("lower logarithm interval", Fraction(83, 100) - Fraction(8, 17))
positive("upper logarithm interval", Fraction(9, 20) - Fraction(943, 2100))
identity(
    "rational symmetric Casimir lower bound",
    (sp.Rational(9, 4) - sp.Rational(9, 20) ** 2)
    / (16 * sp.Rational(83, 100) ** 2) - sp.Rational(20475, 110224),
)
positive("competitive Casimir separation", Fraction(20475, 110224) - Fraction(97969, 529200))
positive("cosine comparison square", Fraction(5) - Fraction(11, 5) ** 2)

print(f"PASS: {checks} exact checks; all variable-domain and period claims remain the hand proof.")
