#!/usr/bin/env python3
"""Exact fixed identities for MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md.

Run with Python 3.12 and SymPy 1.14.  No optimization, sampling, period
enumeration, Lean, Lake, typechecking, or CI.  The note proves the
variable-domain signs and the actual PMP/geometric winding interface.
"""

from fractions import Fraction

import sympy as sp


checks = 0


def equal(name, left, right):
    global checks
    assert sp.simplify(left - right) == 0, name
    checks += 1


def positive(name, value):
    global checks
    assert value > 0, (name, value)
    checks += 1


x = Fraction(3, 13)
equal("logarithm cubic bound", 2 * (x + x**3 / 3), Fraction(1032, 2197))
positive("logarithm separation", Fraction(1032, 2197) - Fraction(15, 32))
positive("positive symmetric B interval", Fraction(27, 32) - Fraction(3, 5))
equal(
    "symmetric Casimir lower value",
    (Fraction(9, 4) - Fraction(3, 8) ** 2)
    / (16 * Fraction(27, 32) ** 2),
    Fraction(5, 27),
)
equal("common Casimir denominator", Fraction(5, 27), Fraction(98000, 529200))
positive("competitive Casimir separation", Fraction(5, 27) - Fraction(97969, 529200))
positive("exact cosine comparison", 9 - 8)

m, extra, p = sp.symbols("m extra p", integer=True)
n = (extra + 2 * m - 1) / 3
equal("mixed defect budget", extra / 3 + 2 * m / 3 - n, sp.Rational(1, 3))
equal("forward count", (p + m - 1).subs(p, extra + m), extra + 2 * m - 1)
equal("density rearrangement", 12 * (sp.Rational(1, 3) - m / 12 + extra / 6), 4 - m + 2 * extra)

print(f"PASS: {checks} exact checks; the uniform signs and period scope are the hand proof.")
