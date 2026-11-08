"""The outer face for large α (hs2_outer_sign_large): Heavy/S2LargeCertA, S2LargeCertB, S2Large."""
import re
import sympy as sp
from fractions import Fraction as Fr
from bern import from_sympy
from leangen import Lib, emit_nested
from common import write, MOD, OUT
import os

x, a, c = sp.symbols('x a c')
LBAR = sp.Rational(-296, 1029)

def polys():
    S = 1 + x; M = 6 * a**2 + 1
    b = x + c * (a - 1); B = a + b
    D = a**2 + 2 * a * b + 1 + 2 * x - 2 * b * x
    u = sp.Rational(3, 4) + 2 * (x - 1)**2 / (S * (35 * x + 13))
    N = M * (S * (u - 1) + 1 / S) + 2 * S - 1
    w = (M**2 - M * S + S**2 + D**2 * u - D * N) / (49 * a**4)
    EL = (2 * D * u - N) / (7 * a**2)
    h = w - sp.Rational(3, 4)
    r = B / a
    t = sp.Rational(4, 3) * (2 * r / 7) - 1
    base = sp.Rational(6, 7) + (u - 1) * r + 1 / r - EL + LBAR + t - t**2 / 2 + t**3 / 3
    out = {}
    for nm, F in [('H0', base + (4 - r / 2) * h), ('H1', base + (7 / r + sp.Rational(1, 4)) * h)]:
        num, den = sp.fraction(sp.together(F))
        out[nm] = (sp.expand(num), sp.factor(den))
    return out

def main():
    res = polys()
    box = [((Fr(5, 8), Fr(7, 8)), (Fr(3, 2), Fr(12, 5)), (Fr(13, 6), Fr(12, 5)))]
    for nm, X, f, what in [('H0', 'hh2LgA', 'S2LargeCertA.lean', 'H₀ = G₂'),
                           ('H1', 'hh2LgB', 'S2LargeCertB.lean', 'H₁ = G₂ + (T - 2)A')]:
        num, den = res[nm]
        print(nm, 'denominator', den)
        P = from_sympy(-num, (c, a, x))
        doc = (f"The large outer face (`OUTER_RATIO_HAND_SIGN` §6, `α ≥ 3/2`, `u = V̄(x)`): minus the "
               f"cleared numerator of `{what}` with the log majorant `hh2_log_le_bound`, in `(c, α, x)`, "
               f"`β = x + c(α - 1)`. Nested Bernstein certificate on `[5/8, 7/8] × [3/2, 12/5] × [13/6, 12/5]`.")
        lib = Lib(X)
        code, nl, names = emit_nested(lib, X, P, ('c', 'a', 'x'), box, doc=doc)
        write(f, [MOD + 'S2Bern'], f'generated certificate `{X}`', doc,
              f"* `{X}`: the polynomial in nested form; `{X}_pos`: its positivity.", lib.render() + "\n" + code,
              'gen_large.py')
        print('  leaves', nl)

if __name__ == '__main__':
    main()
