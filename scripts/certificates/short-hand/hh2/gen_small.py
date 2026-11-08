"""The outer face for small α (hs2_outer_sign_small): Heavy/S2SmallPolyA, S2SmallCertA0, S2SmallCertA1,
S2SmallCertB, S2SmallShift. Run gen_small_link.py afterwards for Heavy/S2Small."""
import sympy as sp
from fractions import Fraction as Fr
from bern import from_sympy
from leangen import Lib, emit_nested, lnum
from shiftgen import emit_defs, emit_shift
from common import write, MOD

x, a, c, s = sp.symbols('x a c s')
LBAR = sp.Rational(-296, 1029)
GEN = 'gen_small.py'

def polys():
    S = 1 + x
    b = x + c * (a - 1); B = a + b; M = 6 * a**2 + 1
    D = a**2 + 2 * a * b + 1 + 2 * x - 2 * b * x
    u = sp.Rational(3, 4) + (sp.Rational(17, 240) * (x - 1)**3 / S**2 + (b - x) / 1200) / (b - 1)
    N = M * (S * (u - 1) + 1 / S) + 2 * S - 1
    w = (M**2 - M * S + S**2 + D**2 * u - D * N) / (49 * a**4)
    EL = (2 * D * u - N) / (7 * a**2)
    h = w - sp.Rational(3, 4)
    r = B / a
    tt = sp.Rational(4, 3) * (2 * r / 7) - 1
    base = sp.Rational(6, 7) + (u - 1) * r + 1 / r - EL + LBAR + tt - tt**2 / 2 + tt**3 / 3
    out = {}
    for nm, F in [('H0', base + (4 - r / 2) * h), ('H1', base + (7 / r + sp.Rational(1, 4)) * h)]:
        num, den = sp.fraction(sp.together(F))
        out[nm] = (sp.expand(num), sp.factor(den))
    return out

af = lambda X: (36 * X + 25) / 84
cp = lambda X: (24 * X + 51) / 128

def boxes(n):
    pts = [Fr(13, 6) + (Fr(12, 5) - Fr(13, 6)) * Fr(i, n) for i in range(n + 1)]
    return pts, [((Fr(5, 8), cp(pts[i + 1])), (Fr(0), Fr(3, 2) - af(pts[i])), (pts[i], pts[i + 1])) for i in range(n)]

def main():
    res = polys()
    shift_body = []
    for nm, X, npc, what in [('H0', 'hh2SmA', 2, 'H₀ = G₂'), ('H1', 'hh2SmB', 1, 'H₁ = G₂ + (T - 2)A')]:
        num, den = res[nm]
        print(nm, 'denominator', den)
        Q = sp.expand(-num)
        Pd = from_sympy(sp.expand(Q.subs(a, (36 * x + 25) / sp.Integer(84) + s)), (c, s, x))
        Qd = from_sympy(Q, (c, a, x))
        doc = (f"The small outer face (`OUTER_RATIO_HAND_SIGN` §§4-5, `α ≤ 3/2`, `u = u_s`): minus the cleared "
               f"numerator of `{what}` with the log majorant `hh2_log_le_bound`, in the shifted coordinates "
               f"`(c, s, x)`, `α = (36x + 25)/84 + s`, `β = x + c(α - 1)`.")
        pts, bx = boxes(npc)
        if npc == 1:
            lib = Lib(X)
            code, nl, names = emit_nested(lib, X, Pd, ('c', 's', 'x'), bx, doc=doc)
            write(f"S2SmallCert{X[-1]}.lean", [MOD + 'S2Bern'], f"generated certificate `{X}`", doc,
                  f"* `{X}`: the polynomial in nested form; `{X}_pos`: its positivity on the box.",
                  lib.render() + "\n" + code, GEN)
            print('  leaves', nl)
        else:
            write(f"S2SmallPoly{X[-1]}.lean", [MOD + 'S2Bern'], f"polynomial `{X}`", doc,
                  f"* `{X}`: the polynomial in nested form.", emit_defs(X, Pd, ('c', 's', 'x'), doc), GEN)
            for b in range(npc):
                lib = Lib(f"{X}{b}")
                code, nl, names = emit_nested(lib, X, Pd, ('c', 's', 'x'), [bx[b]], doc=doc, defs=False)
                code = code.replace(f"theorem {X}_pos (", f"theorem {X}_pos{b} (").replace(
                    f"{X}_b0_", f"{X}_b{b}_").replace(f"{X}_e0_", f"{X}_e{b}_")
                write(f"S2SmallCert{X[-1]}{b}.lean", [MOD + f'S2SmallPoly{X[-1]}'],
                      f"generated certificate `{X}`, box {b}", doc + f" Box {b}: `x ∈ [{pts[b]}, {pts[b + 1]}]`.",
                      f"* `{X}_pos{b}`: positivity on the box.", lib.render() + "\n" + code, GEN)
                print('  leaves', nl)
        XQ = X.replace('hh2Sm', 'hh2SmQ')
        shift_body.append(emit_defs(XQ, Qd, ('c', 'a', 'x'), f"The unshifted polynomial `{XQ}` (`α` in place of `s`)"))
        shift_body.append(emit_shift(XQ, Qd, X, Pd, ('c', 'a', 'x'), "(36 * x + 25) / 84"))
        lines = []
        if npc == 1:
            lines.append(f"  exact {X}_pos c (a - (36 * x + 25) / 84) x hc1 (by linarith) (by linarith) (by linarith) hx hx2")
        else:
            cur = "hx"
            for b in range(npc):
                call = f"{X}_pos{b} c (a - (36 * x + 25) / 84) x hc1 (by linarith) (by linarith) (by linarith)"
                if b == npc - 1:
                    lines.append(f"  exact {call} {cur} hx2")
                else:
                    lines.append(f"  rcases le_total x {lnum(pts[b + 1])} with h{b} | h{b}")
                    lines.append(f"  · exact {call} {cur} h{b}")
                    cur = f"h{b}"
        shift_body.append(f"""/-- **Positivity of `{XQ}`** for `13/6 ≤ x ≤ 12/5`, `(36x + 25)/84 ≤ α ≤ 3/2`,
`5/8 ≤ c ≤ (24x + 51)/128`. -/
theorem {XQ}_pos (c a x : ℝ) (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : (36 * x + 25) / 84 ≤ a)
    (ha2 : a ≤ 3 / 2) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ (24 * x + 51) / 128) : 0 < {XQ} c a x := by
  rw [{XQ}_shift]
""" + "\n".join(lines) + "\n")
    write('S2SmallShift.lean', [MOD + 'S2SmallCertA0', MOD + 'S2SmallCertA1', MOD + 'S2SmallCertB'],
          'the small outer face polynomials in `(c, α, x)`',
          "The cleared numerators `hh2SmQA` (of `H₀`) and `hh2SmQB` (of `H₁`) of the small outer face "
          "(`OUTER_RATIO_HAND_SIGN` §§4-5) in the unshifted coordinates `(c, α, x)`, their shifts "
          "`α = (36x + 25)/84 + s` to the certificate polynomials `hh2SmA`, `hh2SmB` (one bivariate identity "
          "per power of `c`), and their positivity on `13/6 ≤ x ≤ 12/5`, `(36x + 25)/84 ≤ α ≤ 3/2`, "
          "`5/8 ≤ c ≤ (24x + 51)/128`.",
          "* `hh2SmQA`, `hh2SmQB`, `hh2SmQA_shift`, `hh2SmQB_shift`, `hh2SmQA_pos`, `hh2SmQB_pos`.",
          "\n".join(shift_body), GEN)

if __name__ == '__main__':
    main()
