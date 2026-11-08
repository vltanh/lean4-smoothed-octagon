"""Outer face terminal one-variable signs (F₁ ≥ 1/8000 and F₀ > 0 on the reduction curves)."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import F
from uni import emit_uni

x, a, b, u = sp.symbols('x al be u')
c = sp.Rational(7, 96)
S = 1 + x; K = 6 * a ** 2 + 1; L = K / (7 * a ** 2)
D = a ** 2 + 2 * a * b + 1 + 2 * x - 2 * b * x; d = D / (7 * a ** 2)
v = 1 - S / K + (S / K) ** 2; E = S * (u - 1) + 1 / S + (2 * S - 1) / K
w = L ** 2 * v + d ** 2 * u - d * L * E; EL = 2 * d * u - L * E
G = (4 * u * v - E ** 2) * K ** 2 / (576 * a ** 4)
T = 7 * a / (a + b); y = 2 * (a + b) / (7 * a)
zz = (y - 1) / (y + 1); ell = 2 * zz + sp.Rational(2, 3) * zz ** 3
R2 = 2 * w - sp.Rational(1, 2) + (u - 1) * (a + b) / a + a / (a + b) - sp.Rational(1, 7) - EL + ell
F0 = G - c * R2 - sp.Rational(9193, 50000)
F1 = F0 - c * (T - 2) * (w - sp.Rational(3, 4))
UF = sp.Rational(3, 4) + (x - 1) ** 2 / (28 * (x + 1) ** 2)
VB = sp.Rational(3, 4) + 2 * (x - 1) ** 2 / ((x + 1) * (35 * x + 13))
UL = sp.Rational(3, 4) + (x - 1) ** 2 * (b + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (b - 1))
M0 = sp.Rational(1, 8000)
R = sp.Rational
Lc = R(8, 17) + R(32, 221) * (x - 1)
aT3 = (6 * x + 3) / sp.Integer(13)
aL = (4375 * x + 2797) / sp.Integer(10000)
# name: (F, margin, a(x), b(x) [in x,a], u kind, V0, V1, lean a, lean b, doc)
TERM = {
    'T1uf': (F1, R(1, 2500), x, x + Lc * (x - 1), 'uf', Fr(1), Fr(2), "x", "x + (8 / 17 + 32 / 221 * (x - 1)) * (x - 1)", "diagonal `α = x`, lower chord slope"),
    'T1vb': (F1, R(1, 2500), x, x + Lc * (x - 1), 'vb', Fr(1), Fr(2), "x", "x + (8 / 17 + 32 / 221 * (x - 1)) * (x - 1)", "diagonal `α = x`, lower chord slope"),
    'T2uf': (F1, M0, sp.Integer(1), x, 'uf', Fr(6, 5), Fr(5, 3), "1", "x", "lower shape `α = 1`"),
    'T2vb': (F1, M0, sp.Integer(1), x, 'vb', Fr(6, 5), Fr(5, 3), "1", "x", "lower shape `α = 1`"),
    'T3uf': (F1, M0, aT3, x + R(10, 13) * (aT3 - 1), 'uf', Fr(5, 3), Fr(2), "(6 * x + 3) / 13", "x + 10 / 13 * (a - 1)", "lower shape `α = (6x + 3)/13`, `β = x + (10/13)(α - 1)`"),
    'T3vb': (F1, M0, aT3, x + R(10, 13) * (aT3 - 1), 'vb', Fr(5, 3), Fr(2), "(6 * x + 3) / 13", "x + 10 / 13 * (a - 1)", "lower shape `α = (6x + 3)/13`, `β = x + (10/13)(α - 1)`"),
    'T4uf': (F0, 0, sp.Integer(1), x, 'uf', Fr(3, 2), Fr(7203, 4375), "1", "x", "`α = 1`, `β = x`"),
    'T4ul': (F0, 0, sp.Integer(1), x, 'ul', Fr(3, 2), Fr(7203, 4375), "1", "x", "`α = 1`, `β = x`"),
    'T5uf': (F0, 0, aL, x + R(10, 13) * (aL - 1), 'uf', Fr(7203, 4375), Fr(2), "(4375 * x + 2797) / 10000", "x + 10 / 13 * (a - 1)", "`α = a_L(x)`, `β = x + (10/13)(α - 1)`"),
    'T5ul': (F0, 0, aL, x + R(10, 13) * (aL - 1), 'ul', Fr(7203, 4375), Fr(2), "(4375 * x + 2797) / 10000", "x + 10 / 13 * (a - 1)", "`α = a_L(x)`, `β = x + (10/13)(α - 1)`"),
}
UK = {'uf': (UF, "hsUf x", "hsUf"), 'vb': (VB, "hsVbar x", "hsVbar"), 'ul': (UL, "hsUl x b", "hsUl")}


def lf(e):
    s_ = sp.sstr(e)
    s_ = re.sub(r"(?<![A-Za-z0-9_])al(?![A-Za-z0-9_])", "a", s_)
    s_ = re.sub(r"(?<![A-Za-z0-9_])be(?![A-Za-z0-9_])", "b", s_)
    return re.sub(r"\*\*(\d+)", r" ^ (\1 : ℕ)", s_)


def bern_ok(num, V0, V1):
    w = sp.symbols('w')
    P = sp.Poly(sp.expand(num.subs(x, sp.Rational(V0.numerator, V0.denominator) + w)), w)
    H = {m[0]: F(cf) for m, cf in P.terms()}
    n = max(H); W = V1 - V0
    bs = [sum(Fr(comb(k, i), comb(n, i)) * H.get(i, Fr(0)) * W ** i for i in range(k + 1)) for k in range(n + 1)]
    return all(t > 0 for t in bs)


def split(num, V0, V1, depth=0):
    if bern_ok(num, V0, V1):
        return [(V0, V1)]
    assert depth < 8, (V0, V1)
    m = (V0 + V1) / 2
    return split(num, V0, m, depth + 1) + split(num, m, V1, depth + 1)


def gen(nm):
    Fx, mg, ax, bx, uk, V0, V1, la, lb, doc = TERM[nm]
    uexpr, lu, udef = UK[uk]
    e = (Fx - mg).subs(u, uexpr).subs(b, bx).subs(a, ax)
    num, den = sp.fraction(sp.cancel(sp.together(e)))
    fl = sp.factor_list(den)
    mid = sp.Rational((V0 + V1).numerator, 2 * (V0 + V1).denominator)
    sgn = 1 if fl[0] > 0 else -1
    facs = [(f"({abs(fl[0])} : ℝ)", "by norm_num")]
    for f_, k_ in fl[1]:
        s_ = 1 if f_.subs(x, mid) > 0 else -1
        if s_ < 0:
            f_ = -f_
            sgn *= (-1) ** k_
        fs = lf(f_)
        if k_ > 1:
            facs.append((f"({fs}) ^ ({k_} : ℕ)", f"pow_pos (by nlinarith only [hx0, hx1]) {k_}"))
        else:
            facs.append((f"({fs})", "by nlinarith only [hx0, hx1]"))
    num = sgn * num
    pieces = split(num, V0, V1)
    mgl = f" - {mg.p} / {mg.q}" if mg != 0 else ""
    expr = f"hh1o{'F1' if Fx is F1 else 'F0'} x a b u{mgl}"
    out = []
    names = []
    for k, (p0, p1) in enumerate(pieces):
        hyps = ["{x a b u : ℝ}", f"(hx0 : {p0.numerator} / {p0.denominator} ≤ x)", f"(hx1 : x ≤ {p1.numerator} / {p1.denominator})",
                f"(ha : a = {la})", f"(hb : b = {lb})", f"(hu : u = {lu})"]
        pre = [
            "  have hx : 0 < x := by linarith",
            "  have ha1 : 1 ≤ a := by rw [ha]; try linarith",
            "  have hb1 : x ≤ b := by rw [hb]; try nlinarith",
            "  have hab : 0 < a + b := by linarith",
            "  have hS : 1 + x ≠ 0 := by linarith",
            "  have hS' : x + 1 ≠ 0 := by linarith",
            "  have h35 : 35 * x + 13 ≠ 0 := by linarith",
            "  have hK : 6 * a ^ 2 + 1 ≠ 0 := by positivity",
            "  have ha00 : a ≠ 0 := by linarith",
            "  have hab0 : a + b ≠ 0 := hab.ne'",
            "  have hy1 : 2 * (a + b) / (7 * a) + 1 ≠ 0 := by positivity",
        ]
        if uk == 'ul':
            pre.append("  have hbm : b - 1 ≠ 0 := by linarith")
        pre += [
            f"  have key : ({expr}) * ({' * '.join('(' + f_ + ')' for f_, _ in facs)}) = {lf(sp.expand(num))} := by",
            "    rw [hu]",
            f"    simp only [hh1oF1, hh1oF0, hh1oR2, hh1oT, hh1ow, hh1oEL, hh1oG, hh1oL, hh1od, hh1ov, hh1oE, hh1oK, hsDg, hh1oy, hh1ell, {udef}]",
            "    field_simp",
            "    subst hb",
            "    subst ha",
            "    ring",
        ]
        tn = f"hh1o_uni_{nm}" + (f"_{k}" if len(pieces) > 1 else "")
        names.append((tn, p0, p1))
        out.append(emit_uni(tn, x, num, facs, p0, p1, 'lo', f"0 < {expr}", hyps, pre,
                            f"Outer terminal `{nm}` ({doc}) on `[{p0}, {p1}]` (generated)."))
    if len(pieces) > 1:
        # wrapper by case split
        L = [f"/-- Outer terminal `{nm}` ({doc}) on `[{V0}, {V1}]`. -/",
             f"theorem hh1o_uni_{nm} {{x a b u : ℝ}} (hx0 : {V0.numerator} / {V0.denominator} ≤ x) (hx1 : x ≤ {V1.numerator} / {V1.denominator}) (ha : a = {la}) (hb : b = {lb}) (hu : u = {lu}) :",
             f"    0 < {expr} := by"]
        for k, (tn, p0, p1) in enumerate(names[:-1]):
            L.append(f"  rcases le_total x ({p1.numerator} / {p1.denominator}) with h{k} | h{k}")
            L.append(f"  · exact {tn} (by linarith) h{k} ha hb hu")
        tn, p0, p1 = names[-1]
        L.append(f"  exact {tn} (by linarith) (by linarith) ha hb hu")
        out.append("\n".join(L))
    print(nm, 'deg', sp.Poly(num, x).degree(), 'pieces', len(pieces), file=sys.stderr)
    return out


HDR = """module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODefs

/-!
# Gate S1, outer face: terminal one-variable signs ({names})

On the reduction curves of the outer tests: `F₁ ≥ 1/8000` on the diagonal `α = x` and the lower
shapes, and `F₀ > 0` on the `B` corner (`u = u_f(x)`, `u = V̄(x)` or `u = u_ℓ(x, β)`). Each is a
cleared univariate numerator with positive Bernstein coefficients (on the listed subintervals).
Generated by `scripts/certificates/short-hand/gen_ouni.py`.
-/

@[expose] public section

namespace SmoothedOctagon

"""

if __name__ == '__main__':
    out = []
    for nm in sys.argv[2:]:
        out += gen(nm)
    open(sys.argv[1], 'w').write(HDR.replace('{names}', ', '.join(sys.argv[2:])) + "\n\n".join(out) + "\n\nend SmoothedOctagon\n")
