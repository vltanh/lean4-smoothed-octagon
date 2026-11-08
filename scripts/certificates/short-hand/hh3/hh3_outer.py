"""Generator for `hs3_outer_face` (DISPLACEMENT_OUTER_FACE): writes
`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S3Outer{A,B0,B1}.lean`.

Route (lighter than the note's single 1173-term numerator N_i(h, v, t)):
* clear the rational test at the atom level: -D_i * Fbar_i = M_i(x, a, beta) = sum_k m_ik(x, a) beta^k
  (205 / 166 terms);
* write beta = U - W y with U = x(189 + 115a)/304, W = 39x(a - 1)/304, y in [0, 1]
  (y = 0 at g = 115/304, y = 1 at g = 1/4) and apply Bernstein of degree 6 - i in y with abstract
  coefficients c_il(x, a);
* each Bernstein coefficient b_ij(x, a) (92 / 76 terms) is expanded in (h, v)
  (x = 2 + h, a = a0(x) + (x - a0(x)) v) and certified on [0, 1/6] x [0, 1] by an explicit
  nonnegative combination (Bernstein in v for every power of h).
"""
import sympy as sp, pickle, sys, os
from fractions import Fraction as Fr
from math import comb
from hh3_common import *

x, a, be, h, v, y = sp.symbols('x a be h v y')
R = sp.Rational
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..'))
OUT = os.path.join(ROOT, 'SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy')


def Mpoly(i):
    """-D_i * Fbar_i as a polynomial in (x, a, be), with u = hsUO x be."""
    u = R(3, 4) + (x - 1)**2 * (x + be - 2) / ((be - 1) * (x + 1) * (35 * x + 13))
    S = 1 + x
    r = a / (a + be); k = 5 * a - 1; E0 = S * (u - 1) + 1 / S; e = 1 - 1 / a**2; n = S / a**2
    Dl = (a**2 + 2 * a * be + 1 + 2 * x - 2 * be * x) / a**2
    A1 = 2 * e + n + Dl * E0
    A2 = e**2 + e * n + n**2 + Dl**2 * u + Dl * e * E0 - Dl * (2 * S - 1) / a**2
    A3 = 2 * Dl * u + e * E0 - (2 * S - 1) / a**2
    w = 1 - A1 / 7 + A2 / 49; EL = -E0 + A3 / 7
    yy = 2 * R(1, 7) / r
    ell = R(-40153, 180000) + 2 * (5 * yy - 4) / (5 * yy + 4)
    J = (u - 1) / r + r + 1 - R(1, 7) - EL + ell
    if i == 0:
        nn = 2 + 4 * (4 - 3 * yy) / k
    else:
        nn = r / R(1, 7) + 4 / k
    Dc = Dclear(i)
    M = sp.cancel(sp.together(-Dc * (J + nn * (w - R(3, 4)))))
    num, den = sp.fraction(M)
    assert den == 1
    return sp.expand(num)


def Dclear(i):
    base = (a + be) * (5 * a - 1) * (19 * a + 5 * be) * (be - 1) * (1 + x) * (35 * x + 13)
    return 61740000 * a**5 * base if i == 0 else 8820000 * a**4 * base


DSTR = {0: "61740000 * a ^ 5 * (a + be) * (5 * a - 1) * (19 * a + 5 * be) * (be - 1) * (1 + x) * (35 * x + 13)",
        1: "8820000 * a ^ 4 * (a + be) * (5 * a - 1) * (19 * a + 5 * be) * (be - 1) * (1 + x) * (35 * x + 13)"}
NSTR = {0: "2 + 4 * (4 - 3 * (2 * (1 / 7) / hsRA a be)) / (5 * a - 1)",
        1: "hsRA a be / (1 / 7) + 4 / (5 * a - 1)"}
LSTR = "-40153 / 180000 + 2 * (5 * (2 * (1 / 7) / hsRA a be) - 4) / (5 * (2 * (1 / 7) / hsRA a be) + 4)"
USTR = "x * (189 + 115 * a) / 304"
WSTR = "39 * x * (a - 1) / 304"
ASUB = "((100 * (2 + h) + 77 + (140 * (2 + h) - 77) * v) / 240)"


def compute():
    U = x * (189 + 115 * a) / 304; W = 39 * x * (a - 1) / 304
    asub = (100 * (2 + h) + 77 + (140 * (2 + h) - 77) * v) / 240
    data = {}
    for i in (0, 1):
        M = Mpoly(i)
        PM = sp.Poly(M, be)
        deg = PM.degree()
        assert deg == 6 - i
        mk = [sp.expand(PM.coeff_monomial(be**k)) for k in range(deg + 1)]
        c = [sp.expand((-W)**l * sum(comb(k, l) * mk[k] * U**(k - l) for k in range(l, deg + 1)))
             for l in range(deg + 1)]
        assert sp.expand(M.subs(be, U - W * y) - sum(c[l] * y**l for l in range(deg + 1))) == 0
        b = [sp.expand(sum(comb(deg - l, j - l) * c[l] for l in range(j + 1))) for j in range(deg + 1)]
        Bhv = [to_dict(sp.expand(b[j].subs({x: 2 + h, a: asub}, simultaneous=True)), (h, v))
               for j in range(deg + 1)]
        certs = []
        for j in range(deg + 1):
            ct = cert_a(Bhv[j], Fr(1, 6)) or cert_bv(Bhv[j], Fr(1, 6), 1)
            assert ct is not None, (i, j)
            certs.append(ct)
            print(i, j, ct['kind'], file=sys.stderr)
        data[i] = dict(deg=deg, mk=[to_dict(m, (x, a)) for m in mk], c=[to_dict(cl, (x, a)) for cl in c],
                       b=[to_dict(bj, (x, a)) for bj in b], Bhv=Bhv, certs=certs)
    return data


HEADER = """module

public import {imp}

/-!
{doc}
-/

@[expose] public section

namespace SmoothedOctagon

open Real
"""


def emit_A(data, i):
    L = []
    D = data[i]; deg = D['deg']
    for k in range(deg + 1):
        L.append(f"/-- Coefficient of `β^{k}` in `M_{i} = -𝒟_{i} F̄_{i}`. -/\n"
                 f"noncomputable def hh3O{i}m{k} (x a : ℝ) : ℝ :=\n  {poly_expanded(D['mk'][k], ['x', 'a'])}\n")
    msum = " + ".join(f"hh3O{i}m{k} x a" + ("" if k == 0 else f" * be" + ("" if k == 1 else f" ^ ({k} : ℕ)"))
                      for k in range(deg + 1))
    L.append(f"""set_option maxRecDepth 20000 in
/-- **Clearing the outer test `F̄_{i}`** (`DISPLACEMENT_OUTER_FACE` (4)-(8)): with the rational
log majorant and `u = ū`, `F̄_{i} · 𝒟_{i} = -∑ m_{i}k β^k`. -/
theorem hh3_o{i}_clear (x a be : ℝ) (hx : 1 < x) (ha : 1 < a) (hb : 1 < be) :
    hs3Fn x be a (hsUO x be) (1 / 7) ({NSTR[i]})
        ({LSTR}) *
      ({DSTR[i]}) =
      -({msum}) := by
  have h1 : a ≠ 0 := by positivity
  have h2 : a + be ≠ 0 := by positivity
  have h3 : 5 * a - 1 ≠ 0 := by linarith
  have h3x : a * 5 - 1 ≠ 0 := by linarith
  have h4 : 19 * a + 5 * be ≠ 0 := by positivity
  have h4x : a * 19 + be * 5 ≠ 0 := by positivity
  have h5 : be - 1 ≠ 0 := by linarith
  have h6 : 1 + x ≠ 0 := by positivity
  have h6' : x + 1 ≠ 0 := by positivity
  have h7 : 35 * x + 13 ≠ 0 := by positivity
  have h7x : x * 35 + 13 ≠ 0 := by positivity
  have e1 : 2 * (1 / 7 : ℝ) / hsRA a be = 2 * (a + be) / (7 * a) := by
    unfold hsRA; field_simp
  have e2 : (-40153 / 180000 : ℝ) + 2 * (5 * (2 * (a + be) / (7 * a)) - 4) / (5 * (2 * (a + be) / (7 * a)) + 4)
      = 319847 / 180000 - 56 * a / (19 * a + 5 * be) := by
    field_simp; ring
  rw [e1, e2]
  unfold hs3Fn hsELs hsWs hsA1 hsA2 hsA3 hsE0 hsDg hsUO hsRA {' '.join(f'hh3O{i}m{k}' for k in range(deg + 1))}
  field_simp
  ring
""")
    # abstract shift: c_l as formulas in the atoms m_k
    for l in range(deg + 1):
        L.append(f"/-- Coefficient of `y^{l}` after `β = U - W y`, expanded. -/\n"
                 f"noncomputable def hh3O{i}c{l} (x a : ℝ) : ℝ :=\n  {poly_expanded(D['c'][l], ['x', 'a'])}\n")
    for l in range(deg + 1):
        inner = " + ".join(f"{comb(k, l)} * hh3O{i}m{k} x a * ({USTR}) ^ ({k - l} : ℕ)" for k in range(l, deg + 1))
        L.append(f"""set_option maxRecDepth 20000 in
theorem hh3_o{i}_c{l}_eq (x a : ℝ) :
    (-({WSTR})) ^ ({l} : ℕ) * ({inner}) = hh3O{i}c{l} x a := by
  unfold {' '.join(f'hh3O{i}m{k}' for k in range(l, deg + 1))} hh3O{i}c{l}
  ring
""")
    # shift lemma with abstract m_k
    ms = [f"m{k}" for k in range(deg + 1)]
    lhs = " + ".join(f"m{k}" + ("" if k == 0 else f" * (U - W * y)" + ("" if k == 1 else f" ^ ({k} : ℕ)"))
                     for k in range(deg + 1))
    cforms = []
    for l in range(deg + 1):
        inner = " + ".join(f"{comb(k, l)} * m{k} * U ^ ({k - l} : ℕ)" for k in range(l, deg + 1))
        cforms.append(f"(-W) ^ ({l} : ℕ) * ({inner})")
    rhs = " + ".join(f"({cforms[l]})" + ("" if l == 0 else " * y" + ("" if l == 1 else f" ^ {l}"))
                     for l in range(deg + 1))
    L.append(f"""theorem hh3_o{i}_shift_gen ({' '.join(ms)} U W y : ℝ) :
    {lhs} =
      {rhs} := by
  ring
""")
    lhs2 = " + ".join(f"hh3O{i}m{k} x a" + ("" if k == 0 else f" * ({USTR} - {WSTR} * y)" + ("" if k == 1 else f" ^ ({k} : ℕ)"))
                      for k in range(deg + 1))
    rhs2 = " + ".join(f"hh3O{i}c{l} x a" + ("" if l == 0 else " * y" + ("" if l == 1 else f" ^ {l}"))
                      for l in range(deg + 1))
    L.append(f"""/-- The shift `β = U - W y`. -/
theorem hh3_o{i}_shift (x a y : ℝ) :
    {lhs2} =
      {rhs2} := by
  rw [hh3_o{i}_shift_gen, {', '.join(f'hh3_o{i}_c{l}_eq' for l in range(deg + 1))}]
""")
    for j in range(deg + 1):
        L.append(f"/-- Bernstein coefficient `b_{j}` of `∑ c_{i}l y^l` on `[0, 1]`. -/\n"
                 f"noncomputable def hh3O{i}b{j} (x a : ℝ) : ℝ :=\n  {horner_by(D['b'][j], ['x', 'a'], ['a', 'x'])}\n")
        comb_s = bern_comb_str(i, deg, j)
        L.append(f"""set_option maxRecDepth 20000 in
theorem hh3_o{i}_b{j}_eq (x a : ℝ) : {comb_s} = hh3O{i}b{j} x a := by
  unfold {' '.join(f'hh3O{i}c{l}' for l in range(j + 1))} hh3O{i}b{j}
  ring
""")
    doc = f"""# Heavy leaf `hs3_outer_face`: the cleared outer test `F̄_{i}` and its Bernstein coefficients

`hh3_o{i}_clear` clears the rational outer test (`DISPLACEMENT_OUTER_FACE` (4)-(8), log replaced by
`L*`, `u = ū`) to `-∑ m_{{k}}(x, α) βᵏ`; `hh3_o{i}_shift` writes it as `∑ c_l(x, α) yˡ`
(`β = U - W y`, `U = x(189 + 115α)/304`, `W = 39x(α - 1)/304`, `y ∈ [0, 1]` ⟺ `g ∈ [1/4, 115/304]`);
`hh3_o{i}_b{{j}}_eq` identifies the Bernstein coefficients `hh3O{i}b{{j}}`. Generated by
`scripts/certificates/short-hand/hh3/hh3_outer.py`.

## Main API

`hh3O{i}m{{k}}`, `hh3O{i}c{{l}}`, `hh3O{i}b{{j}}`, `hh3_o{i}_clear`, `hh3_o{i}_shift`, `hh3_o{i}_b{{j}}_eq`.
"""
    s = HEADER.format(imp="SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3Base", doc=doc) + "\n" + "\n".join(L) + "\nend SmoothedOctagon\n"
    open(os.path.join(OUT, f'S3OuterA{i}.lean'), 'w').write(s)
    return len(s)


def bern_comb_str(i, deg, j):
    terms = []
    for l in range(j + 1):
        cf = comb(deg - l, j - l)
        terms.append(f"hh3O{i}c{l} x a" if cf == 1 else f"{cf} * hh3O{i}c{l} x a")
    return " + ".join(terms)


def emit_B(data, i, js, part):
    D = data[i]; deg = D['deg']
    L = []
    for j in js:
        Bs = poly_expanded(D['Bhv'][j], ['h', 'v'])
        L.append(f"""set_option maxRecDepth 20000 in
theorem hh3_o{i}_b{j}_hv (h v : ℝ) :
    hh3O{i}b{j} (2 + h) {ASUB} =
      {Bs} := by
  unfold hh3O{i}b{j}
  ring
""")
        cl = lean_cert(D['Bhv'][j], D['certs'][j])
        L.append(f"""set_option maxRecDepth 20000 in
/-- `b_{j} > 0` on the outer domain. -/
theorem hh3_o{i}_b{j}_pos {{x a : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ha : (100 * x + 77) / 240 ≤ a)
    (hax : a ≤ x) : 0 < hh3O{i}b{j} x a := by
  obtain ⟨h, rfl⟩ : ∃ h, x = 2 + h := ⟨x - 2, by ring⟩
  have hk : 0 < 140 * (2 + h) - 77 := by linarith
  obtain ⟨v, rfl⟩ : ∃ v, a = (100 * (2 + h) + 77 + (140 * (2 + h) - 77) * v) / 240 :=
    ⟨(240 * a - 100 * (2 + h) - 77) / (140 * (2 + h) - 77), by
      rw [mul_div_cancel₀ _ hk.ne']; ring⟩
  have h0 : 0 ≤ h := by linarith
  have h1 : h ≤ 1 / 6 := by linarith
  have v0 : 0 ≤ v := by nlinarith
  have v1 : v ≤ 1 := by nlinarith
  rw [hh3_o{i}_b{j}_hv]
""" + "\n".join(cl) + "\n")
    names = ", ".join(f"`hh3_o{i}_b{j}_pos`" for j in js)
    doc = f"""# Heavy leaf `hs3_outer_face`: positivity of Bernstein coefficients of the test `F̄_{i}` (part {part})

{names}: `hh3O{i}b{{j}} x α > 0` for `2 ≤ x ≤ 13/6`, `a₀(x) ≤ α ≤ x`. Each coefficient is expanded in
`x = 2 + h`, `α = a₀(x) + (x - a₀(x)) v` (`hh3_o{i}_b{{j}}_hv`) and written as an explicit nonnegative
combination plus a positive constant (`linear_combination`). Generated by
`scripts/certificates/short-hand/hh3/hh3_outer.py`.

## Main API

{names}.
"""
    s = HEADER.format(imp=f"SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterA{i}", doc=doc) + "\n" + "\n".join(L) + "\nend SmoothedOctagon\n"
    open(os.path.join(OUT, f'S3OuterB{i}{part}.lean'), 'w').write(s)
    return len(s)


PARTS = {0: [(0, 1), (2, 3), (4, 5), (6,)], 1: [(0, 1), (2, 3), (4, 5)]}


if __name__ == '__main__':
    pk = os.path.join(os.environ.get('HH3_CACHE', '/tmp'), 'hh3_outer.pkl')
    if os.path.exists(pk) and '--fresh' not in sys.argv:
        data = pickle.load(open(pk, 'rb'))
    else:
        data = compute()
        pickle.dump(data, open(pk, 'wb'))
    for i in (0, 1):
        print('A', i, emit_A(data, i))
    for i in (0, 1):
        for p, js in enumerate(PARTS[i]):
            print('B', i, p, emit_B(data, i, js, 'abcd'[p]))
