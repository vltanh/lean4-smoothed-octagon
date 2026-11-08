"""Outer face derivative / envelope sign claims (ClaimG and Claim3)."""
import sys, os, re, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sympy as sp
from fractions import Fraction as Fr
from claimg import ClaimG
from claim3 import Claim3
from emitg import emit_claimg
from emit3 import emit_claim3
import oexprs as O

x, a, b, u, C = O.x, O.a, O.b, O.u, O.C
c = O.c
tS = sp.symbols('t')
R = sp.Rational
Cm = lambda s: Fr(8) * s / (9 * s + 8)
Cp = lambda s: s * (7 * s + 1) / (4 * s * s + 11 * s + 1)
Vb = lambda s: Fr(3, 4) + 2 * (s - 1) ** 2 / ((s + 1) * (35 * s + 13))
bC = x + C * (a - 1)
UNF = ["hh1oGa", "hh1oGu", "hh1oR1a", "hh1oR1b", "hh1oR1u", "hh1oR2a", "hh1oR2b", "hh1oR2u", "hh1oTa", "hh1oTb",
       "hh1oT", "hh1owa", "hh1owb", "hh1owu", "hh1oELa", "hh1oLa", "hh1oda", "hh1odb", "hh1ova", "hh1oEa",
       "hh1ow", "hh1oEL", "hh1oL", "hh1od", "hh1ov", "hh1oE", "hh1oK", "hsDg"]
DEFS = {}
HEAVY = os.environ.get("HEAVY", os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..', 'SmoothedOctagon', 'Exclusion', 'Mixed', 'ShortHand', 'Heavy'))
for f in ["S1ODefs.lean", "S1ODeriv.lean"]:
    txt = open(os.path.join(HEAVY, f)).read()
    for m in re.finditer(r"noncomputable def (hh1\w+)[^:]*:[^=]*:=(.*?)(?=\n\n|\nnoncomputable|\n/--|\nend |\ntheorem)", txt, re.S):
        DEFS[m.group(1)] = m.group(2)
DEFS['hsDg'] = ''


def needed(le):
    seen = []
    todo = re.findall(r"hh1\w+|hsDg", le)
    while todo:
        n = todo.pop()
        if n in seen or n not in DEFS:
            continue
        seen.append(n)
        todo += re.findall(r"hh1\w+|hsDg", DEFS[n])
    return [n for n in UNF if n in seen]


POSG = ["have hS : 1 + x ≠ 0 := by linarith only [hx0]", "have hS' : x + 1 ≠ 0 := by linarith only [hx0]"]
# ClaimG specs: name -> (sympy expr, X0, Zmax, tvars, lean expr, vnames, doc)
GSPEC = {
    'sa': ((-(O.Ga - c * (O.R1a + C * O.R1b))).subs(b, bC), Fr(1), Fr(1, 5),
           [(a, Fr(1), (Fr(0), Fr(1))), (C, Fr(8, 17), (Cp(Fr(6, 5)) - Fr(8, 17), Fr(0))), (u, Fr(3, 4), (Vb(Fr(6, 5)) - Fr(3, 4), Fr(0)))],
           "-(hh1oGa x a u - 7 / 96 * (hh1oR1a x a (x + C * (a - 1)) u + C * hh1oR1b x a (x + C * (a - 1)) u))",
           ['a', 'C', 'u'], "`(∂_α + C∂_β)F₁ ≤ 0` (log form, without the `ε` term) on `1 ≤ α ≤ x ≤ 6/5`."),
    'dg': ((-O.R1b).subs(a, x).subs(b, x + tS), Fr(1), Fr(1),
           [(tS, Fr(0), (Fr(0), Fr(10, 13))), (u, Fr(3, 4), (Vb(Fr(2)) - Fr(3, 4), Fr(0)))],
           "-hh1oR1b x x (x + t) u", ['t', 'u'], "`∂_βR̄₁ ≤ 0` on the diagonal `α = x` (log form)."),
    'lo': ((O.R1b - R(1, 100)).subs(b, x + tS).subs(a, (6 * x + 3) / 13), Fr(5, 3), Fr(1, 3),
           [(tS, Fr(0), (Fr(0), Fr(60, 169))), (u, Fr(3, 4), (Vb(Fr(2)) - Fr(3, 4), Fr(0)))],
           "hh1oR1b x ((6 * x + 3) / 13) (x + t) u - 1 / 100", ['t', 'u'],
           "`∂_βR̄₁ ≥ 1/100` on the lower shape `α = (6x + 3)/13` (log form)."),
    'wS': ((O.w - R(3, 4) + R(1, 1000)).subs(b, bC), Fr(1), Fr(1, 2),
           [(a, Fr(1), (Fr(0), Fr(1))), (C, Fr(8, 17), (Cp(Fr(3, 2)) - Fr(8, 17), Fr(0))), (u, Fr(3, 4), (Vb(Fr(3, 2)) - Fr(3, 4), Fr(0)))],
           "hh1ow x a (x + C * (a - 1)) u - 3 / 4 + 1 / 1000", ['a', 'C', 'u'], "`w ≥ 3/4 - 1/1000` on `1 ≤ α ≤ x ≤ 3/2`."),
    'wA': ((O.w - R(3, 4) + R(1, 1000)).subs(b, bC), Fr(3, 2), Fr(1, 2),
           [(a, Fr(6, 5), (Fr(3, 10), Fr(1))), (C, Cm(Fr(3, 2)), (Cp(Fr(2)) - Cm(Fr(3, 2)), Fr(0))), (u, Fr(3, 4), (Vb(Fr(2)) - Fr(3, 4), Fr(0)))],
           "hh1ow x a (x + C * (a - 1)) u - 3 / 4 + 1 / 1000", ['a', 'C', 'u'], "`w ≥ 3/4 - 1/1000` on `6/5 ≤ α ≤ x`, `3/2 ≤ x ≤ 2`."),
}
boxB = dict(X0=Fr(3, 2), sx=1, Zmax=Fr(1, 2), Amax=(Fr(1, 5), Fr(0)), Clo=Fr(1, 2), Chi=Fr(4, 5), mumax=Fr(2, 249))
boxB2 = dict(boxB, Clo=Fr(5, 9), Chi=Fr(10, 13))
boxS1 = dict(X0=Fr(1), sx=1, Zmax=Fr(1, 4), Amax=(Fr(0), Fr(1)), Clo=Fr(8, 17), Chi=Cp(Fr(5, 4)), mumax=Vb(Fr(5, 4)) - Fr(3, 4))
boxS2 = dict(X0=Fr(5, 4), sx=1, Zmax=Fr(1, 4), Amax=(Fr(1, 4), Fr(1)), Clo=Cm(Fr(5, 4)), Chi=Cp(Fr(3, 2)), mumax=Vb(Fr(3, 2)) - Fr(3, 4))
b13 = x + R(10, 13) * (a - 1)
UPRIME = 15 * (x - 1) ** 3 / (8 * (1 + x) * (35 * x + 13) * (b - 1) ** 2)
PK = ["have hbm : x + t - 1 ≠ 0 := by linarith only [hx0, ht]", "have h35 : 35 * x + 13 ≠ 0 := by linarith only [hx0]",
      "have hS : 1 + x ≠ 0 := by linarith only [hx0]"]
SPEC3 = {
    'OB0': (O.R2b - R(1, 40), "hh1oR2b x a b u - 1 / 40", boxB2, (), "`∂_βR̄₂ ≥ 1/40` on the outer `B` box (log form)."),
    'OBV': (c * O.R2b + 15 * (x - 1) / (8 * (1 + x) * (35 * x + 13)) * (O.Gu - c * O.R2u) - c / 1000,
            "7 / 96 * hh1oR2b x a b u + 15 * (x - 1) / (8 * (1 + x) * (35 * x + 13)) * (hh1oGu x a u - 7 / 96 * hh1oR2u x a b) - 7 / 96000",
            boxB2, PK[1:], "`c∂_βR̄₂ + (15(x - 1)/(8S(35x + 13)))∂_uF₀ ≥ c/1000` on the outer `B` box (log form; the factor bounds `|∂_βu_ℓ|`)."),
    'OM1': (R(1, 20) - (O.Gu - c * O.R2u), "1 / 20 - (hh1oGu x a u - 7 / 96 * hh1oR2u x a b)", boxB, (), "`∂_uF₀ ≤ 1/20` on the outer `B` box."),
    'OA0': ((O.Ga - c * (O.R2a + R(10, 13) * O.R2b)).subs(b, b13) - R(1, 250),
            "hh1oGa x a u - 7 / 96 * (hh1oR2a x a (x + 10 / 13 * (a - 1)) u + 10 / 13 * hh1oR2b x a (x + 10 / 13 * (a - 1)) u) - 1 / 250",
            boxB, (), "`(∂_α + (10/13)∂_β)F₀ ≥ 1/250` on `β = x + (10/13)(α - 1)` (outer `B` box, log form, without `ε`)."),
    'wS1': (O.w - R(3, 4), "hh1ow x a b u - 3 / 4", boxS1, (), "`w ≥ 3/4` on `1 ≤ α ≤ x ≤ 5/4`."),
    'wS2': (O.w - R(3, 4), "hh1ow x a b u - 3 / 4", boxS2, (), "`w ≥ 3/4` on `1 ≤ α ≤ x`, `5/4 ≤ x ≤ 3/2`."),
}
# wA pieces: (x0, x1, alo, (c0, c1))
WA = {'wA1': (Fr(3, 2), Fr(7, 4), Fr(6, 5), (Fr(3, 10), Fr(1))),
      'wA2': (Fr(7, 4), Fr(15, 8), Fr(6, 5), (Fr(1, 10), Fr(0))),
      'wA3': (Fr(7, 4), Fr(15, 8), Fr(13, 10), (Fr(9, 20), Fr(1))),
      'wA4': (Fr(15, 8), Fr(2), Fr(6, 5), (Fr(1, 20), Fr(0))),
      'wA5': (Fr(15, 8), Fr(2), Fr(5, 4), (Fr(1, 20), Fr(0))),
      'wA6': (Fr(15, 8), Fr(2), Fr(13, 10), (Fr(23, 40), Fr(1)))}
for k_, (x0, x1, alo, cc) in WA.items():
    GSPEC[k_] = ((O.w - R(3, 4) + R(1, 300)).subs(b, bC), x0, x1 - x0,
                 [(a, alo, cc), (C, Cm(x0), (Cp(x1) - Cm(x0), Fr(0))), (u, Fr(3, 4), (Vb(x1) - Fr(3, 4), Fr(0)))],
                 "hh1ow x a (x + C * (a - 1)) u - 3 / 4 + 1 / 300", ['a', 'C', 'u'],
                 f"`w ≥ 3/4 - 1/300` on `{x0} ≤ x ≤ {x1}`, `{alo} ≤ α ≤ {alo + cc[0] - cc[1] * x0} + {cc[1]}x` (`C = (β - x)/(α - 1)`).")
# step S at the two terminal norms (u substituted)
SA_E = (-(O.Ga - c * (O.R1a + C * O.R1b))).subs(b, bC)
SA_LE = "-(hh1oGa x a u - 7 / 96 * (hh1oR1a x a (x + C * (a - 1)) u + C * hh1oR1b x a (x + C * (a - 1)) u))"
# F1 on the shared face a = 6/5
from gen_ouni import F1 as F1o, UF, VB, x as xo, a as ao, b as bo, u as uo
Cs = sp.Symbol('C')
A65KEY = ["rw [hu]",
          "simp only [hh1oF1, hh1oF0, hh1oR2, hh1oT, hh1ow, hh1oEL, hh1oG, hh1oL, hh1od, hh1ov, hh1oE, hh1oK, hsDg, hh1oy, hh1ell, {U}]",
          "field_simp", "subst hb", "subst ha", "ring"]
A65PRE = ["have ha00 : a ≠ 0 := by rw [ha]; norm_num", "have hab : 0 < a + b := by rw [ha, hb]; nlinarith only [hx0, hv00]",
          "have hab0 : a + b ≠ 0 := hab.ne'", "have hK : 6 * a ^ 2 + 1 ≠ 0 := by positivity",
          "have hy1 : 2 * (a + b) / (7 * a) + 1 ≠ 0 := by have h7 : 0 < 2 * (a + b) / (7 * a) := div_pos (by linarith) (by rw [ha]; norm_num); linarith",
          "have hS : 1 + x ≠ 0 := by linarith only [hx0]", "have hS' : x + 1 ≠ 0 := by linarith only [hx0]",
          "have h35 : 35 * x + 13 ≠ 0 := by linarith only [hx0]"]
for nm_, U_, lu, ud in [('A65uf', UF, 'hsUf x', 'hsUf'), ('A65vb', VB, 'hsVbar x', 'hsVbar')]:
    GSPEC[nm_] = ((F1o - R(1, 2500)).subs(uo, U_).subs(bo, xo + Cs / 5).subs(ao, R(6, 5)), Fr(3, 2), Fr(1, 2),
                  [(Cs, Cm(Fr(3, 2)), (Fr(10, 13) - Cm(Fr(3, 2)), Fr(0)))],
                  "hh1oF1 x a b u - 1 / 2500", ['C'],
                  f"`F₁(x, 6/5, x + C/5, {lu}) ≥ 1/2500` on the shared face `α = 6/5`, `3/2 ≤ x ≤ 2`.",
                  dict(xsym=xo, extra_binders='a b u', extra_hyps=["(ha : a = 6 / 5)", "(hb : b = x + C / 5)", f"(hu : u = {lu})"],
                       key_lines=[k.replace('{U}', ud) for k in A65KEY], pos_hyps=A65PRE))
for nm_, U_, lu, ud in [('saUf', UF, 'hsUf x', 'hsUf'), ('saVb', VB, 'hsVbar x', 'hsVbar')]:
    GSPEC[nm_] = (SA_E.subs(u, U_), Fr(1), Fr(1, 5),
                  [(a, Fr(1), (Fr(0), Fr(1))), (C, Fr(8, 17), (Cp(Fr(6, 5)) - Fr(8, 17), Fr(0)))],
                  SA_LE, ['a', 'C'],
                  f"`(∂_α + C∂_β)F₁ ≤ 0` (log form, without the `ε` term) at `u = {lu}` on `1 ≤ α ≤ x ≤ 6/5`.",
                  dict(extra_binders='u', extra_hyps=[f"(hu : u = {lu})"],
                       key_lines=["rw [hu]", "simp only [" + ", ".join(needed(SA_LE) + [ud]) + "]", "field_simp", "ring"],
                       pos_hyps=POSG + ["have h35 : 35 * x + 13 ≠ 0 := by linarith only [hx0]"]))

# region S (x <= 6/5): F1 increases in beta; 2D terminal on the lower chord slope
GSPEC['dS'] = ((-O.R1b).subs(b, x + tS), Fr(1), Fr(1, 5),
               [(a, Fr(1), (Fr(0), Fr(1))), (tS, Fr(0), (Fr(0), Fr(10, 13))), (u, Fr(3, 4), (Vb(Fr(6, 5)) - Fr(3, 4), Fr(0)))],
               "-hh1oR1b x a (x + t) u", ['a', 't', 'u'], "`∂_βR̄₁ ≤ 0` on `1 ≤ α ≤ x ≤ 6/5` (log form).")
LXS = R(8, 17) + R(32, 221) * (xo - 1)
S2PRE = ["have ha00 : a ≠ 0 := by linarith only [hv00]", "have hab : 0 < a + b := by rw [hb]; nlinarith only [hx0, hv00]",
         "have hab0 : a + b ≠ 0 := hab.ne'", "have hK : 6 * a ^ 2 + 1 ≠ 0 := by positivity",
         "have hy1 : 2 * (a + b) / (7 * a) + 1 ≠ 0 := by have h7 : 0 < 2 * (a + b) / (7 * a) := div_pos (by linarith) (by linarith only [hv00]); linarith",
         "have hS : 1 + x ≠ 0 := by linarith only [hx0]", "have hS' : x + 1 ≠ 0 := by linarith only [hx0]",
         "have h35 : 35 * x + 13 ≠ 0 := by linarith only [hx0]"]
for nm_, U_, lu, ud in [('S2uf', UF, 'hsUf x', 'hsUf'), ('S2vb', VB, 'hsVbar x', 'hsVbar')]:
    GSPEC[nm_] = ((F1o - R(1, 8000)).subs(uo, U_).subs(bo, xo + LXS * (ao - 1)), Fr(1), Fr(1, 5),
                  [(ao, Fr(1), (Fr(0), Fr(1)))],
                  "hh1oF1 x a b u - 1 / 8000", ['a'],
                  f"`F₁(x, α, x + L(x)(α - 1), {lu}) ≥ 1/8000` on `1 ≤ α ≤ x ≤ 6/5`, `L(x) = 8/17 + 32(x - 1)/221`.",
                  dict(xsym=xo, extra_binders='b u',
                       extra_hyps=["(hb : b = x + (8 / 17 + 32 / 221 * (x - 1)) * (a - 1))", f"(hu : u = {lu})"],
                       key_lines=["rw [hu]",
                                  "simp only [hh1oF1, hh1oF0, hh1oR2, hh1oT, hh1ow, hh1oEL, hh1oG, hh1oL, hh1od, hh1ov, hh1oE, hh1oK, hsDg, hh1oy, hh1ell, " + ud + "]",
                                  "field_simp", "subst hb", "ring"], pos_hyps=S2PRE))



def build(nm):
    t0 = time.time()
    if nm in GSPEC:
        sp_ = GSPEC[nm]
        e, X0, Zm, tv, le, vn, doc = sp_[:7]
        kw = dict(sp_[7]) if len(sp_) > 7 else {}
        xs = kw.pop('xsym', x)
        cl = ClaimG(e, xs, X0, 1, Zm, tv)
        ok = cl.certify()
        print(nm, ok, 'P', len(cl.P), '%.1fs' % (time.time() - t0), file=sys.stderr)
        assert ok, nm
        if 'pos_hyps' not in kw:
            kw['pos_hyps'] = POSG
        return emit_claimg(cl, f"hh1o_claim_{nm}", le, needed(le), doc, vn, **kw)
    e, le, box, pk, doc = SPEC3[nm]
    cl = Claim3(nm, e, has_b=e.has(b), has_u=e.has(u), **box)
    ok = cl.certify()
    print(nm, ok, 'P', len(cl.P), '%.1fs' % (time.time() - t0), file=sys.stderr)
    assert ok, nm
    return emit_claim3(cl, f"hh1o_claim_{nm}", le, needed(le), doc, pre_key=pk)


HDR = """module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODeriv
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Tw

/-!
# Gate S1, outer face: generated sign claims ({names})

Polynomial sign claims for the outer partial derivatives (`S1ODeriv`) and the envelope `w`. Each
proof clears the denominators (`field_simp`), bounds the numerator termwise in the small variables
and certifies the remaining polynomial in `x` by its Bernstein coefficients. Generated by
`scripts/certificates/short-hand/gen_oclaims.py`.
-/

@[expose] public section

namespace SmoothedOctagon

"""

if __name__ == '__main__':
    out = [build(nm) for nm in sys.argv[2:]]
    open(sys.argv[1], 'w').write(HDR.replace('{names}', ', '.join(sys.argv[2:])) + "\n\n".join(out) + "\n\nend SmoothedOctagon\n")
