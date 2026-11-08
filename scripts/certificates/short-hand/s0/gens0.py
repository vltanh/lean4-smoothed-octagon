"""Generator of the heavy S0 face-sign certificates (prefix hh0).

For each face function f in {C2, CT, C8} (central face q = q_c, u = û) and {OT, O8, O2} (outer face
q = 1/7, u = ū) it writes the cleared numerator N_f (hsF = -N_f/Den_f, Den_f > 0) and a nested
Bernstein certificate of 0 < N_f:
  level 1: b = β - x on [0, gn1/gd1], gn1 = x(7x+1)(α-1), gd1 = 4x²+11x+1 (abstract lemma hh0_bern{d1});
  level 2: a = α - α₀ on [0, gn2/gd2] (abstract lemma hh0_bern{d2});
  level 3: the level-2 Bernstein coefficients are polynomials in X = x - 12/5 with nonnegative
           coefficients and positive constant term (ring_nf; positivity).
"""
import pickle, sys
from sympy import *
from math import comb
from model import x, al, be
from leanpoly import poly_str
from bernlemmas import pw, prod

X,a,b=symbols('X a b')
xs = X + Rational(12,5)
Rx = 4*x**2+11*x+1
CEN=dict(al0=Integer(1), al0s="1", kap=Integer(0), kaps=None,
          gn1=x*(7*x+1)*(al-1), gd1=Rx,
          gn1s="(X + 12 / 5) * (7 * (X + 12 / 5) + 1) * (a + 1 - 1)",
          gd1s="(4 * (X + 12 / 5) ^ (2 : ℕ) + 11 * (X + 12 / 5) + 1)",
          gn2=5*X+4, gd2=Integer(12), gn2s="(5 * X + 4)", gd2s="12")
OUT=dict(al0=Integer(1), al0s="1", kap=(22*x+20)/55-1, kaps="((22 * (X + 12 / 5) + 20) / 55 - 1)",
          gn1=x*(7*x+1)*(al-1), gd1=Rx,
          gn1s="(X + 12 / 5) * (7 * (X + 12 / 5) + 1) * (a + 1 - 1)",
          gd1s="(4 * (X + 12 / 5) ^ (2 : ℕ) + 11 * (X + 12 / 5) + 1)",
          gn2=33*X+Rational(296,5), gd2=Integer(55), gn2s="(33 * X + 296 / 5)", gd2s="55")
HSF={
 'C2':"hsF x be al (hsUhat x be) (hsQc x al) 2\n      (5 / (2 * (hsRA al be / hsQc x al)) - 11 / 9) (1 / 2)",
 'CT':"hsF x be al (hsUhat x be) (hsQc x al) (hsRA al be / hsQc x al) 0 (1 / 2)",
 'C8':"hsF x be al (hsUhat x be) (hsQc x al) (8 * (hsRA al be / hsQc x al) / 9) (-1 / 9)\n      (1 / 2)",
 'OT':"hsF x be al (hsUbar x be) (1 / 7) (7 * hsRA al be) 0 (1 / 2)",
 'O8':"hsF x be al (hsUbar x be) (1 / 7) (8 * (7 * hsRA al be) / 9) (-1 / 9) (1 / 2)",
 'O2':"hsF x be al (hsUbar x be) (1 / 7) 2 (5 / (2 * (7 * hsRA al be)) - 11 / 9) (1 / 2)",
}
DESC={'C2':"central face, `τ = 2` test `F(2, 5/(2T) - 11/9)`",
      'CT':"central face, `τ = T` test `F(T, 0)`",
      'C8':"central face, `τ = 8T/9` test `F(8T/9, -1/9)`",
      'OT':"outer face, `τ = T` test `F(T, 0)`",
      'O8':"outer face, `τ = 8T/9` test `F(8T/9, -1/9)`",
      'O2':"outer face, `τ = 2` test `F(2, 5/(2T) - 11/9)`"}
KEY={'C2':'c2','CT':'cT','C8':'c8','OT':'oT','O8':'o8','O2':'o2'}
def dstr(d):
    # Lean string of the denominator (as computed by sympy factor)
    s=str(d).replace('**','^')
    return s
DEN={
 'C2':"72 * al * (al + be) * (be - 1) * (x + 1) * (35 * x + 13) * (al ^ 2 + x ^ 2 + 2 * x) ^ 2",
 'CT':"8 * al * (al + be) * (be - 1) * (x + 1) * (35 * x + 13) * (al ^ 2 + x ^ 2 + 2 * x) ^ 2",
 'C8':"72 * al * (al + be) * (be - 1) * (x + 1) * (35 * x + 13) * (al ^ 2 + x ^ 2 + 2 * x) ^ 2",
 'OT':"4704 * al ^ 4 * x ^ 2 * (al + be) * (be - 1) * (x + 1) * (35 * x + 13)",
 'O8':"42336 * al ^ 4 * x ^ 2 * (al + be) * (be - 1) * (x + 1) * (35 * x + 13)",
 'O2':"14112 * al ^ 4 * x ^ 2 * (al + be) * (be - 1) * (x + 1) * (35 * x + 13)"}

def combos(cs, gn, gd):
    n=len(cs)-1
    return [expand(sum(comb(n-i,m-i)*cs[i]*gn**i*gd**(m-i) for i in range(m+1))) for m in range(n+1)]
def upoly(e): return poly_str(e,(X,),['X'])
def plan(N, sp):
    P=Poly(expand(N.subs(be,x+b)),b); d1=P.degree()
    Ms=[expand(P.coeff_monomial(b**k)) for k in range(d1+1)]
    sub={x:xs, al:a+sp['al0'].subs(x,xs)}
    nk=[]
    for k in range(d1+1):
        ck=expand(Ms[k].subs(sub,simultaneous=True)); Q=Poly(ck,a)
        nk.append([expand(Q.coeff_monomial(a**j)) for j in range(Q.degree()+1)])
    cs=[sum(nk[k][j]*a**j for j in range(len(nk[k]))) for k in range(d1+1)]
    gn1=expand(sp['gn1'].subs(sub,simultaneous=True)); gd1=expand(sp['gd1'].subs(sub,simultaneous=True))
    Bs=combos(cs,gn1,gd1)
    lev=[]
    kap=sp['kap'].subs(x,xs)
    for m,Bm in enumerate(Bs):
        if kap!=0: Bm=expand(Bm.subs(a,a+kap))
        Q=Poly(Bm,a); d2=Q.degree()
        es=[expand(Q.coeff_monomial(a**j)) for j in range(d2+1)]
        Cs=combos(es,sp['gn2'],sp['gd2'])
        for j,C in enumerate(Cs):
            co=Poly(C,X).all_coeffs()[::-1]
            assert all(c>=0 for c in co) and co[0]>0, (m,j)
        lev.append((d2,es))
    return d1,Ms,nk,lev

def part_defs(T, N, d1, Ms, nk, lev, desc):
    L=[]
    L.append(f"/-- The cleared numerator of the {desc}: `hsF = -{T}N/Den` with `Den > 0`. -/\n"
             f"noncomputable def {T}N (x al be : ℝ) : ℝ :=\n  {poly_str(N,(x,al,be),['x','al','be'])}\n")
    for k,M in enumerate(Ms):
        L.append(f"/-- Coefficient of `(β - x)^{k}` in `{T}N`. -/\nnoncomputable def {T}M{k} (x al : ℝ) : ℝ :=\n  {poly_str(M,(x,al),['x','al'])}\n")
    for k in range(d1+1):
        for j in range(len(nk[k])):
            L.append(f"noncomputable def {T}n{k}_{j} (X : ℝ) : ℝ :=\n  {upoly(nk[k][j])}\n")
        L.append(f"/-- `{T}M{k}` in the shifted variables `X = x - 12/5`, `a = α - α₀`. -/\nnoncomputable def {T}c{k} (X a : ℝ) : ℝ :=\n  " +
                 " + ".join(prod(f"{T}n{k}_{j} X", pw("a",j)) for j in range(len(nk[k])))+"\n")
    for m,(d2,es) in enumerate(lev):
        for j in range(d2+1):
            L.append(f"noncomputable def {T}e{m}_{j} (X : ℝ) : ℝ :=\n  {upoly(es[j])}\n")
    return L
def part_lev23(T, sp, lev, public_B):
    L=[]
    for m,(d2,es) in enumerate(lev):
        enames=[f"{T}e{m}_{j}" for j in range(d2+1)]
        for j in range(d2+1):
            ts=[]
            for i in range(j+1):
                c=comb(d2-i,j-i)
                ts.append(prod(None if c==1 else str(c), f"{T}e{m}_{i} X", pw(sp['gn2s'],i), pw(sp['gd2s'],j-i)))
            stmt=" + ".join(ts)
            L.append(f"private theorem {T}_C{m}_{j} (X : ℝ) (hX : 0 ≤ X) :\n    0 < {stmt} := by\n  unfold {' '.join(enames[:j+1])}\n  ring_nf\n  positivity\n")
        P=" + ".join(prod(f"{T}e{m}_{j} X", pw("a",j)) for j in range(d2+1))
        args=" ".join(f"({T}_C{m}_{j} X hX)" for j in range(d2+1))
        vis="theorem" if public_B else "private theorem"
        doc=f"/-- Level 2 of the certificate of `{T}N`: the `m = {m}` level-1 Bernstein coefficient is positive. -/\n" if public_B else ""
        L.append(f"{doc}{vis} {T}_B{m} (X a : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ a) (ha' : {sp['gd2s']} * a ≤ {sp['gn2s']}) :\n    0 < {P} :=\n  hh0_bern{d2} ha ha' (by norm_num) {args}\n")
    return L
def part_L1(T, sp, d1, nk, lev, ms, public):
    """Level-1 facts: the m-th scaled Bernstein coefficient in b is positive."""
    L=[]
    av="a" if sp['kaps'] is None else f"(a - {sp['kaps']})"
    for m in ms:
        d2,es=lev[m]
        ts=[]
        for i in range(m+1):
            c=comb(d1-i,m-i)
            ts.append(prod(None if c==1 else str(c), f"{T}c{i} X a", pw(f"({sp['gn1s']})",i), pw(sp['gd1s'],m-i)))
        stmt=" + ".join(ts)
        eun=" ".join(f"{T}e{m}_{j}" for j in range(d2+1))
        cunm=" ".join(f"{T}c{k}" for k in range(m+1))
        nunm=" ".join(f"{T}n{k}_{j}" for k in range(m+1) for j in range(len(nk[k])))
        vis="theorem" if public else "private theorem"
        doc=f"/-- Level 1 of the certificate of `{T}N`: the `m = {m}` Bernstein coefficient in `b`. -/\n" if public else ""
        L.append(f"""{doc}{vis} {T}_L1_{m} (X a : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ {av}) (ha' : {sp['gd2s']} * {av} ≤ {sp['gn2s']}) :
    0 < {stmt} := by
  convert {T}_B{m} X {av} hX ha ha' using 1
  unfold {cunm} {eun} {nunm}
  ring
""")
    return L
def part_lev1(T, sp, d1, Ms, nk, lev, hsf, den, outer):
    L=[]
    P=" + ".join(prod(f"{T}c{k} X a", pw("b",k)) for k in range(d1+1))
    av="a" if sp['kaps'] is None else f"(a - {sp['kaps']})"
    args=" ".join(f"({T}_L1_{m} X a hX ha ha')" for m in range(d1+1))
    L.append(f"""private theorem {T}_pos (X a b : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ {av}) (ha' : {sp['gd2s']} * {av} ≤ {sp['gn2s']})
    (hb : 0 ≤ b) (hb' : {sp['gd1s']} * b ≤ {sp['gn1s']}) :
    0 < {P} :=
  hh0_bern{d1} hb hb' (by positivity) {args}
""")
    Ms_str=" + ".join(prod(f"{T}M{k} x al", pw("(be - x)",k)) for k in range(len(Ms)))
    L.append(f"private theorem {T}_st1 (x al be : ℝ) : {T}N x al be = {Ms_str} := by\n  unfold {T}N {' '.join(f'{T}M{k}' for k in range(len(Ms)))}\n  ring\n")
    for k in range(len(Ms)):
        L.append(f"private theorem {T}_st2_{k} (X a : ℝ) : {T}M{k} (X + 12 / 5) (a + {sp['al0s']}) = {T}c{k} X a := by\n  unfold {T}M{k} {T}c{k} {' '.join(f'{T}n{k}_{j}' for j in range(len(nk[k])))}\n  ring\n")
    L.append(f"""private theorem {T}N_eq (X a b : ℝ) :
    {T}N (X + 12 / 5) (a + {sp['al0s']}) (X + 12 / 5 + b) = {P} := by
  rw [{T}_st1, {', '.join(f'{T}_st2_{k}' for k in range(len(Ms)))}]
  ring
""")
    if outer:
        alo="(22 * x + 20) / 55 ≤ al"; ahi="al ≤ x"
        ha2="by linarith"
    else:
        alo="1 ≤ al"; ahi="al ≤ (5 * x + 4) / 12"
        ha2="by linarith"
    L.append(f"""private theorem {T}_Npos {{x al be : ℝ}} (hx : 12 / 5 ≤ x) (hal : {alo}) (hal' : {ahi})
    (hxb : x ≤ be) (hb : (4 * x ^ 2 + 11 * x + 1) * (be - x) ≤ x * (7 * x + 1) * (al - 1)) :
    0 < {T}N x al be := by
  obtain ⟨X, rfl⟩ : ∃ X, x = X + 12 / 5 := ⟨x - 12 / 5, by ring⟩
  obtain ⟨a, rfl⟩ : ∃ a, al = a + {sp['al0s'].replace('X + 12 / 5','X + 12 / 5')} := ⟨al - ({sp['al0s']}), by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, be = X + 12 / 5 + b := ⟨be - (X + 12 / 5), by ring⟩
  rw [{T}N_eq]
  refine {T}_pos X a b (by linarith) (by linarith) ({ha2}) (by linarith) ?_
  have h := hb
  ring_nf at h ⊢
  linarith
""")
    unf="hsF hsWs hsELs hsA1 hsA2 hsA3 hsE0 hsDg hsRA " + ("hsUbar" if outer else "hsQc hsUhat")
    L.append(f"""private theorem {T}_eq {{x al be : ℝ}} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hxb : x ≤ be) :
    {hsf} =
      -{T}N x al be / ({den}) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hb1 : 0 < be - 1 := by linarith
  have hab : 0 < al + be := by linarith
  have hH : 0 < al ^ 2 + x ^ 2 + 2 * x := by positivity
  have hH' : 0 < x * (x + 2) + al ^ 2 := by positivity
  unfold {unf} {T}N
  rw [eq_div_iff (by positivity)]
  field_simp
  ring
""")
    if outer:
        hyps="""(hx : 12 / 5 ≤ x) (hal : (22 * x + 20) / 55 ≤ al) (hax : al ≤ x)
    (hb : x + 4 * x * (al - 1) / (5 * x + 4) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1))"""
        pre="""  have hal1 : 1 ≤ al := by linarith
  have hxb : x ≤ be := by
    have : 0 ≤ 4 * x * (al - 1) / (5 * x + 4) := by
      apply div_nonneg <;> nlinarith
    linarith
"""
        npos=f"{T}_Npos hx hal hax hxb hR"
        bhi="hb'"
    else:
        hyps="""(hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hal' : al ≤ (5 * x + 4) / 12)
    (hxb : x ≤ be) (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1))"""
        pre="  have hal1 : 1 ≤ al := hal\n"
        npos=f"{T}_Npos hx hal hal' hxb hR"
        bhi="hb"
    L.append(f"""/-- **The {desc_of(T)}** is negative (`hsF = -{T}N/Den`, nested Bernstein certificate of
`{T}N > 0`). -/
theorem {T}_neg {{x al be : ℝ}} {hyps} :
    {hsf} < 0 := by
{pre}  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hb1 : 0 < be - 1 := by linarith
  have hab : 0 < al + be := by linarith
  have hRp : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hR : (4 * x ^ 2 + 11 * x + 1) * (be - x) ≤ x * (7 * x + 1) * (al - 1) := by
    have h := {bhi}
    rw [← sub_le_iff_le_add', le_div_iff₀ hRp] at h
    linarith
  rw [{T}_eq hx hal1 hxb]
  have hN := {npos}
  have hD : 0 < {den} := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hD
""")
    return L
def desc_of(T):
    return DESC[T[3:]]
HDR="""module

{imports}

/-!
# Hand proof of the smaller-short case, heavy S0 sign: {title}

{body}

Generated by `scripts/certificates/short-hand/s0/gens0.py`; every identity is checked by
`ring`/`field_simp`, every final sign by `positivity`.

## Main API

{api}
-/

@[expose] public section

namespace SmoothedOctagon

"""
def write(path, imports, title, body, api, L):
    s=HDR.format(imports="\n".join(f"public import {i}" for i in imports), title=title, body=body, api=api)
    s+="\n".join(L)+"\nend SmoothedOctagon\n"
    open(path,'w').write(s)
    return len(s)
BODY="""The {desc} (`{note}`; inventory HS-S01 {inv}) as the sign of a
cleared numerator `N` in `(x, α, β)`, certified by nested Bernstein expansions: in `b = β - x` on
`[0, x(7x+1)(α-1)/(4x²+11x+1)]`, then in `a = α - α₀` on `[0, {arange}]`; the resulting
coefficients are polynomials in `X = x - 12/5` with nonnegative coefficients (no bound `x ≤ 9`
needed).{route}"""
if __name__=="__main__":
    D=sys.argv[1]
    res=pickle.load(open('nums.pkl','rb'))
    for T0 in sys.argv[2:]:
        T="hh0"+T0
        outer=T0[0]=='O'
        sp=OUT if outer else CEN
        n,d=res[KEY[T0]]; N=-n
        d1,Ms,nk,lev=plan(N,sp)
        L=part_defs(T,N,d1,Ms,nk,lev,DESC[T0])
        note={'C2':"CENTRAL_TAU_TWO_SIGN (3)",'CT':"CENTRAL_DURATION_FACES (5)",'C8':"CENTRAL_DURATION_FACES (5)"}.get(T0,"OUTER_SCALE_LARGE_RATIO_SIGN (7)")
        inv={'C2':'B7','CT':'B8','C8':'B8'}.get(T0,'B9')
        arange="(x - 12/5)·(33/55) + 296/275" if outer else "(5x - 8)/12"
        arange="x - (22x + 20)/55" if outer else "(5x - 8)/12"
        route=("\n\nRoute: the notes' β-lower strip end is replaced by `β ≥ x` (the sign holds on the larger "
               "strip), and their `t`-Bernstein table by the nested certificate.") if outer else \
              ("\n\nRoute: the notes' β-convexity and row-norm table are replaced by the nested certificate.")
        body=BODY.format(desc=DESC[T0], note=note, inv=inv, arange=arange, route=route)
        L2=part_lev23(T,sp,lev,outer)
        split=4 if outer else d1+1
        La=part_L1(T,sp,d1,nk,lev,range(split),outer)
        Lb=part_L1(T,sp,d1,nk,lev,range(split,d1+1),False)
        L1=part_lev1(T,sp,d1,Ms,nk,lev,HSF[T0],DEN[T0],outer)
        base="SmoothedOctagon.Exclusion.Mixed.ShortHand"
        if outer:
            sz1=write(f"{D}/S0{T0}Cert.lean",[f"{base}.Basic",f"{base}.Heavy.S0Bern"],
                      f"{DESC[T0]}, coefficients", body,
                      f"* `{T}N`, `{T}M*`, `{T}c*`, `{T}n*`, `{T}e*`: the numerator and its coefficient polynomials.\n* `{T}_L1_*`: the first level-1 signs.", L+L2+La)
            sz2=write(f"{D}/S0{T0}.lean",[f"{base}.Heavy.S0{T0}Cert"],
                      DESC[T0], body, f"* `{T}_neg`: the sign.", Lb+L1)
            print(T0,sz1,sz2)
        else:
            sz=write(f"{D}/S0{T0}.lean",[f"{base}.Basic",f"{base}.Heavy.S0Bern"],
                     DESC[T0], body, f"* `{T}N` and its coefficient polynomials.\n* `{T}_neg`: the sign.", L+L2+La+Lb+L1)
            print(T0,sz)
