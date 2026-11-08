import sympy as sp, pickle
from fractions import Fraction as Fr
from math import comb
from leangen2 import lean_poly, lnum, pw, bern_coeffs2
m,v,mu=sp.symbols('m v mu')
R3=3*((2-m**2)*v+m*(2-m-v**2))
E_=4*m**4+28*m**2*(1-m)+24*m
R2=(2-m)*v**3-3*m*(m**2-m+10)*v**2+(m**4-13*m**3-14*m**2+24*m+24)*v+E_
C_=m**2*(-m**4+14*m**3-40*m**2-48*m+160)
R1=2*(2-m)*(m**2-2*m+4)*v**3-3*m*(m**3+4*m**2-4*m+32)*v**2+m*(7*m**4-46*m**3+40*m**2-96*m+144)*v+C_
R0=(2-m)*(m**2-2*m+4)**2*v**3-12*m*(m**3+8)*v**2+2*m**2*(3*m**4-16*m**3+20*m**2-56*m+64)*v+4*m**3*(2-m)*(4-m)*(8-m)
def hom_cert(p, e, mubox, eps=0):
    """p(m,v) with p(mu v, v) = v^e * pt(mu,v). Certificate on mu in mubox, v in [0,1]:
    returns (lhs_lean, rhs_lean, mincoef) with lhs = v^(a-e) * (p - eps*v^e*v^?)..."""
    pt=sp.expand(sp.cancel(p.subs(m,mu*v)/v**e)) - eps
    C,a,b=bern_coeffs2(pt,mu,v,(mubox,(0,1)))
    mn=min(min(r) for r in C)
    m0,m1=map(Fr,mubox); dm=m1-m0
    terms=[]
    for i in range(a+1):
        for j in range(b+1):
            c=C[i][j]*comb(a,i)*comb(b,j)/dm**a
            if c==0: continue
            parts=[f"({lnum(c)})"]
            f1="m" if m0==0 else f"(m - {lnum(m0)} * v)"
            f2=f"({lnum(m1)} * v - m)" if m1!=1 else "(v - m)"
            for base,ex in ((f1,i),(f2,a-i),("v",j),("(1 - v)",b-j)):
                if ex: parts.append(pw(base,ex))
            terms.append(" * ".join(parts))
    return a,mn,(" +\n      ".join(terms))
out=[]
hyps="(hm : 0 ≤ m) (hmv : m ≤ v) (hv1 : v ≤ 1)"
for name,R,e in [('R3',R3,1),('R2',R2,1),('R1',R1,2)]:
    a,mn,rhs=hom_cert(R,e,(0,1))
    assert mn>=0
    k=a-e
    lhs=f"v ^ {k} * ({lean_poly(R,(m,v))})" if k>0 else f"({lean_poly(R,(m,v))})"
    out.append(f"""theorem fs_H5_{name} {{m v : ℝ}} {hyps} :
    0 ≤ {lean_poly(R,(m,v))} := by
  have b1 : 0 ≤ m := hm
  have b2 : 0 ≤ v - m := by linarith
  have b3 : 0 ≤ v := by linarith
  have b4 : 0 ≤ 1 - v := by linarith
  have key : {lhs} =
      {rhs} := by ring
  have h : 0 ≤ {lhs} := by rw [key]; clear key; positivity
  {'exact h' if k==0 else f'''rcases eq_or_lt_of_le b3 with hv0 | hv0
  · have hm0 : m = 0 := by linarith
    subst hm0; rw [← hv0]; norm_num
  · exact nonneg_of_mul_nonneg_right (by linarith [h]) (pow_pos hv0 {k})'''}
""")
# R0 with split mu at 1/2, eps=3
blocks=[]
for k_,mb in enumerate([(0,Fr(1,2)),(Fr(1,2),1)]):
    a,mn,rhs=hom_cert(R0,3,mb,eps=3)
    assert mn>=0, mn
    blocks.append((a,rhs,mb))
a=blocks[0][0]; k=a-3
R0l=lean_poly(R0,(m,v))
lhs=f"v ^ {k} * ({R0l}) - 3 * v ^ {a}"
out.append(f"""theorem fs_H5_R0 {{m v : ℝ}} {hyps} (hv : 0 < v) :
    0 < {R0l} := by
  have b3 : 0 ≤ v := hv.le
  have b4 : 0 ≤ 1 - v := by linarith
  have h : 0 ≤ {lhs} := by
    rcases le_total (2 * m) v with hs | hs
    · have b1 : 0 ≤ m := hm
      have b2 : 0 ≤ 1 / 2 * v - m := by linarith
      have key : {lhs} =
          {blocks[0][1]} := by ring
      rw [key]; clear key; positivity
    · have b1 : 0 ≤ m - 1 / 2 * v := by linarith
      have b2 : 0 ≤ v - m := by linarith
      have key : {lhs} =
          {blocks[1][1]} := by ring
      rw [key]; clear key; positivity
  have h3 : 0 < 3 * v ^ {a} := by positivity
  have h4 : 0 < v ^ {k} * ({R0l}) := by linarith
  exact pos_of_mul_pos_right h4 (pow_pos hv {k}).le
""")
open('H5R.lean','w').write("\n".join(out))
print('ok')
