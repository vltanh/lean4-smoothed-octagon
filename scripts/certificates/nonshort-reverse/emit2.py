from common import *
from bern import *
import pickle
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J3 = 24*x**3*C3+12*x**2*C2-C0
e = expand(cancel(J3.subs(t,(1-x-s)/2)/x**2))
d = poly_to_dict(e,[x,s]); n = degs(d,2)
box = ((Fr(1,4),Fr(5,16)),(Fr(0),Fr(1,16)))
eps, H, L, coefs, lins = bern_int_identity(d,2,box,n,['x','s'])
Lp = 1
for c in d.values(): Lp = lcm(Lp, c.denominator)
# identity: Lp * p * (H*L) = Lp*(eps*H*L) + Lp*L*sum coefs ...
P = emit_poly_int(d,['x','s'],Lp)
terms=[]
for alpha,c in coefs.items():
    ci = c*L*Lp; assert ci.denominator==1; ci=int(ci)
    if ci==0: continue
    f=[str(ci)]
    for i in range(2):
        if alpha[i]>0: f.append(f"{lins[i][0]} ^ {alpha[i]}")
        if n[i]-alpha[i]>0: f.append(f"{lins[i][1]} ^ {n[i]-alpha[i]}")
    terms.append(" * ".join(f))
S=" + ".join(terms)
HL = H*L; assert HL.denominator==1
E0 = eps*H*L*Lp; assert E0.denominator==1
lean = f"""module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

theorem leaf_test (x s : ℝ) (h0 : 1/4 ≤ x) (h1 : x ≤ 5/16) (h2 : 0 ≤ s) (h3 : s ≤ 1/16) :
    0 < {P} := by
  have e : ({P}) * {int(HL)} = {int(E0)} + ({S}) := by ring
  have : 0 ≤ {S} := by positivity
  nlinarith
"""
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Nonshort/Test.lean','w').write(lean)
print(len(lean), int(HL))
