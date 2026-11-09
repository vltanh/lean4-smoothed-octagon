from common import *
from bern import *
import pickle, re
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J3 = 24*x**3*C3+12*x**2*C2-C0
e = expand(cancel(J3.subs(t,(1-x-s)/2)/x**2))
d = poly_to_dict(e,[x,s]); n = degs(d,2)
box = ((Fr(1,4),Fr(5,16)),(Fr(0),Fr(1,16)))
eps, H, L, coefs, lins = bern_int_identity(d,2,box,n,['x','s'])
Lp = 1
for c in d.values(): Lp = lcm(Lp, c.denominator)
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
HL = H*L; E0 = eps*H*L*Lp
lean = f"""module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

set_option profiler true in
theorem leaf_test (x s : ℝ) (h0 : 1/4 ≤ x) (h1 : x ≤ 5/16) (h2 : 0 ≤ s) (h3 : s ≤ 1/16) :
    0 < {P} := by
  have a0 : 0 ≤ {lins[0][0]} := by linarith
  have a1 : 0 ≤ {lins[0][1]} := by linarith
  have b0 : 0 ≤ {lins[1][0]} := by linarith
  have b1 : 0 ≤ {lins[1][1]} := by linarith
  have e : ({P}) * {int(HL)} = {int(E0)} + ({S}) := by ring
  have : 0 < ({P}) * {int(HL)} := by rw [e]; positivity
  exact pos_of_mul_pos_left this (by norm_num)
"""
lean = re.sub(r'\^ (\d+)', r'^ (\1 : ℕ)', lean)
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/Test.lean','w').write(lean)
