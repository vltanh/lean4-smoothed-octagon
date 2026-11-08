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
def mkS(names):
    terms=[]
    for alpha,c in coefs.items():
        ci = c*L*Lp; ci=int(ci)
        if ci==0: continue
        f=[str(ci)]
        for i in range(2):
            if alpha[i]>0: f.append(f"{names[2*i]} ^ {alpha[i]}")
            if n[i]-alpha[i]>0: f.append(f"{names[2*i+1]} ^ {n[i]-alpha[i]}")
        terms.append(" * ".join(f))
    return " + ".join(terms)
Sab = mkS(['a','b','c','d'])
S = mkS([lins[0][0],lins[0][1],lins[1][0],lins[1][1]])
HL = H*L; E0 = eps*H*L*Lp
lean = f"""module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

set_option profiler true in
private theorem bpos (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ {Sab} := by positivity

set_option profiler true in
theorem leaf_test (x s : ℝ) (h0 : 1/4 ≤ x) (h1 : x ≤ 5/16) (h2 : 0 ≤ s) (h3 : s ≤ 1/16) :
    0 < {P} := by
  have e : ({P}) * {int(HL)} = {int(E0)} + ({S}) := by ring
  have hS := bpos {lins[0][0]} {lins[0][1]} {lins[1][0]} {lins[1][1]} (by linarith) (by linarith) (by linarith) (by linarith)
  have : 0 < ({P}) * {int(HL)} := by rw [e]; exact add_pos_of_pos_of_nonneg (by norm_num) hS
  exact pos_of_mul_pos_left this (by norm_num)
"""
lean = re.sub(r'\^ (\d+)', r'^ (\1 : ℕ)', lean)
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/Test.lean','w').write(lean)
