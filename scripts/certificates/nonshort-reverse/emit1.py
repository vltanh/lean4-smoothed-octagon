from common import *
from bern import *
import pickle
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J3 = 24*x**3*C3+12*x**2*C2-C0
e = expand(cancel(J3.subs(t,(1-x-s)/2)/x**2))
d = poly_to_dict(e,[x,s]); n = degs(d,2); print(n)
box = ((Fr(1,4),Fr(5,16)),(Fr(0),Fr(1,16)))
b = bernstein(d,2,box,n)
eps = min(b.values()); print(float(eps))
K = scale_factor(box,n)
pe = str(e).replace('**','^')
s_ = bern_expr(b,n,box,['x','s'],eps)
lean = f"""module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

theorem leaf_test (x s : ℝ) (h0 : {lean_num(box[0][0])} ≤ x) (h1 : x ≤ {lean_num(box[0][1])}) (h2 : {lean_num(box[1][0])} ≤ s) (h3 : s ≤ {lean_num(box[1][1])}) :
    0 < {pe} := by
  have e : ({pe}) * {lean_num(K)} = {lean_num(eps*K)} + ({s_}) := by ring
  have : 0 ≤ {s_} := by positivity
  nlinarith
"""
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Nonshort/Reverse/Test.lean','w').write(lean)
print(len(lean))
