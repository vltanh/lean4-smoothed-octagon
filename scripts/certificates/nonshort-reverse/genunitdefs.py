from common import *
from gen import *
import pickle
C = [expand(c) for c in pickle.load(open('unitC.pkl','rb'))]
for i,c in enumerate(C):
    print(f"/-- The coefficient of `y^{i}` in the unit-shape cubic `P`). -/")
    print(f"noncomputable def nsrUC{i} (t x : ℝ) : ℝ :=\n  {lpoly(c,[t,x],['t','x'])}\n")
