from common import *
from gen import *
import pickle
C = [expand(c) for c in pickle.load(open('unitC.pkl','rb'))]
for i,c in enumerate(C):
    print(f"/-- The coefficient of `y^{i}` in the unit-shape cubic `P` (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` (6)). -/")
    print(f"noncomputable def nhUC{i} (t x : ℝ) : ℝ :=\n  {lpoly(c,[t,x],['t','x'])}\n")
