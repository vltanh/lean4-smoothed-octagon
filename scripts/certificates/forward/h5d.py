import sympy as sp, pickle
from leangen2 import bern_coeffs2
from fractions import Fraction as Fr
mu,v=sp.symbols('mu v')
out=pickle.load(open('H5R.pkl','rb'))
Rt,k=out['R0']
f=sp.lambdify((mu,v),Rt)
import itertools
vals=[(f(i/100,j/100),i/100,j/100) for i in range(101) for j in range(101)]
print('min value',min(vals))
def test(boxes):
    res=[]
    for bx in boxes:
        C,a,b=bern_coeffs2(Rt,mu,v,bx)
        res.append(float(min(min(r) for r in C)))
    return res
for splits in [[Fr(1,2)],[Fr(1,4),Fr(1,2),Fr(3,4)]]:
    pts=[Fr(0)]+splits+[Fr(1)]
    boxes=[((pts[i],pts[i+1]),(Fr(0),Fr(1))) for i in range(len(pts)-1)]
    print(splits, test(boxes))
    boxes=[((Fr(0),Fr(1)),(pts[i],pts[i+1])) for i in range(len(pts)-1)]
    print('v-split',splits, test(boxes))
