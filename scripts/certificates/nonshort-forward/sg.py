from model import *
import numpy as np, pickle
R_=sp.Rational
# chi lemma: N1(V2, L+) on q in [1, 4W/(7p)]
N1 = Nc(1, V2, Lp)
num, den = sp.fraction(sp.together(N1))
print('den', sp.factor(den))
Ps = sp.expand(num.subs({t:(1-h)/2, x:h+j}))
f = sp.lambdify((h,j,q), Ps, 'numpy')
H,Jv,Z = np.meshgrid(np.linspace(6/25,1/3,25), np.linspace(0,1/30,25), np.linspace(0,1,25), indexing='ij')
pp = (1-H)/2+H+Jv; WW = 1+H+Jv
Qv = 1 + Z*(4*WW/(7*pp)-1)
vals = f(H,Jv,Qv)
print('chi N1 min', vals.min(), 'max', vals.max())
pickle.dump(Ps, open('chiN1.pkl','wb'))
