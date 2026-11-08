import pickle, sympy as sp
from bern import *
a,t=sp.symbols('a t')
NT=pickle.load(open('N_T.pkl','rb'))
C=bern2(NT,a,t,((0,Fr(1,7)),(0,Fr(1,4))))
print('T min',float(minc(C)))
for r in C: print([round(float(v),3) for v in r])
NE=pickle.load(open('N_E.pkl','rb'))
C=bern2(NE+sp.Rational(1,100)*t+sp.Rational(1,100)*a,a,t,((0,Fr(1,7)),(0,Fr(1,4))))
print('E+ (a+t)/100 max',float(max(max(r) for r in C)))
print(sp.Poly(NE,a,t).as_expr())
