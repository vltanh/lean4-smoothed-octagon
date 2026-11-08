import pickle, sympy as sp
from bern import *
a,t,nu=sp.symbols('a t nu')
res=pickle.load(open('S_E34.pkl','rb'))
R,cI,cc,Bn,Bd=res['E4']
s=1  # den sign positive
# piece 1: t in [39/280, 1/4], a in [0,1/7]
C=bern2(Bn,a,t,((0,Fr(1,7)),(Fr(39,280),Fr(1,4))))
print('piece1 max',float(max(max(r) for r in C)))
# piece 2: t in [0,39/280], a = 40 t nu/39, nu in [0,1]
P2=sp.expand(Bn.subs(a,sp.Rational(40,39)*t*nu))
C=bern2(P2,nu,t,((0,1),(0,Fr(39,280))))
print('piece2 max',float(max(max(r) for r in C)), 'deg', sp.Poly(P2,nu,t).degree_list())
