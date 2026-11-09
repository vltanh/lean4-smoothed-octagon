import pickle, sympy as sp
from bern import *
a,t=sp.symbols('a t')
res=pickle.load(open('S_E34.pkl','rb'))
box=((0,Fr(1,7)),(0,Fr(1,4)))
for name in ['E3','E4']:
    R,cI,cc,Bn,Bd=res[name]
    # sign of Bd at center
    s=sp.sign(Bd.subs({a:sp.Rational(1,14),t:sp.Rational(1,8)}))
    C=bern2(Bn*s,a,t,box)
    mx=max(max(r) for r in C); mn=minc(C)
    print(name,'den sign',s,'numer*sign bern max',float(mx),'min',float(mn))
    # numeric sampling of cI, cc on box
    fI=sp.lambdify((a,t),cI); fc=sp.lambdify((a,t),cc)
    mnI=min(fI(i/70/7+1e-9, j/80/4+1e-6) for i in range(71) for j in range(81))
    mnc=min(fc(i/70/7+1e-9, j/80/4+1e-6) for i in range(71) for j in range(81))
    print('   min cI',mnI,'min cc',mnc)
