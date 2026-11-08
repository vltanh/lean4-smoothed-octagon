import pickle, sympy as sp
from bern import *
from leangen2 import bern_coeffs2
r,d=sp.symbols('r d')
res=pickle.load(open('Nasym_parts.pkl','rb'))
z=1+r; U=3-d; S=1+z; K=1+U; Z=z**2+U
H=S**2/Z; q=sp.Rational(7,3)*S/K; IW=sp.Rational(49)/(43-9*d)
def UBpade(X): return (X-1/X)/2-(X-1)**3/(3*X*(X+1))
def LB3(X):
    tau=(X-1)/(X+1); return 2*tau+2*tau**3/3
out={}
for name in ['E','T']:
    p=res[name]
    B=sp.together(p['R'][0]/p['R'][1]+p['cH'][0]/p['cH'][1]*UBpade(H)+p['cq'][0]/p['cq'][1]*LB3(q)+p['cW'][0]/p['cW'][1]*UBpade(IW))
    Bn,Bd=sp.fraction(B); Bn=sp.expand(Bn); Bd=sp.factor(Bd)
    sgn=sp.sign(Bd.subs({r:sp.Rational(1,10),d:sp.Rational(1,10)}))
    print(name,'Bd',Bd,'sign',sgn,'deg',sp.Poly(Bn,r,d).degree_list())
    out[name]=(Bn,Bd,sgn)
    for bx in [((0,Fr(1,3)),(0,Fr(3,5))), ((0,Fr(1,6)),(0,Fr(3,5))), ((Fr(1,6),Fr(1,3)),(0,Fr(1,2)))]:
        C,m,n=bern_coeffs2(sp.expand(-Bn*sgn),r,d,bx)
        print('  box',[(float(u),float(v)) for u,v in bx],'min',float(min(min(rr) for rr in C)))
pickle.dump(out,open('Nasym_B.pkl','wb'))
