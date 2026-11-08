import pickle, sympy as sp
from bern import *
from leangen2 import bern_coeffs2
a,t=sp.symbols('a t')
res=pickle.load(open('Nsym_parts.pkl','rb'))
I=1+t; y=a*I
UBI=(I-1/I)/2-t**3/(3*I*(I+1))
UBc=-y-y**2/2-y**3/3
out={}
for name in ['E','T']:
    p=res[name]
    B=sp.together(p['R'][0]/p['R'][1]+p['cI'][0]/p['cI'][1]*UBI+p['cc'][0]/p['cc'][1]*UBc)
    Bn,Bd=sp.fraction(B); Bn=sp.expand(Bn); Bd=sp.factor(Bd)
    sgn=sp.sign(Bd.subs({a:sp.Rational(1,5),t:sp.Rational(1,5)}))
    print(name,'Bd',Bd,'sign',sgn,'deg',sp.Poly(Bn,a,t).degree_list())
    out[name]=(Bn,Bd,sgn)
    # we need Bn*sgn < 0
    for bx in [((Fr(1,7),Fr(1,4)),(Fr(13,100),Fr(1,4))), ((Fr(1,7),Fr(1,5)),(Fr(13,100),Fr(1,4))), ((Fr(1,5),Fr(1,4)),(Fr(18,100),Fr(1,4)))]:
        C,m,n=bern_coeffs2(sp.expand(-Bn*sgn),a,t,bx)
        print('  box',[(float(u),float(v)) for u,v in bx],'min',float(min(min(r) for r in C)))
pickle.dump(out,open('Nsym_B.pkl','wb'))
