import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from faces import *
import re, pickle
r,C=sp.symbols('r C',positive=True)
Fo=face('o')
y=2/Fo['T']
F1noell=Fo['F1']+c*ell(y)
f=sp.together(F1noell.subs(be,x+C*(al-1)).subs(al,1/r))
ap=sp.apart(f,r)
terms=sp.Add.make_args(sp.expand(ap))
poly=0; rest=0
for t in terms:
    if t.is_polynomial(r): poly+=t
    else: rest+=t
P=sp.Poly(poly,r)
Z=(1+C)+(x-C)*r
Q=sp.factor(sp.cancel(rest*Z))
print('Q free of r:',not Q.has(r))
coef=[sp.factor(P.coeff_monomial(r**k)) for k in range(5)]
for k,ck in enumerate(coef):
    n,dn=sp.fraction(ck)
    print(k,'num terms',len(sp.Poly(sp.expand(n),x,C,u).terms()),'den',dn)
n,dn=sp.fraction(Q); print('Q num terms',len(sp.Poly(sp.expand(n),x,C,u).terms()),'den',dn)
pickle.dump((coef,Q),open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rrep.pkl'),'wb'))
# check identity numerically
pt={x:sp.Rational(17,10),C:sp.Rational(3,5),u:sp.Rational(151,200),r:sp.Rational(7,10)}
print(float((f-(sum(ck*r**k for k,ck in enumerate(coef))+Q/Z)).subs(pt)))
