import pickle, sympy as sp
from bern import *
a,t,LI,Lc=sp.symbols('a t LI Lc')
out=pickle.load(open('resV_ET.pkl','rb'))
I=1+t; y=a*I
UBI=(I-1/I)/2-t**3/(3*I*(I+1))
UBc=-y-y**2/2-y**3/3
for name in ['E','T']:
    R,cI,cc,dn=out[name]
    num=sp.together(R+cI*UBI+cc*UBc)
    N,D=sp.fraction(num)
    N=sp.expand(N); D=sp.factor(sp.expand(D*dn))
    print(name,'D(total)=',D)
    print(name,'deg',sp.Poly(N,a,t).degree_list())
    # sign: we need value = N/D_total <0
    C=bern2(N,a,t,((0,Fr(1,7)),(0,Fr(1,4))))
    print(name,'bern max',float(max(max(r) for r in C)), 'corner', C[0][0])
    pickle.dump(N,open(f'N_{name}.pkl','wb'))
