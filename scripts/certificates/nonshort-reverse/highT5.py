from nsrN import *
from common import vbar, Lp, Fl, W, X
import numpy as np
fN = lambdify((t,x,k,q,v,L), nsrN(t,x,k,q,v,L), 'numpy')
fvb = lambdify((t,x), vbar,'numpy'); fFl = lambdify((t,x,q), Fl,'numpy'); fLp = lambdify(q, Lp,'numpy')
T_,X_,Y_ = np.meshgrid(np.linspace(0.4,0.5,101), np.linspace(0.12,1/3,101), np.linspace(1e-4,4,401), indexing='ij')
Tx = (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
dom = (20/3*T_**2 < 2*T_+2*X_+X_**2) & (T_ < Tx)
K = 20/3*T_**2
Q = 1+Y_
vb=fvb(T_,X_); fl=fFl(T_,X_,Q); Nb=fN(T_,X_,K,Q,vb,fLp(Q))
for lam in [1.6,1.7,1.75,1.8,1.9,2,2.2,2.5]:
    P = Nb - lam*Y_*(vb-fl)
    m = P[dom].min(); j=np.argmin(np.where(dom,P,np.inf))
    print(lam, m, T_.flat[j], X_.flat[j], Y_.flat[j])
