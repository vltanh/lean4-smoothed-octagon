from nhN import *
from common import vbar, Lp, Fl, W, X
import numpy as np, pickle
y = symbols('y')
def Qk(kk):
    I0 = kk + t*x + t*W*(kk-2*t); I1 = kk*X + t*x*X**2
    A = x*q*(I0 + I1*(q-1))
    e = 6*(q+1)*W**2*X**3*(nhN(t,x,kk,q,vbar,Lp) - A*(vbar-Fl))
    e = cancel(e.subs(q,1+y))
    assert e.is_polynomial(t,x,y)
    P = Poly(expand(e), y)
    return [expand(P.coeff_monomial(y**j)) for j in range(P.degree()+1)]
def Jl(P):
    P0,P1,P2,P3,P4 = P
    return {0:P0, 1:P1+2*P0, 2:P2+48*P0, 3:P3+4*P2, 4:P3-P0, 5:P4-P0}
Tx = lambda X_: (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
T1,X1 = np.meshgrid(np.linspace(1e-3,0.25,301), np.linspace(0.5,7/3,301))
dom1 = (X1 >= 1-2*T1) & (T1 < Tx(X1)) & (X1 < 7/3-10/3*T1)
T2,X2 = np.meshgrid(np.linspace(0.25,0.35,301), np.linspace(0.5,1,301))
dom2 = (T2 < Tx(X2)) | True
res={}
for name, kk, TT, XX, dom in [('unit',Integer(1),T1,X1,dom1),('kh',2*t+Rational(1,2),T2,X2,dom2)]:
    P = Qk(kk)
    res[name]=P
    print(name, 'deg', len(P)-1)
    J = Jl(P)
    for i in J:
        f = lambdify((t,x), J[i], 'numpy')
        val = f(TT,XX)
        j = np.argmin(np.where(dom,val,np.inf))
        print('  J',i, val[dom].min(), TT.flat[j], XX.flat[j])
pickle.dump(res, open('lowQ.pkl','wb'))
