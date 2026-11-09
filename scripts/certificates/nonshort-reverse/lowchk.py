from nhN import *
from common import vbar, Lp, Fl, W, X
import numpy as np, pickle
y = symbols('y')
def Pk(kk, mult):
    e = 6*(q+1)*W**2*X**3*(nhN(t,x,kk,q,vbar,Lp) - mult*(vbar-Fl))
    e = cancel(e.subs(q,1+y))
    P = Poly(expand(e), y)
    return [expand(P.coeff_monomial(y**j)) for j in range(P.degree()+1)]
def Jsigns(C):
    C0,C1,C2,C3 = C[:4]
    return {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
Tx = lambda X_: (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
# unit face
T1,X1 = np.meshgrid(np.linspace(1e-3,0.25,301), np.linspace(0.5,7/3,301))
dom1 = (X1 >= 1-2*T1) & (T1 < Tx(X1)) & (X1 < 7/3-10/3*T1)
# high-ratio face
T2,X2 = np.meshgrid(np.linspace(0.25,0.35,301), np.linspace(0.5,1,301))
dom2 = (T2 < Tx(X2))
for name, kk, TT, XX, dom in [('unit',Integer(1),T1,X1,dom1),('kh',2*t+Rational(1,2),T2,X2,dom2)]:
    C = Pk(kk, q-1)
    print(name, 'deg', len(C)-1)
    J = Jsigns(C)
    for i in J:
        f = lambdify((t,x), J[i]/x**2, 'numpy')
        val = f(TT,XX)
        j = np.argmin(np.where(dom,val,np.inf))
        print('  J',i, val[dom].min(), TT.flat[j], XX.flat[j])
