from nhN import *
from common import vbar, Lp, Fl, W, X
import numpy as np, pickle
y = symbols('y')
def Pk(kk):
    e = 6*(q+1)*W**2*X**3*(nhN(t,x,kk,q,vbar,Lp) - (q-1)*(vbar-Fl))
    e = cancel(e.subs(q,1+y))
    P = Poly(expand(e), y)
    return [expand(P.coeff_monomial(y**j)) for j in range(P.degree()+1)]
ks = Rational(20,3)*t**2
C = Pk(ks)
pickle.dump(C, open('highTC.pkl','wb'))
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
T_,X_ = np.meshgrid(np.linspace(0.4,0.5,401), np.linspace(0.12,1/3,401))
Tx = (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
dom = (20/3*T_**2 < 2*T_+2*X_+X_**2) & (T_ < Tx)
for i in J:
    f = lambdify((t,x), J[i]/x**2, 'numpy')
    val = f(T_,X_)
    j = np.argmin(np.where(dom,val,np.inf))
    print(i, val[dom].min(), T_.flat[j], X_.flat[j])
