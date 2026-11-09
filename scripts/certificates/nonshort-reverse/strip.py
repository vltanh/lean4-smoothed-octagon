from nhN import *
from common import vbar, Lp, Fl, W, X
import numpy as np, pickle
y = symbols('y')
def Pk(kk):
    e = 6*(q+1)*W**2*X**3*(nhN(t,x,kk,q,vbar,Lp) - (q-1)*(vbar-Fl))
    e = cancel(e.subs(q,1+y))
    P = Poly(expand(e), y)
    return [expand(P.coeff_monomial(y**j)) for j in range(P.degree()+1)]
ks = Rational(29,4)*t**2
C = Pk(ks)
print('deg y', len(C)-1)
pickle.dump(C, open('stripC.pkl','wb'))
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
T_,X_ = np.meshgrid(np.linspace(13/35,0.4,401), np.linspace(0.11,9/35,401))
dom = 29/4*T_**2 < 2*T_+2*X_+X_**2
for i in J:
    f = lambdify((t,x), J[i]/x**2, 'numpy')
    val = f(T_,X_)
    j = np.argmin(np.where(dom,val,np.inf))
    print(i, val[dom].min(), T_.flat[j], X_.flat[j])
