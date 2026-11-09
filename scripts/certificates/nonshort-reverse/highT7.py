from nhN import *
from common import vbar, Lp, Fl, W, X
import numpy as np, pickle
y = symbols('y')
e = 6*(q+1)*W**2*X**3*(nhN(t,x,7*t**2,q,vbar,Lp) - (q-1)*(vbar-Fl))
e = cancel(e.subs(q,1+y))
P = Poly(expand(e), y)
C = [expand(P.coeff_monomial(y**j)) for j in range(P.degree()+1)]
pickle.dump(C, open('highT7C.pkl','wb'))
T_,X_ = np.meshgrid(np.linspace(0.4,0.5,301), np.linspace(1/7,1/3,301))
for name,ee in [('C0',C[0]),('C1',C[1]),('C2',C[2]),('C3',C[3]),('disc',4*C[1]*C[3]-C[2]**2)]:
    f = lambdify((t,x), ee, 'numpy'); val=f(T_,X_)
    j=np.argmin(val); print(name, val.min(), T_.flat[j], X_.flat[j])
