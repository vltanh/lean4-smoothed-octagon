from nsrN import *
from common import vbar, Lp, Fl, W, X
import pickle
y = symbols('y')
res = pickle.load(open('lowQ.pkl','rb'))
for name, kk in [('unit',Integer(1)),('kh',2*t+Rational(1,2))]:
    Nv = expand(nsrN(t,x,kk,q,v,L)).coeff(v,1)
    A = -Nv
    I0 = kk + t*x + t*W*(kk-2*t); I1 = kk*X + t*x*X**2
    print(name, simplify(A - x*q*(I0+I1*(q-1))))
    e = 6*(q+1)*W**2*X**3*(nsrN(t,x,kk,q,vbar,Lp) - A*(vbar-Fl))
    P = res[name]
    print(simplify(e - sum(P[j]*(q-1)**j for j in range(5))))
# T identity
g = 1-(1-t)*(t+x)/W**2
Nx = -2*x**3-x**2+10*x+12
print(simplify((vbar-g)*3*W**2*X**3 - (1-t)*x*(Nx - 3*X**3*t)))
