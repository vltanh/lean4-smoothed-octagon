from nsrN import *
from common import vbar, Lp, Fl, W, X, p
import common
h,s = symbols('h s')
ko = 2*t+x
Yn = x*(x+2)
# (5): N(1) at k=ko, L=0
N1 = nsrN(t,x,ko,1,v,0)
print('(5)', expand(N1 - x*((ko + t*Yn)*(1-v) - 2*t*(1-t)*(t+x))))
# (6)
e6 = x*((ko + t*Yn)*(1-vbar) - 2*t*(1-t)*(t+x))
P7 = t*(3*t-1)*x**3 + (18*t**2-15*t+5)*x**2 + (36*t**2-40*t+14)*x + (24*t**2-32*t+12)
print('(6)', simplify(e6 - (1-t)*x**3/(3*W*X**3)*P7))
# (13): Rbar(W/k) = P(h,s)/(24 t k^2 W^2 (W+k) X^3)
q0 = W/ko
Nb = nsrN(t,x,ko,q0,vbar,Lp.subs(q,q0))
B = ko + 2*t*x + x**2
Rb = Nb/(t*B*q0*W)
num = cancel(Rb*24*t*ko**2*W**2*(W+ko)*X**3)
numh = expand(num.subs({t:(1-h)/2, x:h+s}))
C = [factor(Poly(numh, s).coeff_monomial(s**j)) for j in range(8)]
for j,cj in enumerate(C): print(j, cj)
import pickle; pickle.dump(numh, open('ofaceP.pkl','wb'))
