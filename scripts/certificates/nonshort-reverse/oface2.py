from nhN import *
from common import vbar, Lp, W, X
import pickle
h,s = symbols('h s')
ko = 2*t+x
p = t+x; Yn = x*(x+2)
B = ko+2*t*x+x**2
H0 = ko/t*(v-1+t**2)+t*(2-t)
wU = (ko**2-ko*t+t**2+H0*Yn+v*Yn**2)/B**2
alpha = (1-t) - p**2/W + p**3/(W*ko) - W*v + p*(H0+2*v*Yn)/(W*ko)
beta = ko*(1-wU)
gamma = -p**2/ko
# nhR
Rn = (1-t) + q*B/W - p**2/W - p**2/(q*B/W) + p**3/B - p*L - W*v - q*B/W*wU + p*(H0+2*v*Yn)/B
print(simplify(Rn - (alpha + beta*q + gamma/q - p*L)))
P = pickle.load(open('ofaceP.pkl','rb'))
lhs = 24*ko**3*(W+ko)*X**3*nhN(t,x,ko,W/ko,vbar,Lp.subs(q,W/ko))
rhs = B*P.subs({h:1-2*t, s:2*t+x-1})
print(simplify(lhs-rhs))
