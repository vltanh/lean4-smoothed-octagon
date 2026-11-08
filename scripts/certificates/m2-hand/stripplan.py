from sympy import *
from gen import *
import pickle, time
t,x = symbols('t x')
C0,C1,C2,C3 = pickle.load(open('stripC.pkl','rb'))
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
R=Rational
f = R(29,4)*t**2-2*t
tot=0
for i in J:
    e = expand(cancel(J[i]/x**2))
    t0=time.time()
    pl = plan_biv(e, x, t, R(13,35), R(2,5), lambda a,b: R(175,416)*(f+R(27,875)), lambda a,b: R(9,35))
    nl=sum(len(uni_split(coeffs1(g,t),pc[0],pc[1])) for pc in pl for g in pc[5])
    tot+=nl
    print(i, [(float(p[0]),float(p[1]),p[4]) for p in pl], nl, round(time.time()-t0,1))
print(tot)
