from common import *
from gen import *
import pickle, time
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
R=Rational
pieces = [(R(3,25),R(9,35), lambda a,b: R(9,35)-x, lambda a,b: x+x**2),
          (R(9,35),R(2,5), lambda a,b: Integer(0), lambda a,b: x+x**2),
          (R(2,5),Integer(1), lambda a,b: Integer(0), lambda a,b: 1-x)]
tot=0
for i in J:
    e = expand(cancel(J[i].subs(t,(1-x-s)/2)/x**2))
    for (lo,hi,S0f,S1f) in pieces:
        t0=time.time()
        pl = plan_biv(e, s, x, lo, hi, S0f, S1f)
        nl = 0
        for pc in pl:
            for g in pc[5]:
                nl += len(uni_split(coeffs1(g,x), pc[0], pc[1]))
        tot += nl
        print(i, float(lo), float(hi), 'pieces', len(pl), 'degs', [pc[4] for pc in pl], 'leaves', nl, round(time.time()-t0,1))
print('total leaves', tot)
