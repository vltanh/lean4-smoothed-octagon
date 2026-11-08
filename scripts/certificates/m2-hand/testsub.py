from common import *
from bern import *
import pickle
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
import time
for i in J:
    e = expand(cancel(J[i].subs(t,(1-x-s)/2)/x**2))
    cons = [(1-x-s, True), (x+x**2-s, True), (s-Rational(9,35)+x, False)]  # t>0, centre gap, t<=13/35
    t0=time.time()
    tree, st = subdivide(e, [x,s], [(Fr(3,25),Fr(1)),(Fr(0),Fr(1))], cons)
    print(i, st, time.time()-t0)
