from sympy import *
from gen import *
import pickle
h,s = symbols('h s')
P = pickle.load(open('ofaceP.pkl','rb'))
R=Rational
for (lo,hi,S0f,S1f) in [(R(1,5),R(1,4),lambda a,b: R(1,4)-h, lambda a,b: R(4,3)), (R(1,4),Integer(1),lambda a,b: Integer(0), lambda a,b: R(4,3))]:
    try:
        pl = plan_biv(P, s, h, lo, hi, S0f, S1f)
        print(float(lo), float(hi), [(float(p[0]),float(p[1]),p[4]) for p in pl])
    except Exception as e:
        print('fail', e)
