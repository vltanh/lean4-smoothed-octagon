from sympy import *
from gen import *
import pickle, time
t,x = symbols('t x')
res = pickle.load(open('lowQ.pkl','rb'))
def Jl(P):
    P0,P1,P2,P3,P4 = P
    return {0:P0, 1:P1+2*P0, 2:P2+48*P0, 3:P3+4*P2, 4:P3-P0, 5:P4-P0}
R=Rational
Tn = lambda xx: (-2*xx**3-xx**2+10*xx+12)/(3*(xx+2)**3)
for face in ['unit','kh']:
    J = Jl(res[face])
    for i in J:
        e = expand(J[i])
        t0=time.time()
        print(face, i, 'deg t', Poly(e,t).degree(), 'deg x', Poly(e,x).degree())
        if face=='unit':
            p1 = plan_biv(e, t, x, R(1,2), Integer(1), lambda a,b: (1-x)/2, lambda a,b: R(1,4))
            p2 = plan_biv(e, t, x, Integer(1), R(7,3), lambda a,b: Integer(0), lambda a,b: Tn(a))
            pl = p1+p2
        else:
            pl = plan_biv(e, t, x, R(1,2), Integer(1), lambda a,b: R(1,4), lambda a,b: R(7,20))
        nl=sum(len(uni_split(coeffs1(g,x),pc[0],pc[1])) for pc in pl for g in pc[5])
        print('   pieces', [(round(float(p[0]),3),round(float(p[1]),3),p[4]) for p in pl], 'leaves', nl, round(time.time()-t0,1))
