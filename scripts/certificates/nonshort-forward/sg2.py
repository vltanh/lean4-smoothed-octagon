from model import *
from qe import alq, beq, wU_, eta
import pickle, numpy as np
R_=sp.Rational
A_,J_,Z_ = sp.symbols('A J Z')
Qq = x**2+6*x+6
gg = 1 - c*p/W**2
def h1(kk, vv): return (W*vv - c + p**2/W)/p + alq(kk,vv) + beq(kk) - p**2/Bk(kk)
def Nv(kk, vv):
    B=Bk(kk)
    return B**2*(4*vv*wU_(kk,vv) - (h1(kk,vv)+vv-gg)**2)
vs = sp.Symbol('vs')
Nfun = Nv(k, vs)
dN = sp.diff(Nfun, vs)
E = sp.together(2*t**2*p**2*W**3*(-dN.subs(vs, R_(3,4))))
En, Ed = sp.fraction(sp.factor(E))
print('E den', Ed)
cap = R_(9193,50000)
Pp = sp.together(3125*t**2*p**2*W**4*Qq**2*(Nfun.subs(vs, Vq) - 16*(k-t**2)**2*cap))
Pn, Pd = sp.fraction(sp.factor(Pp))
print('P den', Pd)
sub = {t: R_(2,5)-A_, x: R_(1,5)+2*A_+J_, k: 1+Z_}
Ehat = sp.expand(En.subs(sub)/Ed.subs(sub)) if Ed!=1 else sp.expand(En.subs(sub))
Phat = sp.expand(Pn.subs(sub)/Pd.subs(sub)) if Pd!=1 else sp.expand(Pn.subs(sub))
pickle.dump(Ehat, open('Ehat.pkl','wb')); pickle.dump(Phat, open('Phat.pkl','wb'))
for name, Pz in [('E',Ehat),('P',Phat)]:
    f = sp.lambdify((A_,J_,Z_), Pz, 'numpy')
    a,b,cc = np.meshgrid(np.linspace(0,1/15,20), np.linspace(0,1/30,20), np.linspace(0,1/30,20), indexing='ij')
    vals=f(a,b,cc); print(name, vals.min(), vals.max(), [sp.degree(Pz,A_),sp.degree(Pz,J_),sp.degree(Pz,Z_)])
