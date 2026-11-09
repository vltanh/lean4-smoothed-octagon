from model import *
from qe import Cs
import pickle, numpy as np
R_=sp.Rational
A_,J_,Z_ = sp.symbols('A J Z')
Qq = x**2+6*x+6
B1 = 1+2*t*x+x**2
Dd = t*p*W**2*Qq*B1
C0,C1,C2 = Cs(1, Vq)
DC = [sp.factor(sp.together(Dd*Ci)) for Ci in (C0,C1,C2)]
for i,dc in enumerate(DC):
    n,d = sp.fraction(dc); print(i, 'den', d)
DC = [sp.expand(sp.fraction(dc)[0]/sp.fraction(dc)[1]) for dc in DC]
Delta = sp.expand(4*DC[0]*DC[2] - DC[1]**2)
sub = {t: R_(2,5)-A_, x: R_(1,5)+2*A_+J_}
Dh = sp.expand(Delta.subs(sub)); C2h = sp.expand(DC[2].subs(sub))
pickle.dump(Dh, open('QDelta.pkl','wb')); pickle.dump(C2h, open('QC2.pkl','wb')); pickle.dump(DC, open('QDC.pkl','wb'))
for name,Pz in [('Delta',Dh),('C2',C2h)]:
    f = sp.lambdify((A_,J_), Pz, 'numpy')
    a,b = np.meshgrid(np.linspace(0,1/15,60), np.linspace(0,1/30,60), indexing='ij')
    vals=f(a,b); print(name, vals.min(), vals.max(), [sp.degree(Pz,A_),sp.degree(Pz,J_)])
