from model import *
import numpy as np, pickle
R_=sp.Rational
rho = R_(3,4)*(q+2*t+x-1)
vhat = VG + rho*(VG-Fl(q))
def Ghat(kk): return comb(6,0,kk,vhat,Lp,0)
for name,kk in [('k1',1),('ko',2*t+x)]:
    P = sp.factor(sp.together(48*(q+1)*W*R*Ghat(kk)))
    num,den = sp.fraction(P)
    print(name, 'den', den)
    Ps = sp.expand(num.subs({t:(1-h)/2, x:h+j}))
    pickle.dump(Ps, open(f'lr_{name}.pkl','wb'))
    f = sp.lambdify((h,j,q), Ps, 'numpy')
    H,A,Z = np.meshgrid(np.linspace(1/3,1/2,25), np.linspace(0,1,25), np.linspace(0,1,25), indexing='ij')
    Jv = A*H; Qv = 1+Z*(H-Jv)/(1+2*Jv)
    vals = f(H,Jv,Qv)
    print(name,'min (actual q-range)',vals.min())
    Qv2 = 1+Z*H
    print(name,'min (enlarged q=1+hz)', f(H,Jv,Qv2).min())
    print('degrees', sp.Poly(Ps,h,j,q).degree_list() if False else [sp.degree(Ps,h),sp.degree(Ps,j),sp.degree(Ps,q)])
