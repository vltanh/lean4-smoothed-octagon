from model import *
import numpy as np, pickle
R_=sp.Rational
u_=15*(t-R_(1,3)); y_=q-1
alpha = R_(27,4)-3*u_-24*y_+16*(2*t+x-1)
Mm = R_(1,4)-u_+6*y_+24*(2*t+x-1)
def G(kk, al, MM): return comb(al, MM, kk, VG, Lp, Fl(q))
jobs = {
 'lgA1': (G(1, alpha, Mm), (R_(1,4),R_(1,3))),        # h range for t in [1/3,3/8]
 'lgA2': (G(2*t+x, alpha, Mm), (R_(1,4),R_(1,3))),
 'lgB1': (G(R_(29,4)*t**2, 4, 1), (R_(1,5),R_(1,4))),
 'lgB2': (G(2*t+x, 4, 1), (R_(1,5),R_(1,4))),
}
for name,(Gx,(hl,hh)) in jobs.items():
    P = sp.factor(sp.together(48*(q+1)*W*R*Gx))
    num,den = sp.fraction(P)
    print(name,'den',den)
    Ps = sp.expand(num.subs({t:(1-h)/2, x:h+j}))
    pickle.dump(Ps, open(f'{name}.pkl','wb'))
    f = sp.lambdify((h,j,q), Ps, 'numpy')
    H,A,Z = np.meshgrid(np.linspace(float(hl),float(hh),25), np.linspace(0,1,25), np.linspace(0,1,25), indexing='ij')
    Jv = R_(1,30)+A*(5*H/7-R_(1,30)); Jv=Jv.astype(float); Qv = 1+Z*(H-Jv)/(1+2*Jv)
    vals = f(H,Jv,Qv)
    print(name,'min',vals.min(),'max',vals.max(),'deg',[sp.degree(Ps,h),sp.degree(Ps,j),sp.degree(Ps,q)])
