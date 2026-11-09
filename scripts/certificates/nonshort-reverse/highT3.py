from sympy import *
import numpy as np, pickle
t,x = symbols('t x')
C = pickle.load(open('highTC.pkl','rb'))
fs = [lambdify((t,x), c, 'numpy') for c in C]
T_,X_ = np.meshgrid(np.linspace(0.4,0.5,301), np.linspace(0.12,1/3,301))
Tx = (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
dom = (20/3*T_**2 < 2*T_+2*X_+X_**2) & (T_ < Tx)
cs = [f(T_,X_) for f in fs]
best = np.inf
for y in np.linspace(0,3,601):
    P = cs[0]+cs[1]*y+cs[2]*y**2+cs[3]*y**3
    m = P[dom].min()
    if m < best: best=m; arg=(y, T_.flat[np.argmin(np.where(dom,P,np.inf))], X_.flat[np.argmin(np.where(dom,P,np.inf))])
print(best, arg)
