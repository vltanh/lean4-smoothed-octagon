from sympy import *
import numpy as np, pickle
t,x = symbols('t x')
C0,C1,C2,C3 = pickle.load(open('highTC.pkl','rb'))
T_,X_ = np.meshgrid(np.linspace(0.4,0.5,401), np.linspace(0.12,1/3,401))
Tx = (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
dom = (20/3*T_**2 < 2*T_+2*X_+X_**2) & (T_ < Tx)
for name,e in [('C0',C0),('C1',C1),('C2',C2),('C3',C3),('disc',4*C1*C3-C2**2)]:
    f = lambdify((t,x), e, 'numpy')
    val = f(T_,X_)
    j = np.argmin(np.where(dom,val,np.inf)); k2=np.argmax(np.where(dom,val,-np.inf))
    print(name, val[dom].min(), T_.flat[j], X_.flat[j], 'max', val[dom].max())
