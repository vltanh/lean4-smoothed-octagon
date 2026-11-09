from common import *
import pickle, numpy as np
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
fs = {i: lambdify((t,x), J[i]/x**2, 'numpy') for i in J}
# domain D1 in (x,s): t=(1-x-s)/2
X_,S_ = np.meshgrid(np.linspace(0.0,1,2001), np.linspace(0,1,2001))
T_ = (1-X_-S_)/2
dom = (T_>0)&(T_<=13/35)&(S_>=0)&(2*T_+2*X_+X_**2>1)
for i in fs:
    val = fs[i](T_,X_)
    m = val[dom].min()
    j = np.argmin(np.where(dom,val,np.inf))
    print(i, m, X_.flat[j], S_.flat[j], T_.flat[j])
