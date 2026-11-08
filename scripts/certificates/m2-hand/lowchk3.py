from sympy import *
import numpy as np, pickle
t,x = symbols('t x')
res = pickle.load(open('lowQ.pkl','rb'))
def Jl(P):
    P0,P1,P2,P3,P4 = P
    return {0:P0, 1:P1+2*P0, 2:P2+48*P0, 3:P3+4*P2, 4:P3-P0, 5:P4-P0}
Tx = lambda X_: (-2*X_**3-X_**2+10*X_+12)/(3*(X_+2)**3)
T1,X1 = np.meshgrid(np.linspace(0,0.25,301), np.linspace(0.5,7/3,601))
J = Jl(res['unit'])
for i in J:
    f = lambdify((t,x), J[i], 'numpy')
    val = f(T1,X1)
    neg = val<0
    if neg.any():
        print('J',i,'neg at x>=', X1[neg].min(), 'min', val.min())
        # largest t allowed where negative region begins as function of x
        for xx in [1.0,1.2,1.5,1.8,2.0,2.33]:
            row = f(np.linspace(0,0.25,2001), xx)
            ts = np.linspace(0,0.25,2001)[row<0]
            print('   x',xx,'neg from t=', ts.min() if len(ts) else None, 'T(x)=',Tx(xx))
    else:
        print('J',i,'pos on rectangle, min', val.min())
