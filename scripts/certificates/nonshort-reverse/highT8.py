from sympy import *
import numpy as np, pickle
t,x = symbols('t x')
C = pickle.load(open('highT7C.pkl','rb'))
fs = [lambdify((t,x), c, 'numpy') for c in C]
for (a,b) in [(1/7,1/5),(1/5,1/4),(1/4,3/10),(3/10,1/3),(1/5,3/10)]:
    T_,X_ = np.meshgrid(np.linspace(0.4,0.5,201), np.linspace(a,b,201))
    c1=fs[1](T_,X_).min(); c2=fs[2](T_,X_).min(); c3=fs[3](T_,X_).min()
    print((round(a,4),round(b,4)), 'C1>=',c1,'C2>=',c2,'C3>=',c3, '4bc-M^2', 4*c1*c3 - min(c2,0)**2)
print()
for (a,b) in [(0.3,0.31),(0.31,0.32),(0.32,1/3),(0.3,0.315),(0.315,1/3),(0.2,0.25),(0.25,0.3)]:
    T_,X_ = np.meshgrid(np.linspace(0.4,0.5,201), np.linspace(a,b,201))
    c1=fs[1](T_,X_).min(); c2=fs[2](T_,X_).min(); c3=fs[3](T_,X_).min()
    print((round(a,4),round(b,4)), 'C1>=',c1,'C2>=',c2,'C3>=',c3, '4bc-M^2', 4*c1*c3 - min(c2,0)**2)
