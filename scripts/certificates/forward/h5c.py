import sympy as sp, pickle
from leangen2 import bern_coeffs2
from fractions import Fraction as Fr
m,v,mu=sp.symbols('m v mu')
R3=3*((2-m**2)*v+m*(2-m-v**2))
E_=4*m**4+28*m**2*(1-m)+24*m
R2=(2-m)*v**3-3*m*(m**2-m+10)*v**2+(m**4-13*m**3-14*m**2+24*m+24)*v+E_
C_=m**2*(-m**4+14*m**3-40*m**2-48*m+160)
R1=2*(2-m)*(m**2-2*m+4)*v**3-3*m*(m**3+4*m**2-4*m+32)*v**2+m*(7*m**4-46*m**3+40*m**2-96*m+144)*v+C_
R0=(2-m)*(m**2-2*m+4)**2*v**3-12*m*(m**3+8)*v**2+2*m**2*(3*m**4-16*m**3+20*m**2-56*m+64)*v+4*m**3*(2-m)*(4-m)*(8-m)
out={}
for name,R,k in [('R0',R0,3),('R1',R1,2),('R2',R2,1),('R3',R3,1)]:
    Rt=sp.expand(sp.cancel(R.subs(m,mu*v)/v**k))
    print(name,'poly?',sp.Poly(Rt,mu,v).degree_list())
    C,a,b=bern_coeffs2(Rt,mu,v,((0,1),(0,1)))
    print('  min bern',float(min(min(r) for r in C)))
    out[name]=(Rt,k)
pickle.dump(out,open('H5R.pkl','wb'))
