import sympy as sp
z,lam,v,m=sp.symbols('z lam v m',positive=True)
S=1+z; U=z+lam*S; K=1+U; Z=z**2+U
q=S**2/K; H=S**2/Z; d=H-1; x=z/S
s=1-v
h=S/(z+s); e=h-1; t=e/h
Delta0=x*(x-sp.Rational(1,2))*d+x*d**2/(3*(d+2))
Bcal=e*S*K/Z*x*(q-1)*(q/S-x)/q - K**2/(S*Z)*(q-1+e*(S*q-1))*Delta0 + z**2*d*e**2/(2*h) - z*e**3/(3*h*(h+1))
mm=1-lam
Dbar=z*mm*(3*(z-1)+mm)/(6*S**2*(z+lam))
print('Delta0 exact form', sp.simplify(Delta0 - z*mm/(S**2*(z+lam))*((z-1)/2+S*mm/(3*(2*S-mm)))))
Bp=e*S*K/Z*x*(q-1)*(q/S-x)/q - K**2/(S*Z)*(q-1+e*(S*q-1))*Dbar + z**2*d*e**2/(2*h) - z*e*t**2/6
P=(z+lam)**2*v**3-3*z*mm*S*(z+lam)*v**2+((1+lam)*mm*S*z*(3*(z-1)+mm)-6*(z+lam)*(z-lam)*(1-z*lam))*v+(1+lam)*mm*S*(3*(z-1)+mm)*(z-lam)
print('B prime identity', sp.simplify(Bp + z*P/(6*S**2*(z+lam)**2*(S-v))))
print('e/h = v/S', sp.simplify(t - v/S), ' e=', sp.simplify(e - v/(S-v)))
print('coef (q-1+e(Sq-1))/e', sp.simplify((q-1+e*(S*q-1))/e - ((q-1)/t+q*z)))
# P in m: substitute lam=1-m and p=(2-m)z-(2+m)
p_=sp.symbols('p')
Pm=sp.expand(P.subs(lam,1-m))
zsub=(p_+2+m)/(2-m)
lhs=sp.expand(sp.simplify((2-m)**3*Pm.subs(z,zsub)))
R3=3*((2-m**2)*v+m*(2-m-v**2))
E_=4*m**4+28*m**2*(1-m)+24*m
R2=(2-m)*v**3-3*m*(m**2-m+10)*v**2+(m**4-13*m**3-14*m**2+24*m+24)*v+E_
C_=m**2*(-m**4+14*m**3-40*m**2-48*m+160)
R1=2*(2-m)*(m**2-2*m+4)*v**3-3*m*(m**3+4*m**2-4*m+32)*v**2+m*(7*m**4-46*m**3+40*m**2-96*m+144)*v+C_
R0=(2-m)*(m**2-2*m+4)**2*v**3-12*m*(m**3+8)*v**2+2*m**2*(3*m**4-16*m**3+20*m**2-56*m+64)*v+4*m**3*(2-m)*(4-m)*(8-m)
print('(11) check', sp.expand(lhs-(R0+R1*p_+R2*p_**2+R3*p_**3)))
