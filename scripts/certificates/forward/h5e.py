import sympy as sp
U,z,h=sp.symbols('U z h',positive=True)
S=1+z;K=1+U;Z=z**2+U;x=z/S;q=S*S/K;d=S**2/Z-1;e=h-1
lam=(U-z)/S; v=S*(h-1)/h; m=(2*z+1-U)/S
D0=x*(x-sp.Rational(1,2))*d+x*d**2/(3*(d+2))
Db=z*m*(3*(z-1)+m)/(6*S*Z)
Bp=e*(S*K/Z)*x*(q-1)*(q/S-x)/q-(K**2/(S*Z))*(q-1+e*(S*q-1))*Db+z**2*d*e**2/(2*h)-z*e*(e/h)**2/6
P=(z+lam)**2*v**3-3*z*(1-lam)*S*(z+lam)*v**2+((1+lam)*(1-lam)*S*z*(3*(z-1)+(1-lam))-6*(z+lam)*(z-lam)*(1-z*lam))*v+(1+lam)*(1-lam)*S*(3*(z-1)+(1-lam))*(z-lam)
print(sp.simplify(Bp + z*h*P/(6*S*Z**2)))
print(sp.simplify(D0-Db - z*m**3/(6*S*Z*(2*S-m))))
