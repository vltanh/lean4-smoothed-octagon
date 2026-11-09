from sympy import *
a,c,d,v = symbols('a c d v', positive=True)
K=a**2+4; T=a+c; W=c+d; Q=d**2+4; Y=W**2-T**2
x=d-a; e=4-d**2-2*c*d
U=lambda z:1-z+z**2
Sst=K/T
Ust=U(a*T/K)
Cast = (Sst-a)+a+c - a**2*(1/Sst+1/T) + a**3/K   # log term zero
print('Ca*', simplify(Cast - (4/T+4*c/K)))
Vch = 1 - Rational(1,2)*(a*c/T**2 + c*d/W**2)
hst = K/(16*a)*(Sst*Ust + T*Vch - Cast)
wUch = (K**2*Ust + 16*hst*Y + Vch*Y**2)/Q**2
r0 = Q/W - d
gd = lambda s: 1 - d*s/(d+s)**2
P0 = 2*a*T**5*x + 2*T**3*(5*a**2+3*a*c+2*c**2)*x**2 + 2*T**2*(9*a**2+5*a*c+2*c**2)*x**3 + T*(2*a+c)*(7*a+c)*x**4 + a*(4*a+3*c)*x**5
Pe = T*(2*a*T**3 + 2*T**3*x + 4*a*T**2*x + T**2*x**2 + 6*a*T*x**2 + 3*a*x**3)
lhs = Q**2*(wUch - gd(r0))
rhs = -c*x/(2*a*T**2*W**2)*(P0 + e*Pe)
print(simplify(lhs-rhs))
# coefficient of v in w_U(b*)
hv = K/(16*a)*(Sst*Ust + T*v - Cast)
wv = (K**2*Ust + 16*hv*Y + v*Y**2)/Q**2
print(factor(diff(wv,v) - Y*(K*T/a+Y)/Q**2))
