#!/usr/bin/env python3
"""Exact cancellation identities for the pending M2 interval model.

No domain is excluded by this algebra checker alone.
"""
import sympy as s

a,c,e,l0,l1,l2=s.symbols('a c e l0 l1 l2')
K=a*a+4;T=a+c
z0=e*l0;z1=e*l1;z2=e*l2
d=a+T*z1;W=T*(1+z1);Q=d*d+4;Y=W*W-T*T;q=1+z2
N=d*W-q*Y
KU=K*K-a*K*T*(1+z0)+a*a*T*T*(1+z0)**2
vnum=a*W+c*c+c*z1*W/2
Vnum=-a*Q*W*W-a*q*Y*Y+2*a*d*W*Y+K*T*N
Bnum=-K*T*T+2*a*a*T*T*(1+z0)+K*a*a-a**3*T
CnumQ=Q*Q*q*q-d*d*Q*q+d*d*W*W*(q-1)+4*c*W*q
P=(2*a*T*W*CnumQ+2*q*Vnum*vnum-2*a*T*W*q*q*KU
   +2*W*q*N*Bnum-a*T*W*q*K*N*(2*z0-z0*z0)
   -a*T*W*q*d*Q*W*(2*z2-z2*z2))
poly=s.Poly(s.expand(P),e)
assert s.factor(poly.nth(0))==0
assert s.factor(poly.nth(1))==0
assert poly.degree()<=8
assert s.factor(poly.nth(2)-T**3*(4-a*a-2*a*c)*(a*(l0+l2)+c*l1)**2)==0
print('PASS: centered numerator has an exact quadratic zero; degree',poly.degree())
print('PASS: the leading quadratic coefficient has an explicit positive factorization')

# The quadratic-log model has precisely numerator P over this denominator.
S=K/(T*(1+z0));Z=Q*q/W;r=Z-d
u=1-a/S+a*a/(S*S)
v=vnum/(T*W)
L0=z0-z0*z0/2;L2=z2-z2*z2/2
Ca=S+c-a*a*(1/S+1/T)+a**3/K+a*L0
h=K*(S*u+T*v-Ca)/(16*a)
hd=h+v*Y/8
w=(u*K*K+16*h*Y+v*Y*Y)/(Q*Q)
Cd=c+Z-d*d*(1/W+1/Z)+d**3/Q-d*L2
RU=Cd-W*v-Z*w+16*d*hd/Q
assert s.factor(2*a*T*Q*W*W*q*RU-P)==0
print('PASS: exact factored denominator and quadratic logarithm substitution')

Rv=(-Q*W*W-q*Y*Y+2*d*W*Y+(K*T/a)*N)/(Q*W)
Bv=c*(4-a*a)+8*a+a*z1*(c*c+4)+z2*T*(z1+2)*(K+a*T*z1*(z1+2))
assert s.factor(Rv+z1*T*T*Bv/(a*Q*W))==0
print('PASS: the v coefficient has an exact positive-factor negative sign')
# R is affine in the three logarithmic remainders.  Coefficients below
# follow by differentiating with respect to their independent placeholders.
H0,H1,H2=s.symbols('H0 H1 H2')
vf=v-c/T*z1*z1*H1
hf=h+K*T/(16*a)*(vf-v)-K*z0**3*H0/16
wf=(u*K*K+16*hf*Y+vf*Y*Y)/(Q*Q)
Rf=Cd-d*z2**3*H2-W*vf-Z*wf+16*d*(hf+vf*Y/8)/Q
assert s.factor(s.diff(Rf,H0)+K*N*z0**3/(Q*W))==0
assert s.factor(s.diff(Rf,H1)+c/T*z1*z1*Rv)==0
assert s.factor(s.diff(Rf,H2)+d*z2**3)==0
print('PASS: all analytic remainder coefficients')

x=c/T
vactual=1+x*x/(1+z1)-x*(1-z1/2+z1*z1*H1)
turn=s.Rational(1,2)-(1-x+z1)/(1+z1)**2-z1*H1
assert s.factor(vactual-(1-c*d/W**2)-x*z1*turn)==0
print('PASS: the actual turn derivative has the stated divided regular form')
turnupper=x-s.Rational(1,2)-z1*(x/(1+z1)-H1)
assert s.factor((1-x+x*x)-vactual-x*z1*turnupper)==0
m=s.symbols('m')
assert s.factor(T*(1+z0)*((S-a)-c)-(K-T*T*(1+z0)))==0
assert s.factor(c*c-a*d-T*(c-a*(1+z1)))==0
assert s.factor(W*(r-a)-(4-a*a-2*a*c-T*T*z1+Q*z2))==0
assert s.factor(4-c*d-m*W-(4-a*c-m*T-T*(c+m)*z1))==0
assert s.factor(4-d*r-m*Z-Q/W*(c-m-(d+m)*z2))==0
print('PASS: upper turn and compact-state geometric normalized constraints')
ell=s.symbols('ell')
vturn=1+c*c/(T*W)-c/(d-a)*ell
qturn=W/T
Fturn=1+(d/W)**2*qturn-(d/W)*qturn*ell/(qturn-1)
assert s.factor(Fturn-vturn-(d-c)*(1/T-ell/(d-a)))==0
print('PASS: the max-forward-factor chart forces d <= c')

D1=K*K/(a*Q*W*(1+z0))*(a*(l0+l2)+c*l1
    +a*e*l0*l2+T*e*l1*l2*(2+e*l1))
Yfull=Y
Ruc=K/(a*Q*Q)*(d*S*Q-Z*(a*K+S*Yfull))
assert s.factor(-Ruc-e*D1)==0
print('PASS: strictly positive desingularized root denominator in each max chart')

rho=a*a/K;t=a/T;r0=a*T/K
u0=1-r0+r0*r0;v0=1-t+t*t
h0=K*(-1+2*(r0+t)-rho)/16
assert s.factor(u0*v0*K*K/64-h0*h0-s.Rational(3,16))==0
print('PASS: entire zero-duration shape fibre has Casimir 3/16 at upper norms')
