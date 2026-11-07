#!/usr/bin/env python3
"""Exact same-lift midpoint and outer-endpoint stationary-slack identities.

This is algebraic verification, not an M2 positivity or closure assertion.
No Lean, Lake, typechecking, CI or sampled sign decision.
"""
import sympy as s
x,alpha,beta,rho,u,v,E=s.symbols('x alpha beta rho u v E')
S=1+x;A=alpha+beta;B=beta+x;U=(1-rho)/rho
n=(U-x)/S;z1=(U-beta*x)/B;z2=(U-alpha*beta)/A
P=s.Matrix([[-n-2,x+2],[n,x]])
Q1=s.Matrix([[-z1-2*beta,x+2*beta],[z1,x]])
Q2=s.Matrix([[-z2-2*beta,alpha+2*beta],[z2,alpha]])
F1=s.Matrix([[S/B,0],[S/B-B/S,B/S]])
F2=s.Matrix([[S/A,0],[(S*S-B*B)/(S*A),A/S]])
h11=E*(1/S-rho*S)-u*(1-rho*rho*S*S)+v*(1-1/(S*S))
h12=u*(1+rho*S)**2+v*(1+1/S)**2-E*(1+1/S)*(1+rho*S)
h21=-u*(1-rho*S)**2-v*(1-1/S)**2-E*(1-1/S)*(1-rho*S)
H=s.Matrix([[h11,h12],[h21,-h11]]);R=s.diag(1,-1)
L0=-R*H*R/(2*(1-rho)**2);J0=s.Matrix([[0,-1],[s.Rational(1,3),0]])
Hada=s.Matrix([[1,1],[1,-1]])
def inv2(m):return s.Matrix([[m[1,1],-m[0,1]],[-m[1,0],m[0,0]]])
def scaledslack(Q,F):
 m=(P*F*Q.inv()).applyfunc(s.factor);xx=Q*Hada/4
 return s.factor(-s.Rational(3,2)*s.trace(J0*xx)-s.trace(inv2(m)*L0*m*xx))
mid=scaledslack(Q1,F1)
pol=beta*beta*rho*x*x-beta*beta*rho+beta*beta-4*beta*rho*x*x-4*beta*rho*x+2*beta*x+3*rho*x*x+4*rho*x+rho+x*x
N=(1-rho)*(beta*beta*rho+beta*rho*x+rho*x*x-rho+1)-v-rho*E*(beta*x-2*x-1)-rho*u*pol
assert s.factor(mid-N/(2*rho*B*(1-rho)))==0
print('MIDPOINT EXACT PASS',flush=True)
outer=scaledslack(Q2,F2)
zeta=1+rho*(alpha*alpha-1);D=A*A+S*S-B*B
rhoA=rho*alpha*alpha/zeta;rA=alpha/A
w=(v+rho*rho*D*D*u-rho*D*E)/(zeta*zeta);EL=(2*rho*D*u-E)/zeta
HA=(1-rhoA-w)*rA*rA+rhoA*(EL-1+rhoA)*rA+rhoA*(1-rhoA-u)
assert s.factor(outer-A*zeta*zeta/(2*rho*alpha*alpha*(1-rho))*HA)==0
print('OUTER EXACT PASS',flush=True)
