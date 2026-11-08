#!/usr/bin/env python3
"""Exact algebra for the general short-bridge endpoint interface.

This checks the stated identities, not a positivity theorem or M2 closure.
No Lean, Lake, typechecking, CI, optimizer or sampled sign assertion.
"""
import sympy as s


def zero(expression):
    assert s.simplify(s.factor(expression)) == 0


def matrix_zero(matrix):
    for entry in matrix:
        zero(entry)


x, alpha, beta, U = s.symbols('x alpha beta U', positive=True)
rho, u, v, kappa = s.symbols('rho u v kappa', positive=True)
E = s.symbols('E', real=True)
S, A, B = 1+x, alpha+beta, beta+x
n, z = (U-x)/S, (U-alpha*beta)/A
P = s.Matrix([[-n-2, x+2], [n, x]])
Q = s.Matrix([[-z-2*beta, alpha+2*beta], [z, alpha]])
F = s.Matrix([[S/A, 0], [(S*S-B*B)/(S*A), A/S]])
zero(P.det()+2*U)
zero(Q.det()+2*U)
zero(F.det()-1)
q1, q2 = B/S, B/A
F2 = s.Matrix([[1/q1, 0], [1/q1-q1, q1]])
F0 = s.diag(q2, 1/q2)
matrix_zero(F-F2*F0)

# The two secant identities eliminate the corresponding two logarithms.
log1 = (beta-1)/x*(1+x*x/(S*B)-u)
log2 = (x-alpha)/beta*(1+beta*beta/(A*B)-u)
cost1 = x*((beta-1)+(x*x+U)*(beta-1)/(S*B)-x*log1)
cost2 = beta*((x-alpha)+(beta*beta+U)*(x-alpha)/(A*B)-beta*log2)
zero(cost1-x*(beta-1)*(u+U/(S*B)))
zero(cost2-beta*(x-alpha)*(u+U/(A*B)))
zero((cost1+cost2)/U
     -(u*(2*beta*x-x-alpha*beta)/U+(beta*x-alpha)/(S*A)))

C = s.Matrix([[-1-1/S, 1+rho*S], [1-1/S, 1-rho*S]])
V = s.Matrix([[E, -2*v], [2*u, -E]])
h11 = E*(1/S-rho*S)-u*(1-rho*rho*S*S)+v*(1-1/(S*S))
h12 = u*(1+rho*S)**2+v*(1+1/S)**2-E*(1+1/S)*(1+rho*S)
h21 = -u*(1-rho*S)**2-v*(1-1/S)**2-E*(1-1/S)*(1-rho*S)
H = s.Matrix([[h11, h12], [h21, -h11]])
matrix_zero(H-(1-rho)*C*V*C.inv())

# Check the physical costate normalization before its reflection.
a = s.symbols('a', positive=True)
K = a*a+4
nb = (4-a*a*x)/(a*(1+x))
Pphys = s.Matrix([[-(a*x+2*a)/s.sqrt(3), (nb+2*a)/s.sqrt(3)],
                  [a*x, nb]])/2
Ub = s.Matrix([[K*E/16, -K*K*v/(8*a*a*S*S)],
               [a*a*S*S*u/8, -K*E/16]])
lam = s.sqrt(12)*Pphys*Ub*Pphys.inv()
D3 = s.diag(1/s.sqrt(3), 1)
claimed = s.sqrt(3)/(2*(1-rho)**2)*D3*H*D3.inv()
matrix_zero(lam-claimed.subs(rho, a*a/(a*a+4)))

# Missing-control sign at the initial central two-control tie.
Bphys = s.Matrix([[1/s.sqrt(3), 1/s.sqrt(3)], [1, -1]])
Xphys = Pphys*Bphys.inv()
Jphys = s.Matrix([[0, -1], [1, 0]])
slack = -s.Rational(3,2)*s.trace(Jphys*Xphys)-s.trace(lam*Xphys)
r0 = 1/S
hfilter = (1-rho-v)*r0*r0+rho*(E-1+rho)*r0+rho*(1-rho-u)
zero(slack-(s.sqrt(3)*K*a*S/(8*rho)*hfilter).subs(rho,a*a/K))

# The endpoint trace identity is bilinear in an arbitrary relative frame.
m11, m12, m21, m22 = s.symbols('m11 m12 m21 m22')
m = s.Matrix([[m11, m12], [m21, m22]])
M = D3*m*D3.inv()
R = s.diag(1, -1)
J = s.Matrix([[0, -1], [1, 0]])
lam_ref = -R*claimed*R
epA = s.trace((s.eye(2)+J*lam_ref/kappa)*M)
epB = s.trace((lam_ref/kappa-J)*M)
tk = 2*kappa*(1-rho)**2
A0 = tk*(m11+m22)+h12*m22-h11*(m12+3*m21)-3*h21*m11
B0 = h11*(m22-m11)+h12*m21+h21*m12+tk*(3*m21-m12)/3
zero(A0-tk*epA)
zero(s.sqrt(3)*B0-tk*epB)
zero(lam_ref.det()-3*(4*u*v-E*E)/(4*(1-rho)**2))

r, t = s.symbols('r t', positive=True)
Et = (u-1)/r+(v-1)/t+1+r+t-rho+s.log(rho/(r*t))
zero(s.diff(Et,t)-(1-t+t*t-v)/(t*t))
zero(Et.subs(t,rho/r)-((u-1)/r+(v-1)*r/rho+1+r+rho/r-rho))

Elo = (u-1)/r+(v-1)*r/rho+1+r+rho/r-rho
Hfilter = (1-rho-v)*r*r+rho*(E-1+rho)*r+rho*(1-rho-u)
zero(Hfilter-rho*r*(E-Elo))
t0 = rho/r
K0 = 1-v-t0
G = (u-1)/r+r-rho+t-K0/t
zero(s.diff(G,t)-(1+K0/t**2))
zero(G.subs(t,t0)-Elo)
zero(G.subs(t,r)-((u+v-2)/r+2*r-rho+rho/r**2))
assert s.Rational(9,4)-s.Rational(23,16)**2 == s.Rational(47,256)

# Rational constants in the compact six-variable reduction.
assert s.Rational(13,4)-16*s.Rational(17,20)**2*s.Rational(27,256) == s.Rational(12997,6400)
assert s.Rational(12997,6400) < s.Rational(23,16)**2
assert 48*s.Rational(1,10)**2+23*s.Rational(1,10)-3 == -s.Rational(11,50)
assert s.Rational(675,17) < s.Rational(631,100)**2 < s.Rational(19,3)**2
assert 9*(7*s.Rational(19,3)+18)/25 == s.Rational(561,25) < s.Rational(45,2)
zero(s.diff(x*(7*alpha+2*x)/(7+2*x),x)-(49*alpha+28*x+4*x*x)/(7+2*x)**2)

print('PASS: exact short-bridge cost, transfer, costate, endpoint and opposite-turn identities.')
print('No positivity or M2 completion is asserted by this algebra checker.')
