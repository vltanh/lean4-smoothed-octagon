#!/usr/bin/env python3
"""Exact algebra for the smaller-turn finite continuation alternative.

This checks identities, not the still-open two-branch scalar exclusion.
No Lean, Lake, typechecking, numerical optimizer, or sampled signs.
"""
import sympy as s


def zero(expr):
    assert s.factor(expr) == 0, s.factor(expr)


a, b, c, d, r, u, v, h = s.symbols("a b c d r u v h", positive=True)
K, S, T = a*a+4, a+b, a+c
Q, W, Z = d*d+4, c+d, d+r
Y = W*W-T*T
Ua = s.Matrix([[h, -K*K*v/(8*S*S)], [S*S*u/8, -h]])
q0 = K/(S*T)
qc = W/T
D2 = s.Matrix([[1, 0], [2, -1]])
F = s.diag(q0, 1/q0) * ((qc+1/qc)*s.eye(2)+(1/qc-qc)*D2)/2
hd = h+v*Y/8
w = (u*K*K+16*h*Y+v*Y*Y)/(Q*Q)
Ud = s.Matrix([[hd, -W*W*v/8], [Q*Q*w/(8*W*W), -hd]])
for entry in F.inv()*Ua*F-Ud:
    zero(entry)
zero(Ud.det()-Ua.det())

q = W*Z/Q
rot = s.Matrix([[1, -1], [1, 0]])
diag = s.diag(q, 1/q)
Kr = r*r+4
hr = -hd+w*Z*Z/8
t = (Q*Q*v-16*hd*Z*Z+w*Z**4)/(Kr*Kr)
Ur = s.Matrix([[hr, -Z*Z*w/8], [Kr*Kr*t/(8*Z*Z), -hr]])
for entry in rot.inv()*diag.inv()*Ud*diag*rot-Ur:
    zero(entry)
zero(Ur.det()-Ua.det())

hu = K*S/(16*a)
wu = (K*K+16*hu*Y)/(Q*Q)
Ru = 16*d*hu/Q-Z*wu
zero(Ru-K*(d*S*Q-Z*(a*K+S*Y))/(a*Q*Q))
zero(S*(d*W-Y)-a*K-(a*(S*T-K)+S*c*(a-d)))

Cd = c+d+r-d*d*(1/W+1/Z)+d**3/Q-d*s.log(W*Z/Q)
zero(s.diff(Cd, r)-(1-d*r/Z**2))
zero(s.diff(u*v*K*K/64-(hu*u+h)**2, u)
     -(v*K*K/64-2*hu*(hu*u+h)))
zero(Y*Ru-wu*(d*Q-Z*Y)+d*K*K/Q)

# Central zero-factor boundary: no assertion that the Casimir is preserved
# by the scalar change of b.  The displayed identity is modulo R_d=0.
Hs = W*W-c*T
Ds = Z*Hs-d*Q
L0 = a*a+a*c+c*c+4
P = a*d*(c*c+4)+d*d*(4-c*d)+2*c*d*(6-c*d)+4*c*c
zero(d*(Hs*Hs+4*T*T)-Hs*Q*W+(d-a)*P)
hb = K*((K/T)*u+T*v-(4/T+4*c/K))/(16*a)
wb = (u*K*K+16*hb*Y+v*Y*Y)/(Q*Q)
Rb = Cd-W*v-Z*wb+16*d*(hb+v*Y/8)/Q
zero(Q*Ds*wb-(Hs*Q*Cd-(d-a)*P*v-4*d*L0)+Hs*Q*Rb)

x = s.symbols("x")
g = lambda z: 1-c*z/(c+z)**2
chord = ((d-x)*g(a)+(x-a)*g(d))/(d-a)
chord_gap = c*(x-a)*(d-x)*(c*c*(a+d+2*c)+(c*c-a*d)*x) \
    / ((a+c)**2*(d+c)**2*(x+c)**2)
zero(chord-g(x)-chord_gap)
print("PASS: central/turn and next-forward transports preserve the Casimir")
print("PASS: first-root coefficient, comparison numerator, and r derivative")
print("PASS: boundary comparison, negative norm coefficient, and turn chord")
