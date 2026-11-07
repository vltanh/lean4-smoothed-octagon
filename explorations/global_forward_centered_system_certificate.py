"""Exact centered F identities and broad-corner rational inequalities.

All domain, same-PMP-lift and whole-period implications are stated in
GLOBAL_FORWARD_CENTERED_SYSTEM.md. This does not close the complementary
F domain. No Lean, Lake, typechecking, CI, sampling or floating signs.
"""
from fractions import Fraction as Q
import sympy as s


def zero(name, expression):
    expression = expression.replace(
        lambda e: e.func == s.log,
        lambda e: s.expand_log(s.log(s.factor(e.args[0])), force=True))
    assert s.factor(expression) == 0, name
    print("PASS", name)


U, z, w, h, k = s.symbols("U z w h k", positive=True)
S, T, K, Z, W = 1+z, 1+w, 1+U, z*z+U, w*w+U
q = S*T/K
d, x, y, H, I = 3-U, z-1, w-1, h-1, k-1
f = lambda r: (r-1/r)/2-s.log(r)
Phi = f(S/2)+f(T/2)+f(4/K)
e0 = 1-K/8+1/K
A = 1+z+w-1/S-1/T+1/K-s.log(q)
B = Z*h/S+1-z*z*S/(Z*h)-z*z/S+z**3/Z-z*s.log(h)
C = W*k/T+1-w*w*T/(W*k)-w*w/T+w**3/W-w*s.log(k)
aL, aR = K*(h*S-z)/Z, K*(k*T-w)/W
nL, nR = S*S*(U-z)*H/Z, T*T*(U-w)*I/W
mL = K*K*(q-1+H*(q*S-1))/(S*Z)
mR = K*K*(q-1+I*(q*T-1))/(T*W)
RL, RR = aL*A-B, aR*A-C
rL, rR = RL-s.Rational(3,4)*(nL+mL), RR-s.Rational(3,4)*(mR+nR)
pol = lambda d,x: d*d*(x*x+4*x+2)+8*d*x*(x+1)+2*x*x*(8+4*x-x*x)
centerL = (d*x*(d+2*x)+H*pol(d,x))/(8*S*Z) + H*H*z*(d+4*x+x*x)/(2*h*Z)+aL*Phi-z*f(h)
centerR = (d*y*(d+2*y)+I*pol(d,y))/(8*T*W) + I*I*w*(d+4*y+y*y)/(2*k*W)+aR*Phi-w*f(k)
zero("central pairing decomposition", s.Rational(3,4)*(S+T)-A-e0+Phi)
zero("centered left stationarity", rL-centerL)
zero("centered right stationarity", rR-centerR)
det = K**4*(q-1)/(S*T*Z*W)*(q-1+H*(q*S-1)+I*(q*T-1)+H*I*(q+1)*(q*(S+T)-q*q-1))
zero("positive outer determinant factorization", mL*mR-nL*nR-det)
xi = z/S
floor = 1+xi*xi*h-xi*h*s.log(h)/(h-1)
zero("centered exterior norm floor", floor-s.Rational(3,4)-x*(x+2*z*H)/(4*S*S)-z*h/S*f(h)/H)

# The Casimir expansion is polynomial in the independent cubic remainder.
K0, S0, T0, ph, du, dv = s.symbols("K0 S0 T0 ph du dv", positive=True)
U0, d0, x0, y0 = K0-1, 4-K0, S0-2, T0-2
e00 = 1-K0/8+1/K0
cx = -(2*d0*(6-d0)+x0*(24-d0*d0))/(4*K0)
cy = -(2*d0*(6-d0)+y0*(24-d0*d0))/(4*K0)
ell = S0*du+T0*dv
E = e00-ph+ell
gamma = K0*K0*(4*(s.Rational(3,4)+du)*(s.Rational(3,4)+dv)-E*E)/(16*U0*U0)
expanded = -d0**4/64+K0*K0*(2*e00*ph-ph*ph+cx*du+cy*dv+2*ph*ell+4*du*dv-ell*ell)
zero("centered Casimir identity", 16*U0*U0*(gamma-s.Rational(3,16))-expanded)
zero("base rational cancellation", K0*K0*(s.Rational(9,4)-e00*e00)-3*U0*U0+d0**4/64)
zero("left linear coefficient", 3-2*e00*S0-cx)
zero("right linear coefficient", 3-2*e00*T0-cy)
r, rho = s.symbols("r rho", positive=True)
zero("cubic function first derivative", s.diff(f(r),r)-(r-1)**2/(2*r*r))
zero("cubic function second derivative", s.diff(f(r),r,2)-(r-1)/r**3)
zero("positive-series derivative", s.diff(f((1+rho)/(1-rho)),rho)-4*rho*rho/(1-rho*rho)**2)
zero("Casimir threshold conversion", 16*U0*U0*(s.Rational(3,16)-s.Rational(23,125))-s.Rational(7,125)*U0*U0)

# Every constant below is an exact rational comparison in the hand proof.
assert Q(7,2)/Q(16,5) == Q(35,32)
assert 2-Q(35,32) == Q(29,32)
assert Q(29,32)*2-1 == Q(13,16)
assert Q(2960,1729) > Q(3,2)
assert Q(16940,10621) > Q(3,2)
assert Q(77,20)**3 >= 8
assert Q(3,20)**2+4*Q(3,20)+2 <= Q(86,5)
assert 8*(1+Q(3,20)) <= 2*Q(86,5)
assert 16+8*Q(3,20) == Q(86,5)
assert Q(1,2)/(8*2*Q(77,20)) == Q(5,616)
assert Q(86,5)/(8*2*Q(77,20)) == Q(43,154)
assert Q(23,20)*Q(83,20)/(2*Q(77,20)) == Q(1909,3080)
assert Q(1909,3080) < Q(5,8)
assert (4/Q(77,20))/48 == Q(5,231)
assert (4/Q(77,20))*Q(43,20)*Q(3,20)/48 == Q(43,6160)
assert Q(5,616)+Q(5,231) == Q(5,168) < Q(1,32)
assert Q(43,154)+Q(43,6160) == Q(1763,6160) < Q(3,10)
ss, HH = s.symbols("ss HH", nonnegative=True)
zero("residual square completion", s.Rational(5,8)*HH*HH*ss-HH**3/24-HH*(s.Rational(75,32)*ss*ss-(HH-s.Rational(15,2)*ss)**2/24))
assert Q(3,10)+Q(75,32) == Q(423,160) < Q(27,10)
assert Q(1,16) < Q(27,40)
assert Q(27,10)/Q(3,2) == Q(9,5)
assert 6/Q(77,20) == Q(120,77)
assert Q(120,77)*Q(9,5) == Q(216,77)
assert Q(43,20)*Q(9,5) == Q(387,100)
assert Q(387,100)**2 == Q(149769,10000)
ss = Q(3,20)
loss = Q(400,3249)*(ss**4/1024+Q(216,77)*ss**3+Q(149769,10000)*ss**4+ss**6/2304)
assert loss == Q(59749568577,28464128000000)
lower = Q(3,16)-loss
assert lower == Q(5277274431423,28464128000000)
assert lower-Q(37,200) == Q(11410751423,28464128000000) > 0
assert Q(37,200) > Q(23,125)
print("PASS all rational bounds in the broad circular exclusion")
print("Exact normalized Casimir lower:", lower)
print("All centered-system and broad-corner checks passed.")
