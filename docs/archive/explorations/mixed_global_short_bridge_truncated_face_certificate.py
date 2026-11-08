"""Replay the fixed central truncated-root certificate for either D sign.

Python 3.12 / SymPy 1.14.  The two CSV files are static, complete integer
coefficient tables.  This replay uses no optimization, floating arithmetic,
mesh, Lean, Lake, typecheck or CI.  It proves only the named scalar face;
the complete short-bridge comparison uses separately proved continuation.
"""
from pathlib import Path
import csv
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ

HERE = Path(__file__).resolve().parent
checks = 0


def identity(expr):
    global checks
    assert s.factor(expr) == 0
    checks += 1


zz = s.symbols("zeta", nonnegative=True)
identity(2 / (1 - zz**2) - s.diff(6 * zz / (3 - zz**2), zz)
         - 8 * zz**4 / ((1 - zz**2) * (3 - zz**2)**2))
P, Q = s.symbols("P Q", positive=True)
zt = (P - 2 * Q) / (P + 2 * Q)
C = P**2 + 8 * P * Q + 4 * Q**2
identity(6 * zt / (3 - zt**2) - 3 * (P**2 - 4 * Q**2) / C)

x = s.symbols("x", positive=True)
vp = (131*x**4 + 229*x**3 + 163*x**2 + 47*x + 6) / (6*(x+1)*(3*x+1)**3)
vb = (55*x**2 + 64*x + 25) / (4*(x+1)*(17*x+7))
identity(vb-vp-(x-1)**3*(x**2+22*x+9)/(12*(x+1)*(3*x+1)**3*(17*x+7)))
rr = (x-1)/(x+1)
aa = rr/(2+rr)
identity(vp-(s.Rational(5,4)+rr/4-(1+rr)*(2*aa+s.Rational(2,3)*aa**3)/(2*rr)))

A, B, q, D, E, u, v = s.symbols("A B q D E u v", positive=True)
w = (q*q*v + D*D*u - D*q*E)/P**2
EL = (2*D*u-q*E)/P
T = P/Q
TB = Q/A**2
rat = (2*(w-s.Rational(3,4))+(u-1)*TB+1+1/TB-1/(T*TB)
       -EL-3*(P**2-4*Q**2)/C)
numerator = (4*Q*C*(q*q*v+D*D*u-D*q*E)-P*P*Q*C
             +2*P*P*C*(u-1)*Q**2/A**2+2*A*A*P*P*C-2*A*A*P*Q*C
             -2*P*Q*C*(2*D*u-q*E)-6*P*P*Q*(P*P-4*Q*Q))
identity(numerator-2*P*P*Q*C*rat)

# Independently construct the polynomial before any order substitution.
R, h, j, k, ell = ring("h,j,k,ell", ZZ)
A = 1+h
x = A+j
B = x+k
y = x+ell
q = (1+x)*(1+y)
P = q+A*A-1
Q = A*(A+B)
D = A*A+2*A*B+1+2*x-2*B*x
C = P*P+8*P*Q+4*Q*Q


def numerator(uu, vv):
    qe = q*(uu-1)*(1+x)+q*(vv-1)*(1+y)+q+(1+x)+(1+y)-1
    wn = q*q*vv+D*D*uu-D*qe
    return (4*Q*C*wn-P*P*Q*C+2*P*P*C*(uu-1)*(A+B)**2
            +2*A*A*P*P*C-2*A*A*P*Q*C
            -2*P*Q*C*(2*D*uu-qe)-6*P*P*Q*(P*P-4*Q*Q))


base = numerator(0, 0)
nu = numerator(1, 0)-base
nv = numerator(0, 1)-base


def vn(t):
    return 131*t**4+229*t**3+163*t**2+47*t+6


def vd(t):
    return 6*(t+1)*(3*t+1)**3


raw = -(nu*vn(x)*vd(y)+nv*vn(y)*vd(x)+base*vd(x)*vd(y))
assert max(e[2] for e in raw) == 5
checks += 1

# Genuine strengthened order: beta-x=7*h*x*z/[(7+2*x)*(1+z)].
S, h, j, z, ell = ring("h,j,z,ell", ZZ)
parts = [S.zero for _ in range(6)]
for (a, b, c, d), value in raw.items():
    parts[c][(a, b, 0, d)] = value
x = 1+h+j
rden = (7+2*x)*(1+z)
poly = S.zero
for i, part in enumerate(parts):
    poly += part*(7*h*x*z)**i*rden**(5-i)

G = rden*(j*(j+2)+(h+j+2)*ell-2*h*(h+1))-14*(h+1)*h*x*z
CG = 136048896*j*z*(12288*z**3+40192*z**2+42928*z+12717)
derivative_positive = S.zero
with (HERE / "mixed_global_short_bridge_truncated_face_derivative_positive.csv").open() as f:
    for row in csv.DictReader(f):
        ex = tuple(int(row[key]) for key in ("h", "j", "z", "ell"))
        value = int(row["coefficient"])
        assert min(ex) >= 0 and value > 0 and ex not in derivative_positive
        derivative_positive[ex] = value
assert len(derivative_positive) == 11438
checks += 1
assert poly.diff(ell) == CG*G+derivative_positive
checks += 1
assert max(e[2] for e in poly) == 5
checks += 1
assert max(e[2] for e in derivative_positive) == 5
checks += 1

# At ell=0, G>=0 implies j>h.  Substitute j=h+t.
U, hh, t, zz = ring("h,t,z", ZZ)
poly_zero = U.zero
for (a, b, c, d), value in poly.items():
    if d == 0:
        poly_zero += value*hh**a*(hh+t)**b*zz**c
square = 27518828544*t*zz**4*(873+603*zz+7169*hh*zz)*(hh-t)**2
equal_positive = U.zero
with (HERE / "mixed_global_short_bridge_truncated_face_equal_turn_positive.csv").open() as f:
    for row in csv.DictReader(f):
        ex = tuple(int(row[key]) for key in ("h", "t", "z"))
        value = int(row["coefficient"])
        assert min(ex) >= 0 and value > 0 and ex not in equal_positive
        equal_positive[ex] = value
assert len(equal_positive) == 1905
checks += 1
assert poly_zero == square+equal_positive
checks += 1
assert equal_positive[(0, 3, 0)] == 26748301344768
checks += 1
assert equal_positive[(0, 3, 5)] == 10154447732736
checks += 1

print(f"{checks} exact identities/table checks passed; "
      "11,438 derivative coefficients, 1,905 equal-turn coefficients, one explicit square.")
