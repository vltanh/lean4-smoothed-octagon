"""Exact supplementary identities for the reverse-centre phase bound.

Command: python3 explorations/mixed_reverse_centre_phase_certificate.py
Validated with Python 3.12.14 and SymPy 1.14.0.

The hand domain is 0 < r,t < 1/2, 0 < rho < r*t, and
3/4 < u <= 1-r+r*r, 3/4 < v <= 1-t+t*t. No random inputs,
numerical optimization, or trajectory sampling are used. The symbolic
identities do not themselves certify the inequalities, endpoint rank,
geometric winding, or full constrained-index transfer; see the note.
"""

import platform
import sympy as sp

r, t, rho, u, v = sp.symbols("r t rho u v", positive=True)
U, V = 1 - r + r**2, 1 - t + t**2
E = 1 + r + t - rho + sp.log(rho / (r*t)) - (1-u)/r - (1-v)/t
B = -1 + 2*r + 2*t - rho + sp.log(rho / (r*t))
L = rho*(4*u*v-E**2) - (1-rho)**2*E
Lstar = rho*(4*U*V-B**2) - (1-rho)**2*B

checks = []


def check(name, expr):
    assert sp.simplify(expr) == 0, name
    checks.append(name)


check("upper-corner E", E.subs({u: U, v: V}) - B)
check("u derivative", sp.diff(L, u) - (4*rho*v-(2*rho*E+(1-rho)**2)/r))
check("v derivative", sp.diff(L, v) - (4*rho*u-(2*rho*E+(1-rho)**2)/t))
check("strengthened u derivative", -sp.diff(L, u)-E*(1-r)/r
      - ((1-rho)**2-4*rho*r*v+E*(2*rho-1+r))/r)
check("strengthened v derivative", -sp.diff(L, v)-E*(1-t)/t
      - ((1-rho)**2-4*rho*t*u+E*(2*rho-1+t))/t)
check("corner first derivative", sp.diff(Lstar, rho)
      - (4*U*V-B**2-(1-rho)**3/rho))
check("corner second derivative", sp.diff(Lstar, rho, 2)
      - (1-rho)/rho**2*((1-rho)*(1+2*rho)-2*rho*B))
check("endpoint factorization", Lstar.subs(rho, r*t)
      - (1-2*r)*(1-2*t)*(1-r*t)**2)
check("endpoint derivative factorization", sp.diff(Lstar, rho).subs(rho, r*t)
      - (1-r*t)**2*(4*r*t-1)/(r*t))
check("positive polynomial floor",
      (1-sp.Rational(11, 2)*rho+7*rho**2)-sp.Rational(1, 16)
      - (sp.Rational(1, 4)-rho)*(sp.Rational(15, 4)-7*rho))

K = 4/(1-rho)
a2 = rho*K
gamma2 = K**2*(4*u*v-E**2)/256
e = E/16
omega = a2*((1-r)/r*(U-u)+(1-t)/t*(V-v))/4
M = 8*a2/K**2
T2 = 4*a2**2*gamma2/K**2
check("weaker physical translation", a2*gamma2-K*e-K**3*L/256)
check("full physical translation", 2*T2-K*e*(M+2*omega)
      - a2*K*(L-E*((1-r)/r*(U-u)+(1-t)/t*(V-v)))/32)

m = sp.symbols("m", integer=True)
n = (2*m-1)/3
check("all-short index subtraction", m-1-2*(m-n-1)-3-(m-8)/3)

print(f"Python {platform.python_version()}, SymPy {sp.__version__}.")
print(f"PASS: {len(checks)} exact reverse-centre phase and index identities.")
print("Uniform inequalities and full endpoint/index interfaces remain hand arguments.")
