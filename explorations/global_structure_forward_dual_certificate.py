#!/usr/bin/env python3
"""Exact local identities for GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN.md.

Run: python explorations/global_structure_forward_dual_certificate.py
Requires Python 3 and SymPy. No numerical samples, optimizer, ODE,
word-length enumeration, Lean, Lake, typechecking, or CI. The index
target is open; this script certifies identities, not a negative graph.
"""
import platform
import sympy as s

checks = 0


def check(expr, label):
    global checks
    zero = s.zeros(*expr.shape) if isinstance(expr, s.MatrixBase) else 0
    if s.simplify(expr) != zero:
        raise AssertionError(label)
    checks += 1


x, a, y, h, H, c = s.symbols('x a y h H c', positive=True)
K, sm, sp = a*a+4, x+a, a+y
phi_local = sm*s.log(sm)+sp*s.log(sp)-a*s.log(K)-4*s.atan(a/2)
check(s.diff(phi_local, a)-s.log(sm*sp/K), 'potential gradient')

bm, bp = s.symbols('bm bp', positive=True)
Cdual = c*((bm+h)/sm+(h+bp)/sp-2*a*h/K)
dm, dp, e = c*(bm+h)/(2*sm**2), c*(h+bp)/(2*sp**2), c*h/(2*K)
check(Cdual-2*(sm*dm+sp*dp-2*a*e), 'dual stationarity')
check((dm*dp-e*e-c*c/K**2)*4*K*K/c**2
      -((bm+h)*(h+bp)*K*K/(sm*sm*sp*sp)-h*h-4),
      'auxiliary q-square identity')
check(x/sm+a*(1/sm+1/sp-2*a/K)+y/sp-8/K, 'B(a) a')

# The derivative of the preceding identity in direction (bm,h,bp).
diag = 1/sm+1/sp-2*a/K
delta_diag = -(bm+h)/sm**2-(h+bp)/sp**2-2*h*(4-a*a)/K**2
derivative_B_times_a = -(bm+h)*x/sm**2+a*delta_diag-(h+bp)*y/sp**2
B_times_b = bm/sm+h*diag+bp/sp
check(derivative_B_times_a+B_times_b+16*a*h/K**2,
      'directional B scaling identity')

j = (a*a+a*y+y*y)/(4*sp**2)
t = h+H
d = c*t/(2*sp**2)
beta = 2*d-j
R = s.Matrix([[j+2*d, -c/sp], [-c/sp, c/(2*t)]])
check(R.det()+c*beta/(2*t), 'dual twist determinant')

f, F = 2*h/a, 2*H/y
Goff = j+2*d-c*(f+F)/sp+c*f*F/(2*t)
check(Goff+beta+2*c*a*y*(h/a-H/y)**2/(sp**2*t),
      'candidate graph off-diagonal')

# At a stationary point C=c B(a)b and J''a=C-8a/K^2.
C = s.symbols('C', real=True)
Ma = 2*C+(16*c*h-8)*a/K**2
Ga = Ma-2*C+(2*h/a)*(-8*c/K+8*c/(h*h+4))
target = (16*c*h*(a**4+8*a*a-4*h*h)-8*a*a*(h*h+4))/(a*K*K*(h*h+4))
check(Ga-target, 'candidate graph scaling identity')

print(f'Python {platform.python_version()}, SymPy {s.__version__}.')
print(f'PASS: {checks} exact local identities.')
print('No negative-graph or uniform cost-index sign is asserted.')
