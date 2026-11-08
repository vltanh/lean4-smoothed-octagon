#!/usr/bin/env python3
"""Exact identities for GLOBAL_STRUCTURE_FORWARD_ACUTE.md.

Run: python explorations/global_structure_forward_acute_certificate.py
Requires Python 3 and SymPy. No sampled lengths, numerical signs,
optimization, Lean, Lake, typechecking, or CI. The inequalities and
PMP interpretation are proved by hand in the note.
"""
import platform
import sympy as sp

checks = 0


def check(expr, label):
    global checks
    zero = sp.zeros(*expr.shape) if isinstance(expr, sp.MatrixBase) else 0
    if sp.simplify(expr) != zero:
        raise AssertionError(label)
    checks += 1


a, x, y = sp.symbols('a x y', positive=True)
p, s, K = x + a, a + y, a*a + 4
q = p*s/K
tm = (x*x + x*a + a*a)/(8*p*p)
tp = (a*a + a*y + y*y)/(8*s*s)
C = (x + a + y - a*a*(1/p + 1/s) + a**3/K - a*sp.log(q))/4
E = 1 - 2*a*(1/p + 1/s) + a*a/K - sp.log(q)
check(C/2 - p*tm - s*tp - a*E/8, 'triangle slack')

u, v, c, u0, v0, h, pp, ss = sp.symbols('u v c u0 v0 h p s', real=True)
F = u*v/(pp*ss) - (c-u-v)**2/(4*a*a)
H = sp.hessian(F, (u, v))
check(H*sp.Matrix([1, -1]) + sp.Matrix([1, -1])/(pp*ss), 'first Hessian eigenpair')
check(H*sp.Matrix([1, 1]) - (1/(pp*ss)-1/a**2)*sp.Matrix([1, 1]), 'second Hessian eigenpair')
base = F.subs({u:u0, v:v0, c:u0+v0+h})
first = F.subs({u:u0+h, v:v0, c:u0+v0+h})
second = F.subs({u:u0, v:v0+h, c:u0+v0+h})
check(first-base-h*v0/(pp*ss)-h*h/(4*a*a), 'first vertex difference')
check(second-base-h*u0/(pp*ss)-h*h/(4*a*a), 'second vertex difference')

r, t, d, L = sp.symbols('r t d L', real=True)
f = lambda z: 1-z+z*z
En = 1-2*(r+t)+d-L
check(4*f(r)*f(t)-En**2-3*(1-d)**2
      -4*(d-r*t)*(1+r+t-d-r*t)-2*L*En-L**2,
      'strict determinant gap factorization')
check(tm-f(a/p)/8, 'left switching threshold')
check(tp-f(a/s)/8, 'right switching threshold')
check(K-4/(1-a*a/K), 'dimensionless scale')

print(f'Python {platform.python_version()}, SymPy {sp.__version__}.')
print(f'PASS: {checks} exact scalar identities.')
print('The strict determinant bound and period scope are hand arguments in the note.')
