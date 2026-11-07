#!/usr/bin/env python3
"""Exact supplementary algebra for MIXED_GLOBAL_SYMMETRIC_ESCAPE.md.

No floating-point sampling, Lean invocation, or ODE discretization.
The Markdown note contains the hand proof and its explicit scope.
Requires SymPy. Run from any directory with Python 3.
"""

import sympy as sp

h, v, L = sp.symbols('h v L', positive=True)
t, theta = sp.symbols('t theta')
q = sp.sqrt(3) / 3
checks = 0


def equal(lhs, rhs=0, label='identity'):
    global checks
    difference = sp.simplify(sp.factor(lhs - rhs))
    if difference != 0:
        raise AssertionError(f'{label}: {difference}')
    checks += 1


def positive(value, label='rational positivity'):
    global checks
    if not bool(value > 0):
        raise AssertionError(f'{label}: {value}')
    checks += 1


r = (2-h)/h
beta = 1-r
ell = 2*(h-1)/h**2
m0 = h+1-2*h*L/(h-1)
mu = m0/3
j = 4*(h-1)*(2-h)/h**2 * (L-(h-1)/h)
b = q*beta
Sb = v*q*ell
Qb = 1+(beta**2-m0-j/r)*v/3-r*j*v**2/9
n0 = Qb-(1+mu)*Sb**2

# Direct integrals in z=x/q. The first integral ends at z=h-1;
# the second runs from h-1 to beta, with log endpoint ratio -L.
equal(h-1-2*L+(1-m0)*(1-1/h), label='inner moment')
equal(r**2*(beta-(h-1)-2*L+(1-m0)*(1/r-1/(h*r))), j,
      'outer moment')
equal(1-1/h+r**2*(1/r-1/(h*r)), ell, 'area integral')

K = lambda x: sp.Matrix([[1,x],[0,1]])
R0 = sp.Matrix([[sp.Rational(1,2),-sp.sqrt(3)/2],
                [sp.sqrt(3)/2,sp.Rational(1,2)]])
M = sp.Matrix([[-(1+mu)*Sb,-(1+mu)],
               [Qb,(1+mu)*Sb]])
D = 3-v*r*(2-r)
F = h**2*(v*r**2+3)
a = q*(v*r*(4-r)-3)/(v*r**2+3)
w = (v*r**2+3)**2/(16*v)
W = D**2/(12*v)
exit_ratio = (3+v*(2-r)**2)/D

X = sp.sqrt(v)*sp.Matrix([[b,-b*b-1/v],[1,-b]])
Xrot = (R0.T*X*R0).applyfunc(sp.factor)
equal(Xrot[0,0]/Xrot[1,0], a, 'rotated x')
equal(Xrot[1,0]**2, w, 'rotated w')
equal((q-a)**2*w, W, 'vertex invariant')
equal((1+W)*(q-a)/(2*q*W), exit_ratio, 'exit factor')

Mrot = (K(-a)*R0.T*K(b)*M*K(-b)*R0*K(a)).applyfunc(sp.factor)
mu_rot = -1-Mrot[0,1]
delta = sp.factor(mu_rot-a*a)
A = (2-h)*(-6*L*h**3+12*L*h**2-12*L*h+8*L
           +h**4+2*h**3+7*h**2-26*h+16)
B = -3*h**2*(2*L*h**2-8*L*h+4*L+h**3-4*h**2+7*h-4)
C = (3*h-2)*(-2*L*h**3-4*L*h**2-4*L*h+8*L
             +3*h**4-14*h**3+53*h**2-74*h+32)
E = -3*h**2*(2*L*h**2-8*L*h+4*L+h**3+4*h**2-9*h+4)
equal(delta, 4*h*v*(B-A*v)/(3*(h-1)*F**2), 'initial source')
B0 = Mrot[1,0]-1+delta*w
B1 = -2*Mrot[0,0]-2*a-(W-1)*delta/(q-a)
equal(B0, -(h-1)*(h*L-h+1)*F**2/(9*h**6), 'initial gap')
equal(B1, -sp.sqrt(3)*F*(C*v+E)/(18*h**5*(h-1)*D),
      'initial gap derivative')

# Derive that derivative independently from the vertex Hamiltonian gap.
xx, ww, pp, mm, kk, nn = sp.symbols('x w p mu k n')
Q = 1+(xx**2-mm)*ww+ww*((q-xx)*ww+1/(q-xx))*pp
Bgap = nn-Q
Bdot = (sp.diff(Bgap,xx)+sp.diff(Bgap,ww)*2*ww/(q-xx)
        +sp.diff(Bgap,pp)*(mm-xx**2-2*pp/(q-xx))
        -sp.diff(Bgap,nn)*ww*kk)
expected = -kk-2*xx-(((q-xx)**2*ww)-1)*(mm-xx**2)/(q-xx)
equal((Bdot/ww).subs(pp,0), expected, 'independent B1 equation')

lo = 2*(h-1)/(h+1)
hi = (h-1)*(h*h+10*h+1)/(6*h*(h+1))
equal(1/h-sp.diff(lo,h), (h-1)**2/(h*(h+1)**2), 'log lower')
equal(sp.diff(hi,h)-1/h, (h-1)**4/(6*h*h*(h+1)**2), 'log upper')

F1 = -4*L*h+h**3-2*h**2+7*h-6
F2 = 2*L*h**3-8*L*h**2+4*L*h+h**4-8*h**3+23*h**2-24*h+8
equal(C*B+E*A, -24*h**2*(h-1)*F1*F2, 'gap sign factorization')
reduced = [
 (A/((2-h)*(h-1)**2),
  h*(h*h-7*h+30)/(h+1),
  -2*(6*h**3-39*h*h-5*h+2)/(3*h*(h+1))),
 (B/(3*h*h*(h-1)**2),
  (-h*h-3*h+12)/(h+1),
  -2*(2*h**3+2*h*h-15*h-1)/(3*h*(h+1))),
 (C/((3*h-2)*(h-1)**2),
  (3*h**3-9*h*h+14*h+16)/(h+1),
  2*(4*h**4-14*h**3+21*h*h+27*h-2)/(3*h*(h+1))),
 (F1/(h-1), (h**3-3*h+6)/(h+1),
  (3*h**3-2*h*h-5*h+16)/(3*(h+1))),
 (-F2/(h-1)**3, (8-h*h)/(h+1),
  -2*(2*h*h-2*h-11)/(3*(h+1))),
]
for idx, (expression, lower, upper) in enumerate(reduced):
    equal(expression.subs(L,lo), lower, f'base sign {idx} lower')
    equal(expression.subs(L,hi), upper, f'base sign {idx} upper')

vX = 3*h*h/((2-h)*(h+2)*(2*h-1))
vR = 33*h*h/((22-h)*(3*h-2))
z = q-(q-a)/h
equal((z+a).subs(v,vX), label='critical point threshold')
equal(exit_ratio.subs(v,vR), sp.Rational(16,5), 'exit threshold')
equal(sp.diff(a/q,v), 12*r/(v*r*r+3)**2, 'state monotonicity')

U1 = h**3+6*h*h-6*h-12
U2 = 2*h**3+7*h*h-10*h-16
V1 = 7*h**4-79*h**3+144*h*h+144*h-264
V2 = 3*h**4-98*h**3+234*h*h+151*h-362
Qpoly = h**5+4*h**4-33*h**3+36*h*h+6*h-2
thresholds = [
 (B-A*vX,
  -6*h*h*(h-1)**3*U1/((h+1)*(h+2)*(2*h-1)),
  -4*h*h*(h-1)**3*U2/((h+1)*(h+2)*(2*h-1))),
 (B-A*vR,
  -6*h*h*(h-1)**2*V1/((h-22)*(h+1)*(3*h-2)),
  -4*h*h*(h-1)**2*V2/((h-22)*(h+1)*(3*h-2))),
 (B-3*A,
  -12*h*(h-3)*(h-1)**2*(3*h-5)/(h+1),
  -4*(h-1)**2*Qpoly/(h*(h+1))),
]
for idx, (expression, lower, upper) in enumerate(thresholds):
    equal(expression.subs(L,lo), lower, f'threshold {idx} lower')
    equal(expression.subs(L,hi), upper, f'threshold {idx} upper')

# All low-degree sign polynomials may independently be checked in
# Bernstein form; this is redundant with the derivative arguments in the note.
def bernstein_coefficients(poly, left, right):
    transformed = sp.Poly(sp.expand(poly.subs(h,left+(right-left)*t)),t)
    degree = transformed.degree()
    return [sp.factor(sum(transformed.nth(i)*sp.binomial(k,i)
                          /sp.binomial(degree,i) for i in range(k+1)))
            for k in range(degree+1)]

for idx, (_, lower, upper) in enumerate(reduced):
    for side, expr in enumerate((lower,upper)):
        numerator, denominator = sp.fraction(sp.factor(expr))
        for value in bernstein_coefficients(numerator,sp.Rational(1),sp.Rational(2)):
            positive(value, f'base Bernstein {idx}/{side}')

for name, poly, left, right in [
    ('-U1',-U1,sp.Rational(1),sp.Rational(5,3)),
    ('-U2',-U2,sp.Rational(1),sp.Rational(5,3)),
    ('V1',V1,sp.Rational(5,4),sp.Rational(5,3)),
    ('V2',V2,sp.Rational(5,4),sp.Rational(5,3)),
    ('-Q',-Qpoly,sp.Rational(5,3),sp.Rational(2)),
]:
    for value in bernstein_coefficients(poly,left,right):
        positive(value, f'threshold Bernstein {name}')

for poly, point, target in [
    (U1,sp.Rational(5,3),-sp.Rational(19,27)),
    (U2,sp.Rational(5,3),-sp.Rational(107,27)),
    (V1,sp.Rational(5,4),sp.Rational(971,256)),
    (V2,sp.Rational(5,4),sp.Rational(2123,256)),
    (sp.diff(V1,h),sp.Rational(5,3),sp.Rational(2573,27)),
    (sp.diff(V2,h),sp.Rational(5,3),sp.Rational(1529,9)),
    (Qpoly,sp.Rational(5,3),-sp.Rational(256,243)),
    (sp.diff(Qpoly,h),sp.Rational(5,3),-sp.Rational(2944,81)),
    (sp.diff(Qpoly,h),sp.Rational(2),-sp.Rational(38)),
]:
    equal(poly.subs(h,point), target, 'derivative proof endpoint')
equal(sp.diff(Qpoly,h,3),6*(10*h*h+16*h-33), 'Q convex derivative')

Dcal = (1+m0/3)*(1+(beta**2-m0-j/r)*v/3-r*j*v*v/9
                 -(1+m0/3)*ell*ell*v*v/3)
equal(Dcal, (1+mu)*n0, 'scaled Casimir')
equal(M.det(), Dcal, 'covector determinant')
Dcal_interp = Dcal.subs(v,vR).subs(L,lo+theta*(hi-lo))
P = sp.factor(2700*(h-22)**2*(h+1)**2*(3*h-2)**2
              *(Dcal_interp-sp.Rational(99,100)))
sp.Poly(P,h,theta)  # Also verifies that the cleared expression is a polynomial.
equal(sp.diff(P,theta,2)/2,
      1100*(h-1)**4*(h*h-4*h+2)*(19*h*h+24*h-22),
      'log interpolation concavity')

# These are the independently recorded hand-certificate coefficients.
table = [
 (1,47628,47628),
 (8,463239,463239),
 (448,25084107,25235307),
 (896,41248845,42299145),
 (8960,291978441,316279191),
 (3584,73477692,92122967),
 (114688,1701216315,2723688515),
 (16384,338542731,570256931),
 (16384,702595053,1049779728),
]
for endpoint in (0,1):
    calculated = bernstein_coefficients(P.subs(theta,endpoint),
                                       sp.Rational(1),sp.Rational(5,4))
    for k, (denom,left,right) in enumerate(table):
        claimed = sp.Rational((left,right)[endpoint],denom)
        equal(calculated[k],claimed,f'Casimir Bernstein {k}/{endpoint}')
        positive(claimed,f'Casimir Bernstein positivity {k}/{endpoint}')

equal(sp.Rational(891,400)-sp.Rational(313,210)**2,
      sp.Rational(211,35280), 'complete period determinant separation')
positive(sp.Rational(211,35280))
print(f'PASS: {checks} exact algebra identities and rational sign checks.')
print('Scope: symmetric equal-factor 2121 core; positive initial 0 pad;')
print('outgoing 0 pad of factor >= h; genuine competitive closed PMP lift.')
print('No claim of full asymmetric M1, M2/M3 closure, or kernel validation.')
