#!/usr/bin/env python3
"""Exact companion to docs/COMPACT_DOMAIN_SOURCE_AUDIT.md.

Run: python explorations/compact_domain_source_certificate.py
Requires Python 3 and SymPy. The 24 fixed checks use exact identities and
rational comparisons, with no sampling or floating-point arithmetic.
Geometric area bounds, the symmetry reduction and monotonicity arguments
are hand obligations stated in the note. No Lean, Lake, typechecking or CI.
"""
import sympy as s
from fractions import Fraction as F
x=s.symbols('x', real=True)
y,t,b,ss=s.symbols('y t b ss', positive=True)
q=s.sqrt(3)/3
r0=(q+x)/y
r1=(q-x)/y
r2=s.sqrt(3)*(x*x+y*y-q*q)/(2*y)
checks=0

def zero(name,e):
    global checks
    reduced=s.simplify(e)
    if reduced!=0:
        raise AssertionError((name,reduced))
    checks+=1
    print('PASS',name)

def positive(name,e):
    global checks
    if not e>0:
        raise AssertionError((name,e))
    checks+=1
    print('PASS',name)

zero('rho determinant identity',r0*r1+r1*r2+r2*r0-1)
X=s.Matrix([[x,-x*x-y*y],[1,-x]])/y
Z=[s.Matrix([[0,s.Rational(1,3)],[1,0]]),s.Matrix([[q,-s.Rational(2,3)],[0,-q]]),s.Matrix([[-q,-s.Rational(2,3)],[0,q]])]
for i,r in enumerate([r2,r1,r0]):
    zero(f'physical margin {i}',-s.sqrt(3)*s.trace(Z[i]*X)-2*r)
zero('upper-sector rho order',r2-r0-s.sqrt(3)*((x-q)**2+y*y-s.Rational(4,3))/(2*y))
P=s.Rational(227,225)-s.Rational(2,15)/t-s.Rational(113,3375)*t
zero('boundary product', (r0*r2).subs(x,q-y/15).subs(y,t/s.sqrt(3))-P)
zero('product concavity',s.diff(P,t,2)+s.Rational(4,15)/t**3)
Plo=s.Rational(227,225)-s.Rational(263,3375)*s.sqrt(3)
Phi=s.Rational(227,225)-s.Rational(3251,20250)*s.sqrt(3)
zero('lower endpoint product',P.subs(t,s.sqrt(3))-Plo)
zero('upper endpoint product',P.subs(t,9*s.sqrt(3)/2)-Phi)
positive('upper endpoint is the smaller product coefficient',F(3251,20250)-F(263,3375))
positive('sqrt3 upper bound by 26/15',F(26,15)**2-3)
positive('boundary product exceeds 73/100',F(227,225)-F(3251,20250)*F(26,15)-F(73,100))
positive('sqrt(73/100) below 171/200',F(171,200)**2-F(73,100))
positive('square-root slope is positive above 73/100',F(73,100)-F(1,15)**2)
zero('halfplane density rational lower bound',s.Rational(3,4)+(s.Rational(73,100)-s.Rational(2,15)*s.Rational(171,200))/4-s.Rational(113,125))
Pb=(1-b*(ss-b))*(ss-b)/ss
zero('fixed-height product derivative',s.diff(Pb,b)-(-ss-1/ss+4*b-3*b*b/ss))
positive('product derivative negative bound',2-F(4,15))
zero('horoball density exact form',s.Rational(3,4)+s.Rational(239,972)-s.sqrt(478)/243-(242-s.sqrt(478))/243)
positive('sqrt478 below 22',22*22-478)
positive('horoball density exceeds common lower bound',F(220,243)-F(113,125))
positive('sqrt2 lower bound by 140/99',2-F(140,99)**2)
positive('log2 lower three-term bound',F(842,1215)-F(693,1000))
delta_up=(8-4*F(140,99)-F(693,1000))/(2*F(140,99)-1)
positive('octagon density below 903/1000',F(903,1000)-delta_up)
positive('strict separation',F(113,125)-F(903,1000))
print(f'ALL {checks} EXACT CHECKS PASSED')
print('Compact-state input only; no M2 or global cost/equality closure is asserted.')
