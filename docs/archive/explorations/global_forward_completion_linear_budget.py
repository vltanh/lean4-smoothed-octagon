#!/usr/bin/env python3
"""Exact rational certificate for GLOBAL_FORWARD_LINEAR_BUDGET.md."""
import sympy as s

U,t=s.symbols('U t')
xstar=(5*U-8)/3

def log_upper(v):
    r=(v-1)/(v+1)
    return 2*r+2*r**3/(3*(1-r*r))

def gbar(x):
    return (3*x-U-log_upper((1+x)**2/(1+U))/2
            -x*x*log_upper((1+x)**2/(x*x+U))/2)

D=s.factor(2*gbar(xstar)+5*gbar(1)-s.Rational(2501,1384)*U)
P,Q=s.fraction(D)
Qstated=(934200*(U-1)**2*(U+1)*(U+5)
         *(25*U**2-71*U+64)*(25*U**2-41*U+34)
         *(50*U**2-121*U+89))
assert s.factor(Q-Qstated)==0
assert s.degree(P,U)==11
mapped=s.factor(s.Rational(15625,4096)*(1+t)**11
                *P.subs(U,(11+15*t)/(5+5*t)))
poly=s.Poly(mapped,t)
coeffs=[892004586624,18085304987172,155004439305393,758740802025942,
        2383177735230363,5068582904755656,7455203371987515,
        7562347243116750,5144863695643125,2199783702600000,
        513318352762500,44906296750000]
assert [poly.nth(i) for i in range(12)]==coeffs
assert all(c>0 for c in coeffs)
assert P.subs(U,3)>0
quadratics=[25*U**2-71*U+64,25*U**2-41*U+34,50*U**2-121*U+89]
assert [s.discriminant(q,U) for q in quadratics]==[-1359,-1719,-3159]
assert s.Rational(173,100)**2<3
assert s.Rational(173,100)*s.Rational(2501,1384)==s.Rational(2501,800)
print('PASS: exact denominator, degree-eleven positive coefficients, endpoint, discriminants, constants.')
print('Scope: z+w < 5(U-1)/3 at a competitive all-forward minimum; F remains open.')
