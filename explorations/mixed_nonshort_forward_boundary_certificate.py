#!/usr/bin/env python3
"""Exact algebra for the nonshort forward endpoint reduction.

This verifies identities, not the two quantified endpoint exclusions.
The same-root comparison, concavity inequality and domain are hand proofs
in docs/MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md. No Lean or CI.
"""
import sympy as s

d, r, W, v, Cd, w, w0, lo, hi, theta = s.symbols(
    "d r W v Cd w w0 lo hi theta", real=True)
Q, Z, Kr = d*d+4, d+r, r*r+4
cap = s.Rational(23, 125)
checks = 0

def zero(name, expression):
    global checks
    reduced = s.factor(expression)
    if reduced != 0:
        raise AssertionError((name, reduced))
    checks += 1
    print("PASS", name)

h = Q*(W*v+Z*w-Cd)/(16*d)
gamma = Q*Q*v*w/64-h*h
transport = (Q*Q*v-16*h*Z*Z+w*Z**4)/(Kr*Kr)
B = Z**3*(4-d*r)/(d*Kr*Kr)
C = Q*Q*Z*Z/(256*d*d)
zero("forward stationarity reconstruction", Cd-W*v-Z*w+16*d*h/Q)
zero("diagonal derivative along the root", s.diff(h,w)-Q*Z/(16*d))
zero("transported norm decreases with outgoing norm", s.diff(transport,w)+B)
zero("transported norm is affine", s.diff(transport,w,2))
zero("Casimir derivative", s.diff(gamma,w)-(Q*Q*v/64-h*Q*Z/(8*d)))
zero("strict Casimir concavity", s.diff(gamma,w,2)+2*C)

h0 = h.subs(w,w0)
gamma0 = gamma.subs(w,w0)
t0 = transport.subs(w,w0)
tau = t0-s.Rational(3,4)
wcap = w0+tau/B
zero("upper endpoint has norm three quarters",
     transport.subs(w,wcap)-s.Rational(3,4))
Gprime = Q*Q*v/64-h0*Q*Z/(8*d)
cleared = B*B*(gamma0-cap)+B*Gprime*tau-C*tau*tau
zero("cleared upper-endpoint Casimir cap",
     cleared-B*B*(gamma.subs(w,wcap)-cap))
zero("exact nonnegative chord remainder",
     gamma.subs(w,(1-theta)*lo+theta*hi)
     -(1-theta)*gamma.subs(w,lo)-theta*gamma.subs(w,hi)
     -C*theta*(1-theta)*(hi-lo)**2)

print(f"ALL {checks} EXACT FORWARD ENDPOINT IDENTITIES PASSED")
print("The quantified endpoint covers and independent completion audit are separate obligations.")
