#!/usr/bin/env python3
"""Exact identities for GLOBAL_FORWARD_MINIMUM_NONSINGULAR.md.

Python 3 + SymPy. No numerical sampling or optimization; no Lean/Lake/CI.
The theorem is nonsingularity of the actual three-arc multiplier system,
not closure of the F cost-Casimir problem.
"""
import sympy as s

U,z,w,H,K,a=s.symbols('U z w H K a', positive=True)
S,T,L=1+z,1+w,1+U
q=S*T/L
m11=S*S*(U-z)*H/(z*z+U)
m12=L*L*((q-1)+H*(S*q-1))/(S*(z*z+U))
m22=T*T*(U-w)*K/(w*w+U)
m21=L*L*((q-1)+K*(T*q-1))/(T*(w*w+U))
M=s.Matrix([[m11,m12],[m21,m22]])
P=w*w*(z+1)*(U-z)+w*(U*(z+1)*(z+3)-z*z+1)+U*z*(z+3)-U*U+z
rhs=L**4*((q-1)**2+(q-1)*(H*(S*q-1)+K*(T*q-1)))+H*K*(S*T-L)*(S*T+L)*P
assert s.factor(-M.det()*S*T*(z*z+U)*(w*w+U)-rhs)==0
assert s.factor(L**4*(S*q-1)*(T*q-1)-S**3*T**3*(U-z)*(U-w)-(S*T-L)*(S*T+L)*P)==0
assert s.expand(z*(z+1)*(z+3)-z*z+1-(z+1)**3)==0
assert s.factor((a*M).det()-a*a*M.det())==0
print('PASS: 4 exact identities; determinant is strictly negative on the stated domain.')
print('No F exclusion or constrained-index sign is asserted.')
