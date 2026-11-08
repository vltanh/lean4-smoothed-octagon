#!/usr/bin/env python3
"""Exact local identities for GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md.

Run: python explorations/global_structure_forward_ellipticity_certificate.py
Requires Python 3 and SymPy. No sampled word lengths, optimization, ODE,
Lean, Lake, typechecking, or CI. The cyclic-kernel contradiction and PMP
switching interpretation are hand arguments in the note, not tested here.
"""
import platform
import sympy as s

x,a,b=s.symbols('x a b', positive=True)
u,v,w=s.symbols('u v w', real=True)
checks=0

def check(expr,label):
    global checks
    zero=s.zeros(*expr.shape) if isinstance(expr,s.MatrixBase) else s.Integer(0)
    if s.simplify(expr)!=zero:
        raise AssertionError(label)
    checks+=1

sm=x+a
sp=a+b
K=a*a+4
q=sm*sp/K
M=s.Matrix([[u,v],[w,-u]])
V=2*s.Matrix([[-a/K,q*q/sp],[-1/sm,a/K]])
dm=-v/sm**2
dp=sm**2*w/K**2
e=u/K
check(s.trace(M*V)-2*(sm*dm+sp*dp-2*a*e),'stationarity Gram identity')
check(dm*dp-e*e-M.det()/K**2,'Gram determinant identity')
T=s.diag(q,1/q)
check((T.inv()*M*T)[1,0]-sp**2*dp,'switch Gram diagonal')

D0=s.diag(-1,1)
D1=s.Matrix([[1,-2],[0,-1]])
check(D0*D1-D1*D0+D0+D1-s.Matrix([[0,2],[0,0]]),'group bracket')
c=(4-a*b)/(a+b)
l0=a*(a+b+c)/8
l1=b*(a+b+c)/8
check(l0+l1-(a+b)*(s.diff(l0,a)+s.diff(l1,b))+(a*a+a*b+b*b)/4,'cost bracket')

jm=(x*x+x*a+a*a)/(4*sm**2)
jp=(a*a+a*b+b*b)/(4*sp**2)
ell=1/sm+1/sp
C=(x+a+b-a*a*ell+a**3/K-a*s.log(q))/4
check(sm*jm+sp*jp-(x+b+a*a*ell)/4,'off-diagonal scalar sum')
check((sm*jm+sp*jp-C)/(4*a)+(1-2*a*ell+a*a/K-s.log(q))/16,'off-diagonal lower bound')
check(jp/2-s.Rational(3,32)-(a-b)**2/(32*sp**2),'diagonal threshold')

# The recurrence and its nonzero Wronskian can be checked in a single
# determinant-one prefix frame; they are invariant under that prefix.
yminus=s.Matrix([0,-1/sm])
y=s.Matrix([sm/K,0])
Knext=b*b+4
ynext=sp/Knext*s.Matrix([q,1/q])
check(K*yminus-sp*sp*y+Knext*ynext,'Jacobi recurrence')
check(s.det(s.Matrix.hstack(yminus,y))-1/K,'Jacobi Wronskian')
print(f'Python {platform.python_version()}, SymPy {s.__version__}.')
print(f'PASS: {checks} exact local identities.')
print('The uniform theorem also requires the hand PMP and cyclic-kernel arguments.')
