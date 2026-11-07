#!/usr/bin/env python3
"""Exact algebra for MIXED_GLOBAL_TURN_ELIMINATION.md.

Run: python3 explorations/mixed_global_turn_elimination_certificate.py
Dependencies: Python 3.12 and SymPy 1.14.

Domain: actual normal competitive mixed periods after the double-reverse
run theorem. Physical margins are positive; auxiliary adjacent sums and
the common elliptic scalar gamma are positive. At a turn the two switch
norms equal nu; at a paired turn bridge a,d<min(b,c), nu>3/32, and the
three beta coefficients are positive. The checker verifies identities;
the hand note proves domain signs, inertia, the zero-bridge continuation,
and the actual endpoint/index interface. No remaining F/M2 exclusion is
claimed. No numerical samples, optimizer, trajectory integration,
increasing word catalogue, Lean, Lake, typechecking, or CI are used.
"""

import platform

import sympy as sp


checks = 0


def check(label, expr):
    global checks
    entries = list(expr) if isinstance(expr, sp.MatrixBase) else [expr]
    for entry in entries:
        result = sp.factor(sp.cancel(sp.expand_log(entry, force=True)))
        assert result == 0, (label, result)
    checks += 1


# Derive the completed Hessian from the signed cyclic action, rather
# than assuming its diagonal coefficients. The stationarity residual
# is kept visible in the identity before it is set to zero.
x, a, y, gamma = sp.symbols("x a y gamma", positive=True)
um, bi, up, ep, en = sp.symbols("um bi up ep en", real=True)
delta = (ep + en) / 2
K = a*a + 4


def action_edge(left, right):
    return (
        3*left*right - 4 - (left*left + right*right)*sp.log(left+right)
        + left*left*sp.log(left*left+4)/2
        + right*right*sp.log(right*right+4)/2
    ) / 8


def j(left, right):
    return (left*left + left*right + right*right)/(4*(left+right)**2)


J = ep*action_edge(x, a) + en*action_edge(a, y)
C = sp.diff(J, a)
Baux = ep*(um+bi)/(x+a) + en*(bi+up)/(a+y) - 2*delta*a*bi/K
DBii = -ep*(um+bi)/(x+a)**2 - en*(bi+up)/(a+y)**2
DBii -= 2*delta*bi*(4-a*a)/K**2
Mii = sp.diff(J, a, 2) - gamma*DBii
completed_ii = ep*(2*gamma*(um+bi)/(x+a)**2
                    + (gamma*(um+bi)/(x+a)**2-j(x,a))*x/a)
completed_ii += en*(2*gamma*(bi+up)/(a+y)**2
                     + (gamma*(bi+up)/(a+y)**2-j(a,y))*y/a)
completed_ii -= delta*(4*gamma*bi*a*a+8)/K**2
check("physical completed diagonal, with stationarity residual",
      Mii-completed_ii-(C-gamma*Baux)/a)
check("physical action adjacent Hessian", sp.diff(action_edge(a,y),a,y)-j(a,y))
check("physical action Euler defect",
      a*sp.diff(J,a,2)+x*sp.diff(J,a,x)+y*sp.diff(J,a,y)-C+8*delta*a/K**2)

t, eps = sp.symbols("t eps", real=True)
va, vy, wa, wy = sp.symbols("va vy wa wy", real=True)
ss = a+y
beta = eps*(gamma*t/ss**2-j(a,y))
edge = gamma*eps/(2*t)*(wa+wy-2*t/ss*(va+vy))**2
edge += beta*a*y*(va/a-vy/y)**2
check("adjacent physical completed entry",
      sp.diff(edge,va,vy)/2-eps*(j(a,y)+gamma*t/ss**2))
check("adjacent mixed completed entry", sp.diff(edge,va,wy)/2+gamma*eps/ss)
check("adjacent auxiliary completed entry", sp.diff(edge,wa,wy)/2-gamma*eps/(2*t))
onsite = delta*(-gamma*bi/(bi*bi+4)*wa**2 + 4*gamma*a/K*va*wa
                -(4*gamma*bi*a*a+8)/K**2*va**2)
mixed_diag = -gamma*(ep/(x+a)+en/(a+y)-2*delta*a/K)
check("onsite and edge mixed diagonal",
      -gamma*ep/(x+a)-gamma*en/(a+y)+sp.diff(onsite,va,wa)/2-mixed_diag)

# A single turn, including the end variables and the Casimir-induced
# physical linear term (represented by ell here).
s, t, nu, A = sp.symbols("s t nu A", positive=True)
v, w, qa, qd, ell, R = sp.symbols("v w qa qd ell R", real=True)
qscale = 4*nu/gamma
unshifted = A*v*v + gamma**2*eps/(4*nu)*(
    -(w-qscale*s*v)**2/s**2 + (w-qscale*t*v)**2/t**2)
single_matrix = sp.hessian(unshifted,(v,w))/2
check("isolated physical principal diagonal", single_matrix[0,0]-A)
check("isolated mixed principal entry", single_matrix[0,1]+gamma*eps*(1/t-1/s))
check("isolated auxiliary principal diagonal",
      single_matrix[1,1]-gamma**2*eps/(4*nu)*(1/t**2-1/s**2))
h = qscale*(t-s)
kappa = gamma**2/(4*nu*eps*(t*t-s*s))
xx = sp.symbols("xx", real=True)
signed_squares = gamma**2*eps/(4*nu)*(-(xx+qa)**2/s**2+(xx-h*v+qd)**2/t**2)
xcrit = sp.solve(sp.diff(signed_squares,xx),xx)[0]
# The switch sign satisfies eps^2=1. Substitute each actual sign.
for sign in (-1,1):
    check(f"single auxiliary Schur {sign}",
          (signed_squares.subs(xx,xcrit)-kappa*(h*v+qa-qd)**2).subs(eps,sign))
q = sp.symbols("q", real=True)
single_after_aux = R+A*v*v-2*ell*v+kappa*(h*v+q)**2
vcrit = (ell-kappa*h*q)/(A+kappa*h*h)
single_residual = R+kappa*q*q-(ell-kappa*h*q)**2/(A+kappa*h*h)
check("single full Schur", single_after_aux.subs(v,vcrit)-single_residual)
check("single fixed-Casimir positive completion",
      single_residual-(R-ell*ell/A+kappa*A/(A+kappa*h*h)*(q+h*ell/A)**2))

# Adjacent turns. Here s,t,u and the positive physical matrix are
# independent symbols; the bridge sign D is never fixed in the algebra.
u = sp.symbols("u", positive=True)
D = s*s+u*u-t*t
l1,l2,A11,A12,A22 = sp.symbols("l1 l2 A11 A12 A22", real=True)
Am = sp.Matrix([[A11,A12],[A12,A22]])
lv = sp.Matrix([l1,l2])
one = sp.ones(2,1)
alpha = gamma**2/(4*nu)
Aux = alpha*(-sp.diag(1/s**2,1/u**2)+one*one.T/t**2)
Cross = -alpha*qscale/t**2*lv*one.T
Phys = Am+alpha*qscale*qscale/t**2*lv*lv.T
check("paired auxiliary determinant", Aux.det()+gamma**4*D/(16*nu**2*s*s*t*t*u*u))
check("paired physical Schur", Phys-Cross*Aux.inv()*Cross.T-Am+4*nu/D*lv*lv.T)
full = Phys.row_join(Cross).col_join(Cross.T.row_join(Aux))
det_target = gamma**4/(16*nu**2*s*s*t*t*u*u)*(
    4*nu*(lv.T*Am.adjugate()*lv)[0]-D*Am.det())
check("paired full determinant, including D=0", full.det(method="domain-ge")-det_target)

# Physical test-vector identity and the two explicit inequalities used
# for the D>0 hand inertia argument.
aa,bb,cc,dd = sp.symbols("aa bb cc dd", positive=True)
bl,bm,br = sp.symbols("bl bm br", positive=True)
At = sp.Matrix([[(bl*aa+bm*cc)/bb,-bm],[-bm,(bm*bb+br*dd)/cc]])
test = sp.Matrix([bb,cc])
check("paired physical test vector", (test.T*At*test)[0]-bl*aa*bb-br*cc*dd)
check("reverse beta upper defect", (j(aa,bb)-sp.Rational(3,16))*aa*bb
      -(aa-bb)**2/64+(aa-bb)**4/(64*(aa+bb)**2))
bridgeD = (aa+bb)**2+(cc+dd)**2-(bb+cc)**2
check("paired geometric D upper bound at equal endpoints", bridgeD.subs({aa:bb,dd:bb})-4*bb*bb)

# Smooth full bridge residual, retaining both endpoints and zeta via
# the arbitrary vector f. Its rational identity extends through D=0
# because the full block determinant above remains nonzero there.
f1,f2,z = sp.symbols("f1 f2 z", real=True)
fv = sp.Matrix([f1,f2])
Ai = Am.inv()
L = (lv.T*Ai*lv)[0]
lam = 4*nu/D
M = Am-lam*lv*lv.T
shift = fv-lam*z*lv
direct = R-lam*z*z-(shift.T*M.inv()*shift)[0]
smooth = R-(fv.T*Ai*fv)[0]+4*nu/(4*nu*L-D)*(z-(lv.T*Ai*fv)[0])**2
check("paired smooth full Schur", direct-smooth)
v1,v2,x1,x2,zz = sp.symbols("v1 v2 x1 x2 zz", real=True)
vv = sp.Matrix([v1,v2])
aux_poly = -alpha*x1*x1/s**2-alpha*x2*x2/u**2
aux_poly += alpha/t**2*(x1+x2-qscale*((lv.T*vv)[0]-zz))**2
aux_lin = sp.Matrix([sp.diff(aux_poly,x1),sp.diff(aux_poly,x2)]).subs({x1:0,x2:0})/2
xstar = -Aux.inv()*aux_lin
check("paired endpoint-retaining auxiliary Schur",
      aux_poly.subs({x1:xstar[0],x2:xstar[1]},simultaneous=True)
      +4*nu/D*((lv.T*vv)[0]-zz)**2)

P,n,m = sp.symbols("P n m", integer=True)
check("three-constraint index arithmetic",
      (2*m-((P+2*m)-2*n-1)-3+(n-m)+3).subs(P,3*n-m+1))

print(f"Python {platform.python_version()}, SymPy {sp.__version__}.")
print(f"PASS: {checks} exact mixed-turn elimination identities.")
print("Domain signs, inertia, and the full-period endpoint interface are hand arguments; F/M2 remain open.")
