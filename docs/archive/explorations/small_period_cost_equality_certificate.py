#!/usr/bin/env python3
"""Exact identities for SMALL_PERIOD_COST_EQUALITY_AUDIT.md.

The finite word check stops at five pieces. It supplies terminal coverage,
not a bound on a minimizer's length. Inequality signs and the geometric
rigidity implication are proved by hand in the cited notes and audit.
No numerical optimization, Lean invocation, or external source premise.
"""
from itertools import product
import sympy as s

checks = 0

def check(name, expression):
    global checks
    values = list(expression) if isinstance(expression, s.MatrixBase) else [expression]
    residuals = [s.factor(s.together(x)) for x in values]
    if any(x != 0 for x in residuals):
        raise AssertionError((name, residuals))
    checks += 1
    print("PASS", name)

def require(name, condition):
    global checks
    if not condition:
        raise AssertionError(name)
    checks += 1
    print("PASS", name)


def canonical(word):
    return tuple((x-word[0]) % 3 for x in word)


def rebase(word, cut):
    return word[cut:] + tuple((x+1) % 3 for x in word[:cut])


def reduce_word(word):
    out = []
    for x in word:
        if not out or x != out[-1]:
            out.append(x)
    return tuple(out)


def covers_every_rebase(word):
    if set(word) != {0, 1, 2}:
        return False
    first = [word.index(j) for j in range(3)]
    last = [len(word)-1-word[::-1].index(j) for j in range(3)]
    return all(last[j] > first[(j-1) % 3] for j in range(3))


for n in range(1, 6):
    words = []
    for tail in product(range(3), repeat=n-1):
        word = (0,)+tail
        if all(word[i] != word[i+1] for i in range(n-1)):
            words.append(word)
    good = {w for w in words if covers_every_rebase(w)}
    expected = set() if n <= 3 else ({(0,1,2,0)} if n == 4 else {
        (0,1,0,2,0), (0,1,2,0,1), (0,1,2,0,2), (0,1,2,1,0),
        (0,2,0,1,2), (0,2,1,0,2), (0,2,1,2,0)})
    require(f"ordering coverage at {n} pieces", good == expected)
    require(f"ordering agrees with every arc-boundary rebase at {n} pieces",
            all(covers_every_rebase(w) == all(set(rebase(w,k)) == {0,1,2}
                                             for k in range(n)) for w in words))
require("five mixed rebasing orbit", {
    canonical(rebase((0,1,0,2,0), k)) for k in range(5)} == {
    (0,1,0,2,0), (0,2,1,2,0), (0,2,0,1,2), (0,1,2,0,2), (0,1,2,1,0)})
require("five-to-four seam merge", canonical(reduce_word(rebase((0,1,2,0,1),1))) == (0,1,2,0))
rev = (0,2,1,0,2)
require("reverse five includes the twisted reverse seam",
        all(((rev[(j+1) % 5] + (j == 4)) - rev[j]) % 3 == 2 for j in range(5)))

# The measurable-edge integration identity used by the word coverage.
x, y, z = s.symbols("x y z", real=True, nonzero=True)
edge_h = s.Matrix([[1,-x],[z,1-z*x]])
Phi = s.Matrix([[x,-x*x-y*y],[1,-x]])/y
check("fixed-edge group integration", edge_h*Phi-edge_h.diff(x)*y-edge_h.diff(z)/y)

# Four-piece rational-coordinate calculation, parametrizing a^2+b^2=1.
D = [s.Matrix([[0,-1],[-1,0]]), s.Matrix([[-1,2],[0,1]]), s.Matrix([[1,2],[0,-1]])]
R = s.Matrix([[1,-3],[1,1]])/2
for i in range(3):
    check(f"twisted label shift {i}", R.inv()*D[i]*R-D[(i+1) % 3])


def tangent(i,q):
    return (q+1/q)*s.eye(2)/2+(1/q-q)*D[i]/2


pgen,qgen,rgen,zgen = s.symbols("p q r z", positive=True)
middle4 = tangent(0,qgen)*tangent(1,rgen)
isolated4 = tangent(2,1/pgen)*R*tangent(2,1/zgen)
check("four isolated endpoint matrix", isolated4-s.Matrix([
    [pgen*zgen-zgen/(2*pgen),pgen*zgen-2*pgen/zgen-zgen/(2*pgen)],
    [zgen/(2*pgen),zgen/(2*pgen)]]))
check("four bottom row forces third factor", middle4[1,1]-middle4[1,0]
      -(qgen*qgen-(qgen*qgen-1)*rgen*rgen)/(qgen*rgen))
check("four left column forces factor relation", middle4[0,0]-middle4[1,0]-rgen/qgen)


w = s.symbols("w", positive=True)
a = (1-w*w)/(1+w*w)
b = 2*w/(1+w*w)
p, q = 1/a, 1/b
sm = a+b
N = (sm-1)*(sm+3)
M = s.Matrix([[a-b,1-2*sm],[1,b-a]])
check("four tangent endpoint", tangent(2,p)*tangent(0,q)*tangent(1,p)*tangent(2,q)-R)
H = (s.Matrix([[1,1-b],[0,b]]) * s.Matrix([[a,1-a],[0,1]])
     * s.Matrix([[1+b,b-1],[b-1,1+b]]) * s.Matrix([[1,1-a],[0,a]]))/(2*a*b)
check("four half-holonomy forces shape", R*H-(2*s.eye(2)+M)/(sm+1))
check("four shape determinant", M.det()-N)
A, B, C = 2*(sm-1), 2*(1-a+b), 2*(1+a-b)
check("four initial raw margins", s.Matrix([s.trace(d*M) for d in D])-s.Matrix([A,B,C]))
raw = [A,B,C]
expected_states = [[B,A,C],[B,C,A],[A,C,B],[C,A,B]]
la, lb = s.symbols("log_a log_b", real=True)
cost4 = 0
for j,(i,factor) in enumerate(zip([2,0,1,2],[p,q,p,q])):
    active, growing, decreasing = raw[i], raw[(i+1) % 3], raw[(i-1) % 3]
    algebra = active*((active+growing)*(factor-1)+(active+decreasing)*(1-1/factor))/8
    check(f"four arc {j+1} algebraic cost", algebra-(C*(1-a) if j % 2 == 0 else B*(1-b)))
    cost4 += algebra+active*active*(la if j % 2 == 0 else lb)/8
    raw[(i+1) % 3] = s.factor((active+growing)*factor-active)
    raw[(i-1) % 3] = s.factor((active+decreasing)/factor-active)
    check(f"four raw state after arc {j+1}", s.Matrix(raw)-s.Matrix(expected_states[j]))
check("four complete cost formula", cost4-(4*sm*(sm-1)+2*(1+a)*(1-b)*la+2*(1-a)*(1+b)*lb))

ss, dd, ll, rr, tt = s.symbols("s d log_p log_ratio t", real=True)
NN = (ss-1)*(ss+3)
f = (4*ss*(ss-1)+(3-ss*ss)*ll+2*dd*rr)/NN
fp = (s.diff(f,ss)+s.diff(f,dd)*(-ss/dd)+s.diff(f,ll)*2*ss/(ss*ss-1)
      +s.diff(f,rr)*(-2/(dd*(ss*ss-1))))
Hexpr = -(ss*ss+3)*ll-(4+ss-ss**3)*rr/dd
residual = s.together(fp-2*(Hexpr-ss*(ss-1)**3/(ss+1))/NN**2)
num, den = s.fraction(residual)
check("four derivative formula on the circle", s.rem(s.Poly(s.expand(num),dd),s.Poly(dd*dd+ss*ss-2,dd)).as_expr())
pp = (ss*ss-1)/2
integral_num = (ss*ss+3)*((2*tt+ss)*(tt+1)-2*(tt*tt+ss*tt+pp))-(4+ss-ss**3)*(tt+1)
check("four decreasing-weight integral numerator", integral_num-(ss-1)**2*(2*tt-ss*ss-1))
check("four elementary integral one", s.integrate(2*tt/(tt+1)**3,(tt,0,s.oo))-1)
check("four elementary integral two", s.integrate(1/(tt+1)**3,(tt,0,s.oo))-s.Rational(1,2))

# Five mixed pieces: independent products and raw-margin cost calculation.
u, v = s.symbols("u v", positive=True)
P = lambda t: (1+t*t)/(2*t)
Q = lambda t: (1+t*t)/(1-t*t)
factors = [P(u),Q(u),4*u*v/((1-u*u)*(1-v*v)),Q(v),P(v)]
labels = [0,1,0,2,0]
Rp = s.Matrix([[0,1],[-1,1]])

def triang(i,t):
    return [s.diag(t,1/t),s.Matrix([[1/t,t-1/t],[0,t]]),
            s.Matrix([[1/t,0],[1/t-t,t]])][i]

def halfnum(i,t):
    return [s.diag(1,t),s.Matrix([[t,1-t],[0,1]]),s.Matrix([[t,0],[t-1,1]])][i]

sgen = s.symbols("s_factor", positive=True)
middle5=triang(1,qgen)*triang(0,rgen)*triang(2,sgen)
check("five middle endpoint matrix",middle5-s.Matrix([
    [(rgen*rgen-(qgen*qgen-1)*(sgen*sgen-1))/(qgen*rgen*sgen),
     sgen*(qgen*qgen-1)/(qgen*rgen)],
    [-qgen*(sgen*sgen-1)/(rgen*sgen),qgen*sgen/rgen]]))

product_t = s.eye(2)
product_h = s.eye(2)
for i,t in zip(labels,factors):
    product_t = (product_t*triang(i,t)).applyfunc(s.factor)
    product_h = (halfnum(i,t)*product_h).applyfunc(s.factor)
check("five tangent endpoint", product_t-Rp)
check("five positive half-factor normalization", s.prod(factors)-(Q(u)*Q(v))**2)
H5 = s.Matrix([[1,-u],[v,1-u*v]])
check("five half-holonomy", product_h/(Q(u)*Q(v))-H5)
d5 = (1-u)*(1-v)
N5 = d5*(4-d5)
A5, B5 = (1+u)*(1-v), (1-u)*(1+v)
K5 = Rp*H5
Xnum = 2*K5-s.trace(K5)*s.eye(2)
Zp = [s.diag(1,-1),s.Matrix([[-1,2],[0,1]]),s.Matrix([[-1,0],[-2,1]])]
check("five forced state determinant", Xnum.det()-N5)
check("five initial raw margins", s.Matrix([-s.trace(z*Xnum) for z in Zp])-2*s.Matrix([A5,d5,B5]))
raw = [A5,d5,B5]
active_expected = [A5,d5/u,d5,d5/v,B5]
algebra5 = 0
for j,(i,t) in enumerate(zip(labels,factors)):
    active, growing, decreasing = raw[i],raw[(i+1)%3],raw[(i-1)%3]
    check(f"five active raw margin {j+1}",active-active_expected[j])
    algebra5 += active*((active+growing)*(t-1)+(active+decreasing)*(1-1/t))/2
    raw[(i+1)%3] = s.factor((active+growing)*t-active)
    raw[(i-1)%3] = s.factor((active+decreasing)/t-active)
check("five terminal raw twist",s.Matrix(raw)-s.Matrix([B5,A5,d5]))
check("five algebraic cost cancellation",algebra5-2*d5*(d5+2))
check("five first logarithmic coefficient",A5*A5/d5**2-((1+u)/(1-u))**2)
check("five last logarithmic coefficient",B5*B5/d5**2-((1+v)/(1-v))**2)
check("five middle positivity factorization",4*u*v-(1-u*u)*(1-v*v)-(u+v-1+u*v)*(u+v+1-u*v))

# The scalar logarithmic envelope and comparison identities.
t = s.symbols("t", positive=True)
E = t-1-s.log(t)
h = -2*t*s.log(t)/(1-t)-s.log(1+t)
check("envelope first derivative",s.diff(h,t)-2*E/(1-t)**2+1/(1+t))
check("envelope concavity numerator",t*s.diff(h,t,2)-s.diff(h,t)
      -(-2/(1-t)+2*(3*t-1)*E/(1-t)**3+(1+2*t)/(1+t)**2))
check("envelope upper estimate",-2/(1-t)+(3*t-1)/(t*(1-t))+(1+2*t)/(1+t)**2
      -(t*t-t-1)/(t*(1+t)**2))
aa, bb = 2*t/(1+t*t),(1-t*t)/(1+t*t)
check("envelope unit circle",aa*aa+bb*bb-1)
check("envelope log a coefficient",1-((1+t)/(1-t))**2+2*aa/(1-aa))
check("envelope log b coefficient",-1-1/(t*t)+2*bb/(1-bb)+2)
check("envelope residual logarithm product",((1-t)/bb)**2*(1+aa)*(1+bb)-2)
Mconst, d = s.symbols("M d", positive=True)
Bd = (2*(d+2)-d*(Mconst-s.log(d)))/(4-d)
check("five scalar bound derivative",s.diff(Bd,d)-(4*(4-Mconst+s.log(d))-d)/(4-d)**2)
check("log two rational lower polynomial integral",2*s.integrate(1+t*t,(t,0,s.Rational(1,3)))-s.Rational(56,81))
require("strict rational threshold exceeds four",s.Rational(29,5)*s.Rational(56,81)>4)

root2 = s.sqrt(2)
tstar = root2-1
dstar = (2-root2)**2
L2 = s.symbols("log_two", real=True)
check("five equality factors P",P(tstar)-root2)
check("five equality factors Q",Q(tstar)-root2)
check("five equality middle factor",4*tstar*tstar/(1-tstar*tstar)**2-1)
check("five envelope maximum coefficient",(((1+tstar)/(1-tstar))**2+1/tstar**2)/2-(3+2*root2))
check("five boundary cancellation",dstar*(3+2*root2)-2)
delta_oct = (8-4*root2-L2)/(2*root2-1)
check("five boundary equals octagon",(2*(dstar+2)-dstar*(3+2*root2)*L2)/(4-dstar)-delta_oct)
Nstar = 2*root2-1
astar = bstar = 1/root2
coststar = (4*root2*(root2-1)-(1+astar)*(1-bstar)*L2
            -(1-astar)*(1+bstar)*L2)/Nstar
check("four equality equals octagon",coststar-delta_oct)
check("four equality shape normalization",(root2-1)*(root2+3)-Nstar)
check("four equality physical duration",(2/s.sqrt(Nstar))/2*(L2/2)-L2/(2*s.sqrt(Nstar)))
print(f"{checks} exact checks passed")
