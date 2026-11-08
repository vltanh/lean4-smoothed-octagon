"""Exact algebra for the equal-centre short-bridge hand proof.

No numerical sampling, Lean, Lake, typechecking, or CI. The surrounding
hand argument supplies domains, comparison directions, and endpoints.
"""
import sympy as s

checks = 0


def check(name, lhs, rhs=0):
    global checks
    expression = (lhs-rhs).replace(
        lambda e: e.func == s.log,
        lambda e: s.log(s.factor(e.args[0])))
    value = s.factor(s.expand_log(expression, force=True))
    if value != 0:
        raise AssertionError((name, value))
    checks += 1


x, y, rho, z, t = s.symbols('x y rho z t', positive=True)
uu, vv, ee, dd, FF, ww = s.symbols('u v E d F w', real=True)
U = lambda r: 1-r+r*r
V = lambda q: 1+q/(2*(1+q))-q*s.log(2*q/(1+q))/(q-1)
f = lambda q: q-1/q-s.log(q)
h = lambda q: s.log(q)-1+1/q
G = lambda q, v: v*q-f(q)
D = 2+4*x-2*x*x
r, q = 1/(1+x), 1/(1+y)
u, v = V(x), V(y)
E = 1+r+q-rho+s.log(rho/(r*q))-(1-u)/r-(1-v)/q
d = rho*D
F = E-d*u
Fb = F.subs(rho, r*q)
delta = U(q)-v
H = Fb+(1+y)*delta/2

check('primitive derivative', s.diff(f(t),t), U(1/t))
check('primitive convexity', s.diff(f(t),t,2), (t-2)/t**3)
check('turn derivative', s.diff(u,x), (U(r)-u)/(x*(x-1)))
check('turn derivative upper numerator', U(r)-s.Rational(3,4), (x-1)**2/(4*(1+x)**2))
check('turn limit', s.limit(u,x,1), s.Rational(3,4))
check('turn alternative form', u.subs(x,z/(2-z)), 1+z/4-z*s.log(z)/(2*(z-1)))
turnz = 1+z/4-z*s.log(z)/(2*(z-1))
check('turn alternative derivative', s.diff(turnz,z), s.Rational(1,4)-(z-1-s.log(z))/(2*(z-1)**2))
check('log lower remainder derivative', s.diff(s.log(z)-(z-1)+(z-1)**2/2,z), (z-1)**2/z)
check('bridge diagonal bound', D, 4-2*(x-1)**2)
check('bridge diagonal derivative', s.diff(D,x), -4*(x-1))
check('turn diagonal product limit', s.limit(u*D,x,1), 3)
check('central primitive identity', E, G(1+x,u)+G(1+y,v)-h(1/rho))
check('central scale derivative', s.diff(F,rho), 1/rho-1-D*u)
check('Gram norm recurrence', dd**2*uu+vv-dd*ee, vv-dd*(ee-dd*uu))
check('Gram pairing recurrence', 2*dd*uu-ee, dd*uu-(ee-dd*uu))
check('near-turn differential identity', v+(1+y)*s.diff(v,y)-U(q), (1+2*y-y*y)*s.diff(v,y))
check('zero-factor central derivative', s.diff(Fb,y), -q+r*q*q*(1+u*D)+(1+2*y-y*y)*s.diff(v,y))
check('strong residual derivative', s.diff(H,y), -q/2+q*q*(r*(1+u*D)-1)+(1+2*y-y*y)*s.diff(v,y)/2)
check('strong derivative upper bound', -q/2+q*q+(y-1)/(4*y*(1+y)**2), -(y-1)*q*q*(s.Rational(1,2)-1/(4*y)))

xx = (1+z)/(1-z)
uz = s.Rational(5,4)+z/4-(1+z)*s.log(1+z)/(2*z)
check('diagonal turn transform', u.subs(x,xx), uz)
Fsym = (1+z)**2*(-2*z*z*s.log(1+z)+6*s.log(1+z)+z**3+3*z*z-6*z)/(4*z*(z-1))
check('diagonal central residual', Fb.subs(y,x).subs(x,xx), Fsym)
loglower = 2*z/(2+z)+s.Rational(2,3)*(z/(2+z))**3
Fbound = -z*z*(1+z)**2*(3*z**3+11*z*z+24*z+24)/(12*(1-z)*(z+2)**3)
check('diagonal rational logarithm bound', Fsym.subs(s.log(1+z),loglower), Fbound)
check('diagonal norm gap bound', (1+xx)*(U((1-z)/2)-s.Rational(3,4))/2, z*z/(4*(1-z)))
poly = 3*z**5+17*z**4+46*z**3+65*z*z+36*z
check('strong diagonal residual bound', Fbound+z*z/(4*(1-z)), -z*z*poly/(12*(1-z)*(z+2)**3))
if any(c <= 0 for c in s.Poly(poly,z).coeffs()):
    raise AssertionError('displayed diagonal coefficients must be positive')
checks += 1

# Legendre identities use t>2 and w=f'(t), so no radical simplification
# or implicit branch choice is concealed in the algebra.
wt = U(1/t)
Lt = s.log(t)-1+2/t
check('Legendre value at derivative', G(t,wt), Lt)
check('Legendre derivative by parametrization', s.diff(Lt,t), t*s.diff(wt,t))
check('Legendre lower endpoint', Lt.subs(t,2), s.log(2))
check('derivative distance from lower endpoint', wt-s.Rational(3,4), (t-2)**2/(4*t*t))
m = 4*t*t*(s.log(t/2)-1+2/t)/(t-2)**2
check('Legendre chord slope', m*(wt-s.Rational(3,4)), Lt-s.log(2))
check('Legendre chord identity', s.log(2)+m*(vv-s.Rational(3,4))-G(t,vv), (t-m)*(wt-vv))
check('bridge times scale bound', 2-D/(1+x), 2*x*(x-1)/(1+x))
Fp = s.symbols('Fp', real=True)
check('outer residual derivative', t*(-D*FF-dd*Fp)+2*Fp, (2-dd*t)*Fp-D*t*FF)
T0 = s.symbols('T0', positive=True)
check('reverse derivative boundary residual', Lt-G(T0,vv)+2*(vv-wt)/dd, G(t,vv)-G(T0,vv)-(2/dd-t)*(wt-vv))
de = s.symbols('delta', positive=True)
check('central chord boundary bound', (t-m)*de+(2-m*dd)*(-t*de/2), -m*(1-dd*t/2)*de)

print(f'All {checks} exact equal-centre identities and coefficient checks passed.')
