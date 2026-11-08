"""Exact identities for the competitive reverse-centre scale bound.

The inequalities and actual whole-period interface are proved in
docs/MIXED_REVERSE_CENTRE_SCALE_BOUND.md. No numerical sampling,
Lean, Lake, typechecking, CI, or remaining-case closure claim.
"""

import sympy as s

r, t, rho, u, v, x = s.symbols('r t rho u v x', positive=True)
U = lambda z: 1-z+z*z
E = 1+r+t-rho+s.log(rho/(r*t))-(1-u)/r-(1-v)/t
Gamma = (4*u*v-E*E)/(16*(1-rho)**2)
checks = 0


def check(name, lhs, rhs=0):
    global checks
    if s.simplify(lhs-rhs) != 0:
        raise AssertionError(name)
    checks += 1


upper = -1+2*r+2*t-rho+s.log(rho/(r*t))
check('upper norm corner', E.subs({u: U(r), v: U(t)}), upper)
check('upper rho derivative', s.diff(-rho+s.log(rho/(r*t)), rho),
      1/rho-1)
check('strict r comparison', upper.subs(rho, r*t)-s.Rational(3, 2)*r,
      (2-r)*(t-s.Rational(1, 2)))
check('norm u derivative', s.diff(Gamma, u),
      (4*v-2*E/r)/(16*(1-rho)**2))
check('norm v derivative', s.diff(Gamma, v),
      (4*u-2*E/t)/(16*(1-rho)**2))
E0 = E.subs({u: s.Rational(3, 4), v: s.Rational(3, 4)})
check('ratio r derivative', s.diff(E0, r), (2*r-1)**2/(4*r*r))
check('ratio t derivative', s.diff(E0, t), (2*t-1)**2/(4*t*t))
boundary = 1-rho+(1-1/(4*rho))*r+(rho-s.Rational(1, 4))/r
check('product boundary', E0.subs(t, rho/r), boundary)
check('product boundary concavity', s.diff(boundary, r, 2),
      2*(rho-s.Rational(1, 4))/r**3)
lower = 1+rho-1/(8*rho)
check('left product endpoint', boundary.subs(r, 2*rho), lower)
check('right product endpoint', boundary.subs(r, s.Rational(1, 2)), lower)
check('lower scale derivative', s.diff(lower, rho), 1+1/(8*rho*rho))
check('positive lower endpoint', lower.subs(rho, s.Rational(3, 20)),
      s.Rational(19, 60))
B = 1-rho+s.log(4*rho)
check('equal ratio corner', E0.subs({r: s.Rational(1, 2),
                                  t: s.Rational(1, 2)}), B)
G = (s.Rational(9, 4)-B*B)/(16*(1-rho)**2)
numerator = s.Rational(9, 4)-B*B-B*(1-rho)**2/rho
check('one-variable derivative', s.diff(G, rho),
      numerator/(8*(1-rho)**3))
log_upper = 2*(x-1)/(x+1)
check('log upper derivative', s.diff(log_upper-s.log(x), x),
      -(x-1)**2/(x*(x+1)**2))
Bhat = (-4*rho*rho+11*rho-1)/(4*rho+1)
check('rational log substitution', 1-rho+log_upper.subs(x, 4*rho), Bhat)
check('positive derivative numerator',
      s.Rational(9, 4)-Bhat*Bhat-Bhat*(1-rho)**2/rho,
      (4*rho-1)**2*(4*rho*rho+rho+4)/(4*rho*(4*rho+1)**2))
check('cutoff log bound', log_upper.subs(x, s.Rational(3, 5)),
      -s.Rational(1, 2))
check('cutoff determinant bound',
      (s.Rational(9, 4)-s.Rational(7, 20)**2)
      /(16*s.Rational(17, 20)**2), s.Rational(851, 4624))
check('strict rational separation', s.Rational(851, 4624)-s.Rational(23, 125),
      s.Rational(23, 578000))
check('physical active scale', (4*rho/(1-rho)).subs(rho, s.Rational(3, 20)),
      s.Rational(12, 17))

if __name__ == '__main__':
    print(f'All {checks} exact reverse-centre scale identities passed.')
