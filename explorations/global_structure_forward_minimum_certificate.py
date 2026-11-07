"""Exact checks for GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md.

Run: python3 explorations/global_structure_forward_minimum_certificate.py
No floating-point sampling, Lean, Lake, typechecking, or CI.
The comparison paths and actual PMP/endpoints are the hand proof.
"""
import sympy as s

count = 0


def eq(name, expression):
    global count
    assert s.simplify(expression) == 0, name
    count += 1


def positive(name, expression):
    global count
    assert expression > 0, name
    count += 1


R = s.Rational
positive('sqrt2 lower', 2 * 100000**2 - 141421**2)
positive('sqrt3 upper', 173206**2 - 3 * 100000**2)
log_lower = sum(R(2, (2*j+1)*3**(2*j+1)) for j in range(5))
eq('log lower value', log_lower - R(4297606, 6200145))
positive('log lower comparison', log_lower - R(69314, 100000))
oct_upper = (2*R(173206, 100000)
             * (8-4*R(141421, 100000)-R(69314, 100000))
             / (2*R(141421, 100000)-1))
eq('octagon rational value', oct_upper - R(649530373, 207775000))
positive('octagon upper comparison', R(2501, 800) - oct_upper)
pi_lower = 16*(R(1, 5)-R(1, 3*5**3)+R(1, 5*5**5)-R(1, 7*5**7))-R(4, 239)
eq('pi rational value', pi_lower - R(1231847548, 392109375))
positive('pi lower comparison', pi_lower - R(6283, 2000))
kappa_upper = 3*R(2501, 800)/(4*R(6283, 2000)-2*R(2501, 800))
eq('kappa upper value', kappa_upper - R(205, 138))
eq('Casimir rational difference', R(23, 125)-kappa_upper**2/12-R(3019, 28566000))
positive('Casimir rational comparison', R(23, 125)-kappa_upper**2/12)
positive('minimum cost comparison', R(27853, 8800)-R(313, 100))
positive('log 5/4 upper comparison', R(9, 40)-R(43, 192))
eq('minimum scale', R(20, 11)/(R(20, 11)+4)-R(5, 16))

r, t, x, u, v = s.symbols('r t x u v', positive=True)
U = lambda z: 1-z+z*z
E = 1+r+t-x+s.log(x/(r*t))-(1-u)/r-(1-v)/t
D = 4*u*v-E*E
G = E-3*x
F = D-3*(1-x)**2
eq('G derivative', s.diff(G, x)-(1/x-4))
eq('F derivative', s.diff(F, x)+2*(1-x)*G/x)
B0 = -1+2*r+2*t-r*t
eq('boundary identity', 4*U(r)*U(t)-B0*B0-3*(1-r*t)**2)
eq('u derivative', s.diff(D, u)-(4*v-2*E/r))
eq('switch floor polynomial', 4*U(t)-6*t-2*(2*t-1)*(t-2))
z = R(23, 125)
eq('lower endpoint value', 9*z+16*z*z-R(34339, 15625))
eq('upper endpoint value', R(121, 16)*z+25*z*z-R(22379, 10000))
positive('lower endpoint gap', R(9, 4)-R(34339, 15625))
positive('upper endpoint gap', R(9, 4)-R(22379, 10000))

a, b, gamma = s.symbols('a b gamma', positive=True)
K = a*a+4
onsite = s.Matrix([[-(4*gamma*b*a*a+8)/K**2, 2*gamma*a/K],
                   [2*gamma*a/K, -gamma*b/(b*b+4)]])
eq('onsite determinant', onsite.det()-8*gamma*(b-2*gamma*a*a)/(K*K*(b*b+4)))
print(f'All {count} exact identities and rational signs passed.')
