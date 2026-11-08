"""Central face (q = q_c) atoms and claim expressions, sympy side, mirroring the Lean forms."""
import sympy as sp

x, a, b, u = sp.symbols('x al be u')
c = sp.Rational(7, 96)
S = 1 + x
X = x * (x + 2)
K = X + a ** 2
D = a ** 2 + 2 * a * b + 1 + 2 * x - 2 * b * x
lam = S ** 2 / K
d = D / K
v = 1 - 1 / S + 1 / S ** 2
E = S * (u - 1) + 1 / S + (2 * S - 1) / S ** 2
w = lam ** 2 * v + d ** 2 * u - d * lam * E
EL = 2 * d * u - lam * E
G = (4 * u * v - E ** 2) * S ** 4 / (16 * X ** 2)
q = a ** 2 / K
B = a + b
T = K / (a * B)

# u-derivatives (exact; R2 and w affine in u)
Gu = (4 * v - 2 * S * E) * S ** 4 / (16 * X ** 2)
R2u = 2 * (d ** 2 - d * lam * S) + B / a - (2 * d - lam * S)
wu = d ** 2 - d * lam * S
# beta-derivatives at fixed u (log version of the ell term)
db = 2 * (a - x) / K
wb = 2 * d * db * u - db * lam * E
ELb = 2 * db * u
R2b = 2 * wb - ELb + (u - 1) / a - a / B ** 2 + 1 / B
Tb = -K / (a * B ** 2)
R1b = R2b + Tb * (w - sp.Rational(3, 4)) + (T - 2) * wb
# alpha-derivatives at fixed beta, u
Ka = 2 * a
la = -2 * a * S ** 2 / K ** 2
da = 2 * B / K - 2 * a * D / K ** 2
qa = 2 * a / K - 2 * a ** 3 / K ** 2
wa = 2 * lam * la * v + 2 * d * da * u - (da * lam + d * la) * E
ELa = 2 * da * u - la * E
ya_over_y = 1 / a + 1 / B - 2 * a / K   # (log y)_a, y = 2 a B / K
R2a = 2 * wa - ELa - (u - 1) * b / a ** 2 + b / B ** 2 - qa + ya_over_y
# x-derivatives at fixed alpha, beta, u
Kx = 2 * S
lx = 2 * S / K - S ** 2 * Kx / K ** 2
Dx = 2 - 2 * b
dx = Dx / K - D * Kx / K ** 2
vx = 1 / S ** 2 - 2 / S ** 3
Ex = (u - 1) - 1 / S ** 2 + 2 / S ** 2 - 2 * (2 * S - 1) / S ** 3
wx = 2 * lam * lx * v + lam ** 2 * vx + 2 * d * dx * u - (dx * lam + d * lx) * E - d * lam * Ex
ELx = 2 * dx * u - lx * E - lam * Ex
qx = -a ** 2 * Kx / K ** 2
yx_over_y = -Kx / K
R2x = 2 * wx - ELx - qx + yx_over_y
Tx = Kx / (a * B)
R1x = R2x + Tx * (w - sp.Rational(3, 4)) + (T - 2) * wx
Gx = sp.diff(G, x)

claims = {
    # u-step: -F_u(3/4) >= 0
    'U0': (c * R2u - Gu).subs(u, sp.Rational(3, 4)),
    'U1': (c * (R2u + (T - 2) * wu) - Gu).subs(u, sp.Rational(3, 4)),
    # bound on -F0_u from above (for the beta and alpha steps): 1/2 - (c R2u - Gu) >= 0
    'M0': sp.Rational(1, 5) - (c * R2u - Gu),
    'B0': R2b - sp.Rational(1, 40),
    'B1': R1b - sp.Rational(1, 50),
    'A0': R2a + sp.Rational(10, 13) * R2b - sp.Rational(1, 30),
}
Lx = sp.Rational(-286, 100000) - sp.Rational(118, 10000) * (x - sp.Rational(8, 5)) - sp.Rational(75, 10000) * (x - sp.Rational(8, 5)) * (x - sp.Rational(9, 5))
claims['X1a'] = c * (R1x + R1b) - Lx
claims['X1b'] = Lx - Gx
