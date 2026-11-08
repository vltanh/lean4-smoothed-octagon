"""Outer face (q = 1/7) atoms and claim expressions (sympy), mirroring S1ODefs / S1ODeriv."""
import sympy as sp, pickle
x, a, b, u = sp.symbols('x al be u')
C = sp.symbols('C')
c = sp.Rational(7, 96)
S = 1 + x; K = 6 * a ** 2 + 1; L = K / (7 * a ** 2)
D = a ** 2 + 2 * a * b + 1 + 2 * x - 2 * b * x; d = D / (7 * a ** 2)
v = 1 - S / K + (S / K) ** 2; E = S * (u - 1) + 1 / S + (2 * S - 1) / K
w = L ** 2 * v + d ** 2 * u - d * L * E; EL = 2 * d * u - L * E
G = (4 * u * v - E ** 2) * K ** 2 / (576 * a ** 4)
T = 7 * a / (a + b)
La = -2 / (7 * a ** 3); da = 2 * (a + b) / (7 * a ** 2) - 2 * d / a; db = 2 * (a - x) / (7 * a ** 2)
va = S * 12 * a / K ** 2 - 2 * S ** 2 * 12 * a / K ** 3; Ea = -(2 * S - 1) * 12 * a / K ** 2
wa = 2 * L * La * v + L ** 2 * va + 2 * d * da * u - (da * L + d * La) * E - d * L * Ea
wb = 2 * d * db * u - db * L * E; wu = d ** 2 - d * L * S
ELa = 2 * da * u - La * E - L * Ea
R2a = 2 * wa - ELa - (u - 1) * b / a ** 2 + b / (a + b) ** 2 + (1 / (a + b) - 1 / a)
R2b = 2 * wb - 2 * db * u + (u - 1) / a - a / (a + b) ** 2 + 1 / (a + b)
R2u = 2 * wu + (a + b) / a - (2 * d - L * S)
Ta = 7 * b / (a + b) ** 2; Tb = -7 * a / (a + b) ** 2
R1a = R2a + Ta * (w - sp.Rational(3, 4)) + (T - 2) * wa
R1b = R2b + Tb * (w - sp.Rational(3, 4)) + (T - 2) * wb
R1u = R2u + (T - 2) * wu
Ga = (4 * u * va - 2 * E * Ea) * K ** 2 / (576 * a ** 4) + (4 * u * v - E ** 2) * (24 * a * K / (576 * a ** 4) - 4 * K ** 2 / (576 * a ** 5))
Gu = (4 * v - 2 * S * E) * K ** 2 / (576 * a ** 4)
