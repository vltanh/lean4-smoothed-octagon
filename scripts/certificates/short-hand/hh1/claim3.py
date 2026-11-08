"""Claims with x = X0 + sx*z (z in [0,Zmax]), a = 1 + A (A in [0, c0 + c1 z]),
b = x + t (t in [Clo*A, Chi*A]), u = 3/4 + m (m in [0, mumax])."""
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import F, bernstein_cert

zz, A, t, m = sp.symbols('z A t m')
XS = sp.symbols('x al be u')
tt = sp.symbols('t')


class Claim3:
    def __init__(self, name, expr, X0, sx, Zmax, Amax, Clo, Chi, mumax, has_b=True, has_u=True):
        self.name = name; self.expr = expr
        self.X0 = Fr(X0); self.sx = sx; self.Zmax = Fr(Zmax); self.Amax = Amax
        self.Clo = Fr(Clo); self.Chi = Fr(Chi); self.mumax = Fr(mumax)
        self.has_b = has_b; self.has_u = has_u

    def build(self):
        x_, a_, b_, u_ = XS
        e = self.expr
        if self.has_b:
            e = e.subs(b_, x_ + tt)
        e = sp.together(e)
        num, den = sp.fraction(e)
        num = sp.expand(num); den = sp.factor(den)
        smp = {x_: sp.Rational(19, 10), a_: sp.Rational(11, 10), tt: sp.Rational(1, 20), u_: sp.Rational(151, 200)}
        if den.subs(smp) < 0:
            num, den = -num, -den
        self.num_x, self.den_x = num, den   # in x al t u
        X0 = sp.Rational(self.X0.numerator, self.X0.denominator)
        sub = {x_: X0 + self.sx * zz, a_: 1 + A, u_: sp.Rational(3, 4) + m, tt: t}
        P = sp.Poly(sp.expand(num.subs(sub)), zz, A, t, m)
        self.P = {mon: F(c) for mon, c in P.terms()}

    def termwise(self):
        Clo, Chi, mumax = self.Clo, self.Chi, self.mumax
        c0, c1 = self.Amax
        d = {}; T1 = []
        for (i, j, k, l), p in self.P.items():
            if k == 0:
                d[(i, j, l)] = d.get((i, j, l), Fr(0)) + p
            else:
                cc = Clo if p > 0 else Chi
                d[(i, j + k, l)] = d.get((i, j + k, l), Fr(0)) + p * cc ** k
                T1.append((i, j, k, l, p))
        e = {}; T2 = []
        for (i, j, l), v in d.items():
            if l == 0:
                e[(i, j)] = e.get((i, j), Fr(0)) + v
            else:
                e[(i, j)] = e.get((i, j), Fr(0)) + min(v, Fr(0)) * mumax ** l
                T2.append((i, j, l, v))
        H = {}; T3 = []
        for (i, j), v in e.items():
            if j == 0:
                H[i] = H.get(i, Fr(0)) + v
            else:
                if v < 0:
                    for r in range(j + 1):
                        H[i + r] = H.get(i + r, Fr(0)) + v * comb(j, r) * c0 ** (j - r) * c1 ** r
                T3.append((i, j, v))
        self.H = {i: v for i, v in H.items() if v != 0}
        self.T1, self.T2, self.T3 = T1, T2, T3

    def certify(self):
        self.build(); self.termwise()
        self.cert = bernstein_cert(self.H, self.Zmax)
        return self.cert is not None
