"""General termwise claim: 0 <= E(vars), vars = main x (x = X0 + sx*z, z in [0,Zmax]) and
termwise variables v_i = lo_i + w_i, w_i in [0, hi_i(z)] with hi_i affine in z (c0 + c1 z).
Hierarchical termwise bound over w_k, ..., w_1 (last listed is innermost), then Bernstein in z."""
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import F, bernstein_cert

zz = sp.symbols('z')


class ClaimG:
    def __init__(self, expr, xsym, X0, sx, Zmax, tvars, allow_zero=False):
        # tvars: list of (sym, lo, (c0, c1)) ; variable = lo + w, w in [0, c0 + c1 z]
        self.expr = expr; self.xsym = xsym
        self.X0 = Fr(X0); self.sx = sx; self.Zmax = Fr(Zmax); self.tvars = tvars
        self.allow_zero = allow_zero

    def build(self):
        e = sp.together(self.expr)
        num, den = sp.fraction(e)
        num = sp.expand(num); den = sp.factor(den)
        self.num_x, self.den_x = num, den
        self.ws = sp.symbols(' '.join(f'w{i}' for i in range(len(self.tvars))))
        if len(self.tvars) == 1: self.ws = (self.ws,)
        sub = {self.xsym: sp.Rational(self.X0.numerator, self.X0.denominator) + self.sx * zz}
        for (s_, lo, _), w in zip(self.tvars, self.ws):
            sub[s_] = sp.Rational(Fr(lo).numerator, Fr(lo).denominator) + w
        P = sp.Poly(sp.expand(num.subs(sub)), zz, *self.ws)
        self.P = {mon: F(c) for mon, c in P.terms()}

    def termwise(self):
        # process innermost (last) variable first
        cur = dict(self.P)  # key: (i, j1..jk)
        nv = len(self.tvars)
        self.levels = []
        for lev in range(nv - 1, -1, -1):
            c0, c1 = self.tvars[lev][2]
            new = {}
            T = []
            for key, v in cur.items():
                j = key[1 + lev]
                base = key[:1 + lev]  # drop this and inner vars (inner already dropped)
                if j == 0:
                    new[base] = new.get(base, Fr(0)) + v
                else:
                    T.append((key, v))
                    if v < 0:
                        # v * w^j >= v * hi(z)^j ; hi = c0 + c1 z expands into z powers
                        for rr in range(j + 1):
                            cf = v * comb(j, rr) * c0 ** (j - rr) * c1 ** rr
                            nb = (base[0] + rr,) + base[1:]
                            new[nb] = new.get(nb, Fr(0)) + cf
            self.levels.append((lev, T))
            cur = new
        self.H = {k[0]: v for k, v in cur.items() if v != 0}

    def certify(self):
        self.build(); self.termwise()
        self.cert = bernstein_cert(self.H, self.Zmax)
        if self.cert is None and self.allow_zero:
            # allow b0 = 0 exactly
            pass
        return self.cert is not None
