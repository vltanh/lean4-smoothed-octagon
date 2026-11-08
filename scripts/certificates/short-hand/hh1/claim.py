import re
"""Generator of polynomial sign claims for gate S1 (hh1).

A claim is `0 ≤ E(x, a, b, u)` (E rational, given both as a sympy expression and as a Lean
expression string in the variables x a b u) on a domain

    x = X0 + sx*z, z in [0, Zmax]          (sx = +1 or -1)
    a = 1 + A,     A in [0, Amax(z)]      (Amax affine in z, or constant)
    b = x + C0*A + s, |s| <= tmax*A
    u = 3/4 + mu,  mu in [0, mumax]

Proof: E * den = P(z, A, s, mu) (field_simp; ring), then the hierarchical termwise bound
P >= H(z) (s-level, mu-level, A-level), then a Bernstein certificate for H >= 0 on [0, Zmax].
"""
import sympy as sp
from fractions import Fraction as Fr
from math import comb

z, A, s, mu = sp.symbols('z A s mu')


def F(r):
    r = sp.Rational(r)
    return Fr(int(r.p), int(r.q))


def lq(fr):
    """Lean real literal for a Fraction (parenthesized if needed)."""
    fr = Fr(fr)
    if fr.denominator == 1:
        return f"({fr.numerator} : ℝ)" if fr.numerator < 0 else f"{fr.numerator}"
    if fr.numerator < 0:
        return f"(-{-fr.numerator} / {fr.denominator} : ℝ)"
    return f"({fr.numerator} / {fr.denominator} : ℝ)"


def lmono(i, j, k, l):
    parts = []
    for v, e in (('z', i), ('A', j), ('s', k), ('mu', l)):
        if e == 1:
            parts.append(v)
        elif e > 1:
            parts.append(f"{v} ^ ({e} : ℕ)")
    return " * ".join(parts) if parts else "1"


def lpoly_terms(terms):
    """terms: list of (Fraction coeff, lean monomial string)."""
    out = []
    for c, m in terms:
        if c == 0:
            continue
        cs = lq(abs(c))
        t = cs if m == "1" else (m if abs(c) == 1 else f"{cs} * {m}")
        out.append(('-' if c < 0 else '+', t))
    if not out:
        return "0"
    s0 = ('-' if out[0][0] == '-' else '') + out[0][1]
    for sg, t in out[1:]:
        s0 += f" {sg} {t}"
    return s0


def bernstein_cert(H, Z, depth=0, maxdepth=12):
    """H: dict i->Fraction (polynomial in z) on [0, Z]. Returns list of intervals (z0,z1)
    on each of which the Bernstein coefficients of H(z0 + w), w in [0, z1-z0], are all > 0
    (or >= 0 with positive endpoint values), or None."""
    def shift(H, z0):
        n = max(H) if H else 0
        out = {}
        for i, c in H.items():
            for k in range(i + 1):
                out[k] = out.get(k, Fr(0)) + c * comb(i, k) * z0 ** (i - k)
        return out

    def bcoeffs(Hs, W):
        n = max(Hs) if Hs else 0
        bs = []
        for k in range(n + 1):
            bs.append(sum(Fr(comb(k, i), comb(n, i)) * Hs.get(i, Fr(0)) * W ** i for i in range(k + 1)))
        return bs

    res = []

    def rec(z0, z1, d):
        Hs = shift(H, z0)
        bs = bcoeffs(Hs, z1 - z0)
        if all(b > 0 for b in bs):
            res.append((z0, z1))
            return True
        if d >= maxdepth:
            return False
        m = (z0 + z1) / 2
        return rec(z0, m, d + 1) and rec(m, z1, d + 1)

    ok = rec(Fr(0), Fr(Z), 0)
    return res if ok else None


class Claim:
    def __init__(self, name, expr, lean_expr, X0, sx, Zmax, Amax, C0, tmax, mumax,
                 has_b=True, has_u=True, strict=False, extra_hyps=None, doc=""):
        self.name = name
        self.expr = expr
        self.lean_expr = lean_expr
        self.X0 = Fr(X0); self.sx = sx; self.Zmax = Fr(Zmax)
        self.Amax = Amax  # (c0, c1): Amax(z) = c0 + c1*z, Fractions
        self.C0 = Fr(C0); self.tmax = Fr(tmax); self.mumax = Fr(mumax)
        self.has_b = has_b; self.has_u = has_u
        self.strict = strict
        self.doc = doc

    def build(self):
        x_, a_, b_, u_ = sp.symbols('x al be u')
        X0, sx, C0 = self.X0, self.sx, self.C0
        xs = sp.Rational(X0.numerator, X0.denominator) + sx * z
        sub = {x_: xs, a_: 1 + A}
        if self.has_b:
            sub[b_] = xs + sp.Rational(C0.numerator, C0.denominator) * A + s
        if self.has_u:
            sub[u_] = sp.Rational(3, 4) + mu
        e = sp.together(self.expr)
        num, den = sp.fraction(e)
        num = sp.expand(num)
        den = sp.factor(den)
        smp = {x_: sp.Rational(19, 10), a_: sp.Rational(11, 10), b_: sp.Rational(2), u_: sp.Rational(151, 200)}
        if den.subs(smp) < 0:
            num, den = -num, -den
        self.num_x = num
        self.den_x = den
        num = sp.expand(num.subs(sub))
        self.num = num
        self.den = den
        P = sp.Poly(num, z, A, s, mu)
        self.P = {mon: F(c) for mon, c in P.terms()}
        return self

    def termwise(self):
        P, tmax, mumax = self.P, self.tmax, self.mumax
        c0, c1 = self.Amax
        # s level
        d = {}
        T1 = []  # (i,j,k,l,p)
        for (i, j, k, l), p in P.items():
            if k == 0:
                d[(i, j, l)] = d.get((i, j, l), Fr(0)) + p
            else:
                d[(i, j + k, l)] = d.get((i, j + k, l), Fr(0)) - abs(p) * tmax ** k
                T1.append((i, j, k, l, p))
        e = {}
        T2 = []
        for (i, j, l), v in d.items():
            if l == 0:
                e[(i, j)] = e.get((i, j), Fr(0)) + v
            else:
                e[(i, j)] = e.get((i, j), Fr(0)) + min(v, Fr(0)) * mumax ** l
                T2.append((i, j, l, v))
        H = {}
        T3 = []
        for (i, j), v in e.items():
            if j == 0:
                H[i] = H.get(i, Fr(0)) + v
            else:
                if v < 0:
                    # v * Amax(z)^j * z^i
                    for r in range(j + 1):
                        cf = v * comb(j, r) * c0 ** (j - r) * c1 ** r
                        H[i + r] = H.get(i + r, Fr(0)) + cf
                T3.append((i, j, v))
        self.H = {i: v for i, v in H.items() if v != 0}
        self.T1, self.T2, self.T3 = T1, T2, T3
        return self.H

    def certify(self):
        self.build()
        H = self.termwise()
        cert = bernstein_cert(H, self.Zmax)
        self.cert = cert
        return cert is not None
