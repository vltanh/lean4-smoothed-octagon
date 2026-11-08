"""Planning of nested Bernstein certificates (fast, Fraction arithmetic)."""
from fractions import Fraction as Fr
from math import comb
import sympy as sp

def F(c):
    c = sp.Rational(c); return Fr(int(c.p), int(c.q))

def to_dict(expr, vars_):
    P = sp.Poly(sp.expand(expr), *vars_)
    return {m: F(c) for m, c in P.terms()}

def bern1(cs, lo, hi):
    n = len(cs)-1; hgt = hi - lo
    u = [Fr(0)]*(n+1)
    for jj, c in enumerate(cs):
        if c == 0: continue
        for i in range(jj+1):
            u[i] += c * comb(jj, i) * lo**(jj-i) * hgt**i
    return [sum((Fr(comb(kk, i), comb(n, i)) * u[i] for i in range(kk+1)), Fr(0)) for kk in range(n+1)]

def uni_ok(cs, lo, hi, depth=0, maxdepth=12):
    """number of leaves if positive on [lo,hi] by subdivision, else None"""
    while len(cs) > 1 and cs[-1] == 0: cs = cs[:-1]
    b = bern1(cs, lo, hi)
    if min(b) > 0: return 1
    if depth >= maxdepth or b[0] <= 0 or b[-1] <= 0: return None
    mid = (lo+hi)/2
    a = uni_ok(cs, lo, mid, depth+1, maxdepth)
    if a is None: return None
    c = uni_ok(cs, mid, hi, depth+1, maxdepth)
    if c is None: return None
    return a + c

def poly_in(d, idx, n):
    """split dict over variable idx -> list of dicts over remaining vars"""
    out = [dict() for _ in range(n+1)]
    for m, c in d.items():
        e = m[idx]; rest = m[:idx] + m[idx+1:]
        out[e][rest] = out[e].get(rest, Fr(0)) + c
    return out

def padd(a, b, s=1):
    r = dict(a)
    for m, c in b.items():
        r[m] = r.get(m, Fr(0)) + s*c
        if r[m] == 0: del r[m]
    return r
def pmul(a, b):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x+y for x, y in zip(m1, m2))
            r[m] = r.get(m, Fr(0)) + c1*c2
    return {m:c for m,c in r.items() if c != 0}
def pscale(a, s): return {m: c*s for m, c in a.items() if c*s != 0}

def bern_inner(d, nv, idx, lo, hi, deg):
    """d: dict poly in nv vars; Bernstein in var idx over [lo, hi] where lo, hi are dicts in the other
    nv-1 vars (or Fractions). returns list of deg+1 dicts (in other vars) gamma_k with
    (hi-lo)^deg * P = sum_k gamma_k * C(deg,k) (v-lo)^k (hi-v)^(deg-k)  -- gamma includes binomial."""
    m = nv - 1
    one = {tuple([0]*m): Fr(1)}
    if not isinstance(lo, dict): lo = {tuple([0]*m): Fr(lo)} if lo != 0 else {}
    if not isinstance(hi, dict): hi = {tuple([0]*m): Fr(hi)} if hi != 0 else {}
    H = padd(hi, lo, -1)
    cs = poly_in(d, idx, max([mm[idx] for mm in d] + [0]))
    n = len(cs) - 1
    assert deg >= n
    # P(lo + H w) = sum_j cs_j (lo + H w)^j ; coefficient a_i (dict) of w^i
    a = [dict() for _ in range(deg+1)]
    lopow = [one]; Hpow = [one]
    for _ in range(deg): lopow.append(pmul(lopow[-1], lo)); Hpow.append(pmul(Hpow[-1], H))
    for jj, cj in enumerate(cs):
        if not cj: continue
        for i in range(jj+1):
            term = pmul(cj, pscale(pmul(lopow[jj-i], Hpow[i]), comb(jj, i)))
            a[i] = padd(a[i], term)
    # Bernstein: beta_k = sum_{i<=k} C(k,i)/C(deg,i) a_i ; then (hi-lo)^deg P = sum beta_k C(deg,k) w'^k ... 
    # with w = (v-lo)/H: P = sum beta_k C(deg,k) w^k (1-w)^(deg-k); multiply by H^deg:
    # H^deg P = sum beta_k C(deg,k) (v-lo)^k (hi-v)^(deg-k)
    gam = []
    for kk in range(deg+1):
        b = {}
        for i in range(kk+1):
            if a[i]: b = padd(b, pscale(a[i], Fr(comb(kk, i), comb(deg, i))))
        gam.append(pscale(b, comb(deg, kk)))
    return gam

def uni_dict_ok(d, lo, hi, maxdepth=12):
    n = max([m[0] for m in d] + [0])
    cs = [d.get((i,), Fr(0)) for i in range(n+1)]
    return uni_ok(cs, Fr(lo), Fr(hi), 0, maxdepth)

def biv_ok(d, xlo, xhi, S0, S1, maxdepth=12, maxsplit=8, extra=(0,1,2)):
    """d: dict in (x, s). s in [S0(x), S1(x)] (dicts in x or Fractions). returns #leaves or None.
    splits x."""
    n = max([m[1] for m in d] + [0])
    for e in extra:
        gam = bern_inner(d, 2, 1, S0, S1, n+e)
        tot = 0
        for g in gam:
            if not g: tot = None; break
            r = uni_dict_ok(g, xlo, xhi, maxdepth)
            if r is None: tot = None; break
            tot += r
        if tot is not None: return tot, [(xlo, xhi, n+e)]
    if maxsplit == 0: return None
    mid = (xlo+xhi)/2
    a = biv_ok(d, xlo, mid, S0, S1, maxdepth, maxsplit-1, extra)
    if a is None: return None
    b = biv_ok(d, mid, xhi, S0, S1, maxdepth, maxsplit-1, extra)
    if b is None: return None
    return a[0]+b[0], a[1]+b[1]
