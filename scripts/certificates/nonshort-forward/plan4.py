"""Plan nested Bernstein certificates with generic (abstract-coefficient) lemmas.
P(h, s, y): s in [0, g(h)] (g linear in h), y in [0, Y(h)] or numeric pieces.
Level 1: Bernstein in y -> b_k(h, s) = sum_i w_ki * C_i(h, s) (* Y(h)^i if symbolic)
Level 2: Bernstein in s on [0, g(h)] -> beta_kl(h)
Level 3: univariate positivity of beta_kl on [h0, h1] (subdivision count)."""
from fractions import Fraction as Fr
from math import comb
from plan3 import padd, pmul, pscale, bern1
import sympy as sp

def coeffs_in(d, idx):
    n = max([m[idx] for m in d] + [0])
    out = [dict() for _ in range(n+1)]
    for m, c in d.items():
        rest = m[:idx] + m[idx+1:]
        out[m[idx]][rest] = out[m[idx]].get(rest, Fr(0)) + c
    return out

def shift_scale(cs, lo, H, one):
    """cs: list of polys (dicts) coefficients of y^i; returns coefficients in w where y = lo + H w.
    lo, H: dicts (polys in remaining vars) ; one: unit dict"""
    n = len(cs) - 1
    out = [dict() for _ in range(n+1)]
    lop = [one]; Hp = [one]
    for _ in range(n): lop.append(pmul(lop[-1], lo)); Hp.append(pmul(Hp[-1], H))
    for l, c in enumerate(cs):
        if not c: continue
        for i in range(l+1):
            out[i] = padd(out[i], pscale(pmul(c, pmul(lop[l-i], Hp[i])), comb(l, i)))
    return out

def bern01(cs, deg):
    """cs: list of dicts, coefficients of w^i (i <= n <= deg); returns C(deg,k)*beta_k as dicts"""
    n = len(cs) - 1
    res = []
    for k in range(deg+1):
        b = {}
        for i in range(min(k, n)+1):
            if cs[i]: b = padd(b, pscale(cs[i], Fr(comb(k, i), comb(deg, i)) * comb(deg, k)))
        res.append(b)
    return res

def uni_leaves(d, lo, hi, maxdepth=14):
    n = max([m[0] for m in d] + [0])
    cs = [d.get((i,), Fr(0)) for i in range(n+1)]
    while len(cs) > 1 and cs[-1] == 0: cs = cs[:-1]
    def rec(lo, hi, depth):
        b = bern1(cs, lo, hi)
        if min(b) > 0: return 1
        if depth >= maxdepth or b[0] <= 0 or b[-1] <= 0: return None
        mid = (lo+hi)/2
        a = rec(lo, mid, depth+1)
        if a is None: return None
        c = rec(mid, hi, depth+1)
        return None if c is None else a + c
    return rec(Fr(lo), Fr(hi), 0)

def level2(bk, g, h0, h1, extra=(0,1,2,3)):
    """bk: dict in (h, s); s in [0, g(h)], g dict in h. returns (#leaves, deg) or None"""
    cs = coeffs_in(bk, 1)  # coefficients of s^l, dicts in (h,)
    m = len(cs) - 1
    one = {(0,): Fr(1)}
    # coefficients in w where s = g w : c_l g^l
    for e in extra:
        if m + e > 24: break
        csw = shift_scale(cs, {}, g, one)
        betas = bern01(csw, m+e)
        tot = 0
        for be in betas:
            if not be: tot = None; break
            r = uni_leaves(be, h0, h1)
            if r is None: tot = None; break
            tot += r
        if tot is not None: return tot, m+e
    return None

def plan(d, h0, h1, g, ypieces, extra=(0,1,2)):
    """d: dict in (h, s, y). ypieces: list of (ylo, yhi) numeric (Fractions) or 'sym' for [0, Y(h)]"""
    cs = coeffs_in(d, 2)   # dicts in (h, s)
    n = len(cs) - 1
    one = {(0, 0): Fr(1)}
    res = []
    for (ylo, yhi) in ypieces:
        lo = {(0,0): Fr(ylo)} if ylo else {}
        H = {(0,0): Fr(yhi - ylo)}
        csw = shift_scale(cs, lo, H, one)
        best = None
        for e in extra:
            if n + e > 24: break
            bks = bern01(csw, n+e)
            tot = 0; ok = True
            for bk in bks:
                r = level2(bk, g, h0, h1)
                if r is None: ok = False; break
                tot += r[0]
            if ok: best = (tot, n+e); break
        res.append(((ylo, yhi), best))
    return res

def plan_sym(d, h0, h1, g, Y, extra=(0,1,2)):
    """y in [0, Y(h)] with Y a dict in h (embedded into (h,s) dicts)."""
    cs = coeffs_in(d, 2)
    n = len(cs) - 1
    one = {(0, 0): Fr(1)}
    Yhs = {(m[0], 0): c for m, c in Y.items()}
    csw = shift_scale(cs, {}, Yhs, one)
    for e in extra:
        if n + e > 14: break
        bks = bern01(csw, n+e)
        tot = 0; ok = True; fails = []
        for kk, bk in enumerate(bks):
            r = level2(bk, g, h0, h1)
            if r is None: ok = False; fails.append(kk); continue
            tot += r[0]
        print('elev', e, 'tot', tot, 'fails', fails)
        if ok: return tot, n+e
    return None

def plan_symp(d, h0, h1, g, fr, extra=(0,1,2)):
    """y in [a h, b h] pieces, fr = list of (a, b) fractions."""
    cs = coeffs_in(d, 2)
    n = len(cs) - 1
    one = {(0, 0): Fr(1)}
    out = []
    for a, b in fr:
        lo = {(1, 0): Fr(a)} if a else {}
        H = {(1, 0): Fr(b - a)}
        csw = shift_scale(cs, lo, H, one)
        res = None
        for e in extra:
            if n + e > 24: break
            bks = bern01(csw, n+e)
            tot = 0; ok = True; fails = []
            for kk, bk in enumerate(bks):
                r = level2(bk, g, h0, h1)
                if r is None: ok = False; fails.append(kk); continue
                tot += r[0]
            if ok: res = (tot, n+e); break
        out.append(((a, b), res))
    return out
