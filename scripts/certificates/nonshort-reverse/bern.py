"""Bernstein subdivision certificates for polynomial positivity, with Lean emission."""
from fractions import Fraction as Fr
from math import comb
import itertools, sympy

def poly_to_dict(p, vars_):
    P = sympy.Poly(sympy.expand(p), *vars_)
    return {m: Fr(int(sympy.numer(c)), int(sympy.denom(c))) for m, c in P.terms()}

def degs(d, m):
    return tuple(max((k[i] for k in d), default=0) for i in range(m))

def shift_scale_1d(coeffs, lo, h):
    # coefficients c_j of p(x) -> coefficients of p(lo + h*u) in u
    n = len(coeffs)-1
    out = [Fr(0)]*(n+1)
    for j, c in enumerate(coeffs):
        if c == 0: continue
        # (lo + h u)^j
        for i in range(j+1):
            out[i] += c * comb(j, i) * lo**(j-i) * h**i
    return out

def to_unit_box(d, m, box):
    # d: dict monomial->coef ; returns dict for p(lo+h*u)
    cur = dict(d)
    for v in range(m):
        lo, hi = box[v]; h = hi - lo
        new = {}
        # group by other exponents
        groups = {}
        for mon, c in cur.items():
            key = mon[:v] + mon[v+1:]
            groups.setdefault(key, {})[mon[v]] = c
        for key, cs in groups.items():
            n = max(cs)
            arr = [cs.get(j, Fr(0)) for j in range(n+1)]
            sh = shift_scale_1d(arr, lo, h)
            for i, c in enumerate(sh):
                if c != 0:
                    mon = key[:v] + (i,) + key[v:]
                    new[mon] = new.get(mon, Fr(0)) + c
        cur = new
    return cur

def bernstein(d, m, box, n):
    # Bernstein coefficients b_alpha on box with degrees n (tuple)
    u = to_unit_box(d, m, box)
    # power basis on [0,1]^m to Bernstein: b_alpha = sum_{beta<=alpha} prod C(alpha_i,beta_i)/C(n_i,beta_i) a_beta
    res = {}
    for alpha in itertools.product(*[range(ni+1) for ni in n]):
        s = Fr(0)
        for beta, a in u.items():
            if all(beta[i] <= alpha[i] for i in range(m)):
                w = Fr(1)
                for i in range(m):
                    w *= Fr(comb(alpha[i], beta[i]), comb(n[i], beta[i]))
                s += w * a
        res[alpha] = s
    return res

def bern_minmax(d, m, box, n):
    b = bernstein(d, m, box, n)
    vals = list(b.values())
    return min(vals), max(vals), b

def subdivide(p, vars_, box, constraints=(), maxdepth=30, strict=True, minmargin=Fr(0)):
    """p: sympy expr; constraints: list of (sympy expr g, strict?) meaning g>0 or g>=0.
    Returns tree: ('pos', box, eps) | ('out', box, k) | ('split', var, mid, left, right)"""
    m = len(vars_)
    d = poly_to_dict(p, vars_)
    n = degs(d, m)
    gs = []
    for g, st in constraints:
        dg = poly_to_dict(g, vars_)
        gs.append((dg, degs(dg, m), st))
    stats = {'pos':0,'out':0}
    def rec(box, depth):
        for k,(dg,ng,st) in enumerate(gs):
            lo, hi, _ = bern_minmax(dg, m, box, ng)
            if (hi <= 0 and st) or (hi < 0):
                stats['out'] += 1
                return ('out', box, k)
        lo, hi, _ = bern_minmax(d, m, box, n)
        if lo > minmargin:
            stats['pos'] += 1
            return ('pos', box, lo)
        if depth >= maxdepth:
            raise RuntimeError('depth exceeded at box %s, min %s' % (box, float(lo)))
        # choose split var: largest width*deg relative
        best = max(range(m), key=lambda i: (box[i][1]-box[i][0]) * max(n[i],1) / (W0[i]))
        lo_, hi_ = box[best]
        mid = (lo_+hi_)/2
        b1 = list(box); b1[best] = (lo_, mid)
        b2 = list(box); b2[best] = (mid, hi_)
        return ('split', best, mid, rec(tuple(b1), depth+1), rec(tuple(b2), depth+1))
    W0 = [box[i][1]-box[i][0] for i in range(m)]
    tree = rec(tuple(box), 0)
    return tree, stats

def lean_frac(q):
    q = Fr(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)" if q.numerator >= 0 else f"(({q.numerator}) : ℝ)"
    return f"(({q.numerator}) / {q.denominator} : ℝ)"

def lean_num(q):
    q = Fr(q)
    if q.denominator == 1:
        return str(q.numerator) if q.numerator >= 0 else f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})" if q.numerator >= 0 else f"(({q.numerator}) / {q.denominator})"

def bern_expr(b, n, box, names, scale_eps):
    """sum over alpha of c_alpha * prod (v-lo)^i (hi-v)^(n-i) ; c_alpha = C(n,alpha)*(b_alpha - eps)."""
    terms = []
    m = len(names)
    for alpha, val in b.items():
        c = val - scale_eps
        w = 1
        for i in range(m): w *= comb(n[i], alpha[i])
        c = c * w
        if c == 0: continue
        fac = [lean_num(c)]
        for i in range(m):
            lo, hi = box[i]
            if alpha[i] > 0:
                fac.append(f"({names[i]} - {lean_num(lo)}) ^ {alpha[i]}")
            if n[i]-alpha[i] > 0:
                fac.append(f"({lean_num(hi)} - {names[i]}) ^ {n[i]-alpha[i]}")
        terms.append(" * ".join(fac))
    return " + ".join(terms) if terms else "0"

def scale_factor(box, n):
    K = Fr(1)
    for i in range(len(n)):
        K *= (box[i][1]-box[i][0])**n[i]
    return K

from math import lcm
def int_lin(lo, hi, name):
    # returns strings for positive multiples of (v-lo) and (hi-v) with integer coefficients, and their scale factors
    D = lcm(Fr(lo).denominator, Fr(hi).denominator)
    a = Fr(lo)*D; b = Fr(hi)*D
    # (v - lo)*D = D v - a ; (hi - v)*D = b - D v
    def num(z):
        z = int(z); return str(z) if z >= 0 else f"({z})"
    if D == 1:
        s1 = f"({name} - {num(a)})" if a != 0 else name
        s2 = f"({num(b)} - {name})"
    else:
        s1 = f"({D} * {name} - {num(a)})" if a != 0 else f"({D} * {name})"
        s2 = f"({num(b)} - {D} * {name})"
    return s1, s2, D

def bern_int_identity(d, m, box, n, names):
    """Return (lhs_mult, eps_term, terms) all integers such that
    lhs_mult * p = eps_int * prod((hi-lo)D)^n + sum c_alpha prod lin1^i lin2^(n-i), c_alpha >= 0 ints."""
    b = bernstein(d, m, box, n)
    eps = min(b.values())
    lins = [int_lin(box[i][0], box[i][1], names[i]) for i in range(m)]
    # p = sum b_alpha prod C(n,a) (v-lo)^a (hi-v)^(n-a) / (hi-lo)^n
    # with lin1 = D(v-lo), lin2 = D(hi-v): (v-lo)^a(hi-v)^(n-a) = lin1^a lin2^(n-a) / D^n
    # so p * prod (D(hi-lo))^n = sum b_alpha C(n,a) lin1^a lin2^(n-a)
    H = Fr(1)
    for i in range(m):
        H *= (lins[i][2]*(box[i][1]-box[i][0]))**n[i]
    coefs = {}
    for alpha, val in b.items():
        w = 1
        for i in range(m): w *= comb(n[i], alpha[i])
        coefs[alpha] = (val - eps) * w
    # eps part: eps * sum C(n,a) lin1^a lin2^(n-a) = eps * prod (lin1+lin2)^n = eps * H
    L = 1
    for c in coefs.values(): L = lcm(L, c.denominator)
    L = lcm(L, eps.denominator)
    return eps, H, L, coefs, lins

def emit_poly_int(d, names, mult):
    # d: dict monomial->Fr ; mult integer making coefficients integral ; emit integer-coefficient poly string
    terms=[]
    for mon, c in sorted(d.items()):
        ci = c*mult; assert ci.denominator == 1; ci = int(ci)
        if ci == 0: continue
        f = [str(abs(ci))] if True else []
        for i, e in enumerate(mon):
            if e == 1: f.append(names[i])
            elif e > 1: f.append(f"{names[i]} ^ {e}")
        term = " * ".join(f)
        terms.append(("- " if ci < 0 else "+ ") + term)
    s = " ".join(terms)
    if s.startswith("+ "): s = s[2:]
    else: s = "-" + s[2:] if s.startswith("- ") else s
    return s
