"""Generate Lean certificates (Bernstein form) for polynomial positivity."""
from fractions import Fraction as Fr
from math import comb, lcm
import sympy as sp

def F(c):
    c = sp.Rational(c)
    return Fr(int(c.p), int(c.q))

def lnum(q):
    q = Fr(q)
    if q.denominator == 1:
        return str(q.numerator) if q.numerator >= 0 else f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})"

TYPED = [False]
def pw(name, e):
    if e == 0: return None
    if e == 1: return name
    return f"{name} ^ ({e} : ℕ)" if TYPED[0] else f"{name} ^ {e}"

def lpoly(expr, vars_, names, mult=None):
    """Lean string of a polynomial (sympy expr) in vars_; if mult given, multiply coefficients."""
    P = sp.Poly(sp.expand(expr), *vars_)
    TYPED[0] = len(P.terms()) > 60
    terms = []
    for mon, c in sorted(P.terms(), key=lambda mc: mc[0]):
        c = F(c) * (mult if mult is not None else 1)
        if c == 0: continue
        fs = [pw(names[i], e) for i, e in enumerate(mon)]
        fs = [f for f in fs if f]
        a = abs(c)
        if fs:
            body = " * ".join(([lnum(a)] if a != 1 else []) + fs)
        else:
            body = lnum(a)
        terms.append(("-" if c < 0 else "+", body))
    if not terms: return "0"
    s = ("-" if terms[0][0] == "-" else "") + terms[0][1]
    for sg, b in terms[1:]:
        s += f" {sg} {b}"
    return s

def coeffs1(expr, var):
    P = sp.Poly(sp.expand(expr), var)
    n = P.degree()
    return [F(P.coeff_monomial(var**i)) for i in range(n+1)]

def bern1(cs, lo, hi):
    """Bernstein coefficients of p(x)=sum cs[i] x^i on [lo,hi]."""
    n = len(cs)-1
    h = hi - lo
    # shift: p(lo + h u)
    u = [Fr(0)]*(n+1)
    for j, c in enumerate(cs):
        if c == 0: continue
        for i in range(j+1):
            u[i] += c * comb(j, i) * lo**(j-i) * h**i
    b = []
    for k in range(n+1):
        s = Fr(0)
        for i in range(k+1):
            s += Fr(comb(k, i), comb(n, i)) * u[i]
        b.append(s)
    return b

def uni_split(cs, lo, hi, depth=0, maxdepth=40):
    b = bern1(cs, lo, hi)
    if min(b) > 0:
        return [(lo, hi, b)]
    if depth > maxdepth:
        raise RuntimeError(f"uni_split failed near [{float(lo)},{float(hi)}] min {float(min(b))}")
    mid = (lo + hi) / 2
    # prefer a simpler midpoint (dyadic of small denominator)
    return uni_split(cs, lo, mid, depth+1, maxdepth) + uni_split(cs, mid, hi, depth+1, maxdepth)

def lin_forms(lo, hi, var):
    D = lcm(lo.denominator, hi.denominator)
    A = lo * D; B = hi * D
    A = int(A); B = int(B)
    if D == 1:
        a = f"({var} - {lnum(A)})" if A != 0 else var
        b = f"({lnum(B)} - {var})"
    else:
        a = f"({D} * {var} - {lnum(A)})" if A != 0 else f"({D} * {var})"
        b = f"({lnum(B)} - {D} * {var})"
    return a, b, D, B - A

def emit_uni(name, expr, var, varname, lo, hi, stmt=None, private=True):
    """Lean code proving `theorem name (x) (h0 : lo ≤ x) (h1 : x ≤ hi) : 0 < stmt`."""
    lo = Fr(lo); hi = Fr(hi)
    cs = coeffs1(expr, var)
    n = len(cs) - 1
    if stmt is None:
        stmt = lpoly(expr, [var], [varname])
    leaves = uni_split(cs, lo, hi)
    out = []
    pv = "private " if private else ""
    for li, (a_, b_, bb) in enumerate(leaves):
        eps = min(bb)
        af, bf, D, H = lin_forms(a_, b_, varname)
        cs_ = [(bb[i] - eps) * comb(n, i) for i in range(n+1)]
        M = 1
        for c in cs_ + [eps]: M = lcm(M, c.denominator)
        ci = [int(c * M) for c in cs_]
        K = M * H**n
        E = eps * M * H**n
        terms = []
        for i in range(n+1):
            if ci[i] == 0: continue
            fs = [str(ci[i])] + [f for f in (pw("a", i), pw("b", n-i)) if f]
            terms.append(" * ".join(fs))
        S = " + ".join(terms) if terms else "0"
        out.append(f"""{pv}theorem {name}_bp{li} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ {S} := by positivity

{pv}theorem {name}_l{li} ({varname} : ℝ) (h0 : {lnum(a_)} ≤ {varname}) (h1 : {varname} ≤ {lnum(b_)}) :
    0 < {stmt} := by
  linear_combination (1 / {K} : ℝ) * {name}_bp{li} {af} {bf} (by linarith) (by linarith)
""")
    # combine
    body = []
    cur = "h0"
    for li in range(len(leaves)):
        a_, b_, _ = leaves[li]
        if li == len(leaves) - 1:
            body.append(f"  exact {name}_l{li} {varname} {cur} h1")
        else:
            body.append(f"  rcases le_total {varname} {lnum(b_)} with hc{li} | hc{li}")
            body.append(f"  · exact {name}_l{li} {varname} {cur} hc{li}")
            cur = f"hc{li}"
    out.append(f"""theorem {name} ({varname} : ℝ) (h0 : {lnum(lo)} ≤ {varname}) (h1 : {varname} ≤ {lnum(hi)}) :
    0 < {stmt} := by
""" + "\n".join(body) + "\n")
    return "\n".join(out), len(leaves)

def bern_inner(expr, s, x, S0, S1, d=None):
    """Bernstein coefficients (polys in x) of expr(x,s) in s over [S0(x), S1(x)] (polynomial bounds)
    returns list gamma_j with (S1-S0)^d * expr = sum gamma_j (s-S0)^j (S1-s)^(d-j)."""
    z = sp.Symbol('zz')
    e = sp.expand(expr.subs(s, S0 + (S1 - S0)*z))
    P = sp.Poly(e, z)
    deg = P.degree()
    if d is None: d = deg
    a = [P.coeff_monomial(z**i) for i in range(deg+1)] + [0]*(d-deg)
    # power coefficients a_i in z -> Bernstein beta_k = sum_{i<=k} C(k,i)/C(d,i) a_i
    gam = []
    for k in range(d+1):
        bk = sum(sp.Rational(comb(k, i), comb(d, i)) * a[i] for i in range(k+1))
        # (S1-S0)^d * expr = sum beta_k C(d,k) ((s-S0))^k ((S1-s))^(d-k)  [since z=(s-S0)/(S1-S0)]
        gam.append(sp.expand(bk * comb(d, k) * (S1 - S0)**d / (S1 - S0)**d))
    # check identity
    chk = sp.expand((S1 - S0)**d * expr - sum(gam[k] * (s - S0)**k * (S1 - s)**(d-k) for k in range(d+1)))
    # NOTE: gam computed above is beta*C(d,k) and identity is (S1-S0)^d expr = sum gam (s-S0)^k (S1-s)^(d-k) * ... 
    return gam, chk

def try_piece(expr, s, x, xlo, xhi, S0, S1, d):
    gam, chk = bern_inner(expr, s, x, S0, S1, d)
    assert chk == 0
    leaves = []
    for g in gam:
        cs = coeffs1(g, x) if sp.expand(g) != 0 else [Fr(0)]
        try:
            lv = uni_split(cs, Fr(xlo), Fr(xhi), maxdepth=12)
        except RuntimeError:
            return None
        leaves.append(lv)
    return gam

def plan_biv(expr, s, x, xlo, xhi, S0f, S1f, d0=None, maxsplit=12):
    """Split [xlo,xhi] until each piece has all gamma_j>0. S0f,S1f: functions (xlo,xhi)->(S0expr,S1expr)."""
    xlo = Fr(xlo); xhi = Fr(xhi)
    S0, S1 = S0f(xlo, xhi), S1f(xlo, xhi)
    deg = sp.Poly(sp.expand(expr), s).degree()
    for d in ([d0] if d0 else [deg, deg+1, deg+2]):
        g = try_piece(expr, s, x, xlo, xhi, S0, S1, d)
        if g is not None:
            return [(xlo, xhi, S0, S1, d, g)]
    if maxsplit == 0:
        raise RuntimeError(f"plan_biv failed on [{float(xlo)},{float(xhi)}]")
    mid = (xlo + xhi) / 2
    return plan_biv(expr, s, x, xlo, mid, S0f, S1f, d0, maxsplit-1) + plan_biv(expr, s, x, mid, xhi, S0f, S1f, d0, maxsplit-1)

def emit_biv_piece(name, expr, s, x, sname, xname, piece, stmt=None, unfold=None):
    xlo, xhi, S0, S1, d, gam = piece
    if stmt is None:
        stmt = lpoly(expr, [x, s], [xname, sname])
    S0s = lpoly(S0, [x], [xname]); S1s = lpoly(S1, [x], [xname])
    out = []
    M = 1
    for g in gam:
        for c in sp.Poly(sp.expand(g), x).coeffs(): M = lcm(M, F(c).denominator)
    gs = [lpoly(g, [x], [xname], mult=M) for g in gam]
    total_leaves = 0
    for j, g in enumerate(gam):
        code, nl = emit_uni(f"{name}_g{j}", sp.expand(g*M), x, xname, xlo, xhi, stmt=gs[j])
        total_leaves += nl
        out.append(code)
    a = f"({sname} - ({S0s}))"; b = f"(({S1s}) - {sname})"
    rhs_terms = []
    for j in range(d+1):
        fs = [f"({gs[j]})"]
        if j >= 1: fs.append(a if j == 1 else f"{a} ^ {j}")
        if d - j >= 1: fs.append(b if d - j == 1 else f"{b} ^ {d-j}")
        rhs_terms.append(" * ".join(fs))
    # generic lemma shape: c0 * b ^ d + c1 * a * b ^ (d-1) + ... + cd * a ^ d
    rhs = " + ".join(rhs_terms)
    gargs = " ".join(f"({name}_g{j} {xname} hx0 hx1)" for j in range(d+1))
    out.append(f"""theorem {name} ({xname} {sname} : ℝ) (hx0 : {lnum(xlo)} ≤ {xname}) (hx1 : {xname} ≤ {lnum(xhi)})
    (hs0 : {S0s} ≤ {sname}) (hs1 : {sname} ≤ {S1s}) (hgap : (0 : ℝ) < ({S1s}) - ({S0s})) :
    0 < {stmt} := by
  have hpos := nh_bern_pos{d} (a := {a}) (b := {b}) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    {gargs}
  have e : {M} * (({S1s}) - ({S0s})) ^ {d} * ({stmt}) = {rhs} := by {('unfold ' + unfold + '; ') if unfold else ''}ring
  have h2 : 0 < {M} * (({S1s}) - ({S0s})) ^ {d} * ({stmt}) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)
""")
    return "\n".join(out), total_leaves
