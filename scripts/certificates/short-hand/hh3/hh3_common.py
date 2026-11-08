"""Shared helpers for the hh3 generators (heavy leaves of gate S3).

Polynomials are dicts {exponent tuple: Fraction}.  Lean strings use `x ^ (n : ℕ)` exponents.
The certificate finders return explicit nonnegative combinations; Lean re-checks every identity
(`ring`, `linear_combination`), so nothing computed here is trusted.
"""
from fractions import Fraction as Fr
from math import comb
import sympy as sp


def to_dict(expr, syms):
    P = sp.Poly(sp.expand(expr), *syms)
    return {m: Fr(int(c.p), int(c.q)) for m, c in P.terms()}


def lnum(c):
    c = Fr(c)
    if c.denominator == 1:
        return f"{c.numerator}" if c.numerator >= 0 else f"({c.numerator})"
    if c.numerator >= 0:
        return f"({c.numerator} / {c.denominator})"
    return f"(({c.numerator}) / {c.denominator})"


def mono(vars_, exps):
    parts = []
    for v, e in zip(vars_, exps):
        if e == 1:
            parts.append(v)
        elif e > 1:
            parts.append(f"{v} ^ ({e} : ℕ)")
    return parts


def mono_pow(vars_, exps):
    """Like mono, but always with an explicit exponent (so that `pow_le_pow_left₀` facts match)."""
    return [f"{v} ^ ({e} : ℕ)" for v, e in zip(vars_, exps) if e >= 1]


def term_str(c, vars_, exps):
    m = mono(vars_, exps)
    if not m:
        return lnum(c)
    if c == 1:
        return " * ".join(m)
    return f"{lnum(c)} * " + " * ".join(m)


def poly_expanded(d, vars_, width=None):
    items = [(k, c) for k, c in sorted(d.items()) if c != 0]
    if not items:
        return "0"
    return " + ".join(term_str(c, vars_, k) for k, c in items)


def horner(d, vars_):
    """Nested Horner form; keys of d are in the order of vars_, vars_[0] outermost."""
    if len(vars_) == 0:
        return lnum(d.get((), 0))
    v = vars_[0]
    groups = {}
    for exps, c in d.items():
        if c == 0:
            continue
        groups.setdefault(exps[0], {})[exps[1:]] = c
    if not groups:
        return "0"
    s = None
    for e in range(max(groups), -1, -1):
        g = groups.get(e)
        inner = horner(g, vars_[1:]) if g else "0"
        if s is None:
            s = inner
        elif inner == "0":
            s = f"({v} * ({s}))"
        else:
            s = f"({inner} + {v} * ({s}))"
    return s


def horner_by(d, dict_vars, order):
    idx = [dict_vars.index(v) for v in order]
    return horner({tuple(k[i] for i in idx): c for k, c in d.items()}, order)


def bern_coeffs(p, d):
    """p: list of coefficients (ascending) on [0,1]; fhBern convention b_k = sum C(d-l,k-l) p_l,
    so that sum_l p_l v^l = sum_k b_k v^k (1-v)^(d-k)."""
    p = list(p) + [Fr(0)] * (d + 1 - len(p))
    return [sum(comb(d - l, k - l) * p[l] for l in range(k + 1)) for k in range(d + 1)]


def scale_poly(d, H, V):
    """P(H s, V w) as dict in (s, w)."""
    return {(r, l): c * Fr(H) ** r * Fr(V) ** l for (r, l), c in d.items()}


def cert_bv(d, H, V):
    """Certificate for P(h,v) > 0 on [0,H] x [0,V]: Bernstein in v (degree dv) for every power
    h^r, crude in h for negative Bernstein coefficients at r >= 1.  Returns None or a dict with
    the decomposition."""
    dv = max(k[1] for k in d)
    dh = max(k[0] for k in d)
    # P(h, V w) = sum_r h^r sum_l c_rl V^l w^l ; Bernstein in w on [0,1]
    rows = {}
    for r in range(dh + 1):
        p = [d.get((r, l), Fr(0)) * Fr(V) ** l for l in range(dv + 1)]
        rows[r] = bern_coeffs(p, dv)
    bhat = []
    for k in range(dv + 1):
        s = rows[0][k] - sum(-rows[r][k] * Fr(H) ** r for r in range(1, dh + 1) if rows[r][k] < 0)
        bhat.append(s)
    m = min(bhat[k] / comb(dv, k) for k in range(dv + 1))
    if m <= 0:
        return None
    return dict(kind='bv', dv=dv, dh=dh, rows=rows, m=m, H=Fr(H), V=Fr(V))


def cert_a(d, H):
    """Crude in h, exact monomials in v: ahat_l >= 0, ahat_0 > 0."""
    dv = max(k[1] for k in d)
    ahat = []
    for l in range(dv + 1):
        s = d.get((0, l), Fr(0)) - sum(-c * Fr(H) ** r for (r, ll), c in d.items()
                                       if ll == l and r >= 1 and c < 0)
        ahat.append(s)
    if ahat[0] <= 0 or min(ahat) < 0:
        return None
    return dict(kind='a', ahat=ahat, H=Fr(H))


def cert_c(d, H, V):
    """Crude in both variables: p00 - sum_neg |c| H^r V^l > 0."""
    p00 = d.get((0, 0), Fr(0))
    neg = sum(-c * Fr(H) ** r * Fr(V) ** l for (r, l), c in d.items() if c < 0 and (r, l) != (0, 0))
    if p00 - neg <= 0:
        return None
    return dict(kind='c', res=p00 - neg, H=Fr(H), V=Fr(V))


def lean_cert(d, cert, hv=('h', 'v'), hyps=('h0', 'h1', 'v0', 'v1')):
    """Lean tactic lines proving `0 < P(h, v)` (P given by the dict d, written in the goal),
    from hypotheses h0 : 0 ≤ h, h1 : h ≤ H, v0 : 0 ≤ v, v1 : v ≤ V."""
    h, v = hv
    h0, h1, v0, v1 = hyps
    lines = []
    comb_terms = []
    n = 0
    H = cert['H']
    if cert['kind'] == 'a':
        for (r, l), c in sorted(d.items()):
            if r == 0 or c == 0:
                continue
            n += 1
            mon = " * ".join(mono_pow([h, v], (r, l)) or ["1"])
            vmon = " * ".join(mono_pow([v], (l,)) or ["1"])
            if c > 0:
                lines.append(f"  have f{n} : 0 ≤ {mon} := by positivity")
                comb_terms.append(f"{lnum(c)} * f{n}")
            else:
                hp = f"pow_le_pow_left₀ {h0} {h1} {r}"
                if l == 0:
                    lines.append(f"  have f{n} : {h} ^ ({r} : ℕ) ≤ {lnum(H)} ^ ({r} : ℕ) := {hp}")
                else:
                    lines.append(f"  have f{n} : {mon} ≤ {lnum(H)} ^ ({r} : ℕ) * {vmon} := "
                                 f"mul_le_mul_of_nonneg_right ({hp}) (pow_nonneg {v0} {l})")
                comb_terms.append(f"{lnum(-c)} * f{n}")
        for l, a in enumerate(cert['ahat']):
            if l == 0 or a == 0:
                continue
            n += 1
            lines.append(f"  have f{n} : 0 ≤ {' * '.join(mono_pow([v], (l,)))} := by positivity")
            comb_terms.append(f"{lnum(a)} * f{n}")
    elif cert['kind'] == 'c':
        V = cert['V']
        for (r, l), c in sorted(d.items()):
            if (r, l) == (0, 0) or c == 0:
                continue
            n += 1
            mon = " * ".join(mono_pow([h, v], (r, l)))
            if c > 0:
                lines.append(f"  have f{n} : 0 ≤ {mon} := by positivity")
                comb_terms.append(f"{lnum(c)} * f{n}")
            else:
                if r == 0:
                    lines.append(f"  have f{n} : {mon} ≤ {lnum(V)} ^ ({l} : ℕ) := "
                                 f"pow_le_pow_left₀ {v0} {v1} {l}")
                elif l == 0:
                    lines.append(f"  have f{n} : {mon} ≤ {lnum(H)} ^ ({r} : ℕ) := "
                                 f"pow_le_pow_left₀ {h0} {h1} {r}")
                else:
                    lines.append(f"  have f{n} : {mon} ≤ {lnum(H)} ^ ({r} : ℕ) * {lnum(V)} ^ ({l} : ℕ) := "
                                 f"mul_le_mul (pow_le_pow_left₀ {h0} {h1} {r}) (pow_le_pow_left₀ {v0} {v1} {l}) "
                                 f"(pow_nonneg {v0} {l}) (by norm_num)")
                comb_terms.append(f"{lnum(-c)} * f{n}")
    elif cert['kind'] == 'bv':
        dv, dh, rows, m, V = cert['dv'], cert['dh'], cert['rows'], cert['m'], cert['V']
        # P(h,v) = sum_{r,k} rows[r][k] h^r (v/V)^k (1 - v/V)^(dv-k)
        lines.append(f"  have hw : 0 ≤ 1 - {v} / {lnum(V)} := by rw [sub_nonneg, div_le_one (by norm_num)]; exact {v1}")
        lines.append(f"  have hv' : 0 ≤ {v} / {lnum(V)} := by positivity")
        for r in range(dh + 1):
            for k in range(dv + 1):
                b = rows[r][k]
                coef = b - (m * comb(dv, k) if r == 0 else 0)
                if r == 0:
                    # subtract crude negatives of higher r
                    coef = rows[0][k] - m * comb(dv, k) - sum(-rows[rr][k] * H ** rr for rr in range(1, dh + 1) if rows[rr][k] < 0)
                if r >= 1 and b < 0:
                    n += 1
                    base = f"({v} / {lnum(V)}) ^ ({k} : ℕ) * (1 - {v} / {lnum(V)}) ^ ({dv - k} : ℕ)"
                    lines.append(f"  have f{n} : {h} ^ ({r} : ℕ) * ({base}) ≤ {lnum(H)} ^ ({r} : ℕ) * ({base}) := "
                                 f"mul_le_mul_of_nonneg_right (pow_le_pow_left₀ {h0} {h1} {r}) (by positivity)")
                    comb_terms.append(f"{lnum(-b)} * f{n}")
                    continue
                if coef == 0:
                    continue
                n += 1
                hm = f"{h} ^ ({r} : ℕ) * " if r >= 1 else ""
                lines.append(f"  have f{n} : 0 ≤ {hm}({v} / {lnum(V)}) ^ ({k} : ℕ) * (1 - {v} / {lnum(V)}) ^ ({dv - k} : ℕ) := by positivity")
                comb_terms.append(f"{lnum(coef)} * f{n}")
    lines.append("  linear_combination " + " + ".join(comb_terms))
    return lines
