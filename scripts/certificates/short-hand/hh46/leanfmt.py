"""Lean formatting helpers for exact rational polynomials."""
from fractions import Fraction as Fr

def lnum(c):
    """Lean literal for a nonnegative rational (no sign)."""
    c = Fr(c)
    assert c >= 0
    return f"{c.numerator}" if c.denominator == 1 else f"({c.numerator} / {c.denominator})"

def pw(v, k):
    if k == 0: return None
    if k == 1: return v
    return f"{v} ^ ({k} : ℕ)"

def upoly(cs, v):
    """sum_i cs[i] v^i as a Lean string (cs: list of Fractions)."""
    out = []
    for i, c in enumerate(cs):
        c = Fr(c)
        if c == 0: continue
        m = pw(v, i)
        a = abs(c)
        t = lnum(a) if m is None else (m if a == 1 else f"{lnum(a)} * {m}")
        out.append(("- " if c < 0 else "+ ") + t)
    if not out: return "0"
    s = " ".join(out)
    return s[2:] if s.startswith("+ ") else "-" + s[2:]

def slit(c):
    """Signed Lean literal for a rational."""
    c = Fr(c)
    if c >= 0: return lnum(c)
    a = -c
    return f"(-{a.numerator})" if a.denominator == 1 else f"(-{a.numerator} / {a.denominator})"

def fullpoly(cs, v):
    """`c0 + c1 * v + c2 * v ^ (2 : ℕ) + ...` in exactly the shape of the generic Bernstein lemmas."""
    parts = []
    for i, c in enumerate(cs):
        m = pw(v, i)
        parts.append(slit(c) if m is None else f"{slit(c)} * {m}")
    return " + ".join(parts)
