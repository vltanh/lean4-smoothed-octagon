"""Lean emitters for nested Bernstein certificates (hh2 / S2 heavy leaves).

Conventions: polynomials are dicts {exponent tuple: Fraction}; univariate lists cs[i] = coeff of y^i.
Exponents are written `^ (k : ℕ)`.
"""
from fractions import Fraction as Fr
from math import comb, lcm
import sys

from bern import uni_bern, elevate, bern_weights, uni_coeffs, lincomb

def lnum(q):
    q = Fr(q)
    if q.denominator == 1:
        return str(q.numerator) if q.numerator >= 0 else f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})" if q.numerator >= 0 else f"(({q.numerator}) / {q.denominator})"

def pw(v, e):
    if e == 0: return None
    if e == 1: return v
    return f"{v} ^ ({e} : ℕ)"

def upoly(cs, v):
    terms = []
    for i, c in enumerate(cs):
        c = Fr(c)
        if c == 0: continue
        mono = pw(v, i)
        if mono is None:
            terms.append(lnum(c))
        elif c == 1:
            terms.append(mono)
        else:
            terms.append(f"{lnum(c)} * {mono}")
    if not terms: return "0"
    return " + ".join(terms)

def ilin(lo, hi, v):
    """integer linear forms a = D*v - A >= 0, b = B - D*v >= 0 with a + b = B - A."""
    D = lcm(Fr(lo).denominator, Fr(hi).denominator)
    A = int(Fr(lo) * D); B = int(Fr(hi) * D)
    if D == 1:
        a = f"({v} - {lnum(A)})" if A != 0 else v
        b = f"({lnum(B)} - {v})"
    else:
        a = f"({D} * {v} - {lnum(A)})" if A != 0 else f"({D} * {v})"
        b = f"({lnum(B)} - {D} * {v})"
    return a, b, B - A

# ---------------------------------------------------------------- generic lemmas
class Lib:
    """Collects generic lemmas (positivity of Bernstein forms; interval Bernstein lemmas)."""
    def __init__(self, prefix):
        self.prefix = prefix
        self.pos = set()
        self.intervals = {}   # (n, lo, hi) -> name
        self.code = []
    def pos_name(self, n):
        self.pos.add(n)
        return f"hh2BernPos{n}"
    def emit_pos(self, n):
        cs = " ".join(f"c{k}" for k in range(n+1))
        hs = " ".join(f"(h{k} : 0 < c{k})" for k in range(n+1))
        def term(k):
            parts = [f"c{k}"] + [p for p in (pw("a", k), pw("b", n-k)) if p]
            return " * ".join(parts)
        full = " + ".join(term(k) for k in range(n+1))
        no_top = " + ".join(term(k) for k in range(n))
        no_bot = " + ".join(term(k) for k in range(1, n+1))
        return f"""/-- A Bernstein form of degree {n} with positive coefficients is positive. -/
theorem hh2BernPos{n} {{a b : ℝ}} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {{{cs} : ℝ}}
    {hs} :
    0 < {full} := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < {term(n)} := by positivity
    have h'' : 0 ≤ {no_top} := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < {term(0)} := by positivity
    have h'' : 0 ≤ {no_bot} := by positivity
    linarith
"""
    def interval(self, n, lo, hi):
        key = (n, Fr(lo), Fr(hi))
        if key in self.intervals: return self.intervals[key]
        name = f"{self.prefix}BernI{n}_{len(self.intervals)}"
        self.intervals[key] = name
        return name
    def weights(self, n, lo, hi):
        """V[k][i] such that hyp_k = sum_i V[k][i] c_i is C(n,k)*(hi-lo)^n * (Bernstein coeff k) ... scaled.
        We use the identity (hi-lo)^n p(y) = sum_k (sum_i V[k][i] c_i) (y-lo)^k (hi-y)^(n-k)."""
        W = bern_weights(n, Fr(lo), Fr(hi))
        H = Fr(hi) - Fr(lo)
        return [[comb(n, k) * W[k][i] for i in range(n+1)] for k in range(n+1)]
    def emit_interval(self, n, lo, hi, name):
        V = self.weights(n, lo, hi)
        lo, hi = Fr(lo), Fr(hi)
        cs = " ".join(f"c{k}" for k in range(n+1))
        def lin(k):
            ts = []
            for i in range(n+1):
                w = V[k][i]
                if w == 0: continue
                ts.append(f"c{i}" if w == 1 else f"{lnum(w)} * c{i}")
            return " + ".join(ts) if ts else "0"
        hyps = "\n".join(f"    (hb{k} : 0 < {lin(k)})" for k in range(n+1))
        poly = " + ".join(([f"c0"] + [f"c{i} * {pw('y', i)}" for i in range(1, n+1)]))
        A = f"(y - {lnum(lo)})" if lo != 0 else "y"
        B = f"({lnum(hi)} - y)"
        rhs = " + ".join(f"({lin(k)})" + "".join(" * " + p for p in (pw(A, k), pw(B, n-k)) if p) for k in range(n+1))
        hb = " ".join(f"hb{k}" for k in range(n+1))
        return f"""/-- Bernstein positivity of degree {n} on `[{lo}, {hi}]`, with abstract coefficients. -/
private theorem {name} {{y {cs} : ℝ}} (h0 : {lnum(lo)} ≤ y) (h1 : y ≤ {lnum(hi)})
{hyps} :
    0 < {poly} := by
  have hpos := {self.pos_name(n)} (a := {A}) (b := {B}) (by linarith) (by linarith) (by linarith) {hb}
  have e : ({lnum(hi - lo)} : ℝ) ^ ({n} : ℕ) * ({poly}) = {rhs} := by ring
  have hH : (0 : ℝ) < ({lnum(hi - lo)} : ℝ) ^ ({n} : ℕ) := by norm_num
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos hH.le
"""
    def render(self):
        ivs = [self.emit_interval(n, lo, hi, name) for (n, lo, hi), name in self.intervals.items()]
        return "\n".join(ivs)
    def render_pos(self, degrees):
        return "\n".join(self.emit_pos(n) for n in degrees)

# ---------------------------------------------------------------- univariate leaves
def uni_split(cs, lo, hi, maxdepth=10, maxelev=8):
    for r in range(maxelev + 1):
        bs = uni_bern(cs, lo, hi)
        if r: bs = elevate(bs, r)
        if min(bs) > 0: return [(lo, hi, bs)]
    if maxdepth == 0: return None
    mid = (lo + hi) / 2
    L = uni_split(cs, lo, mid, maxdepth - 1, maxelev)
    if L is None: return None
    R = uni_split(cs, mid, hi, maxdepth - 1, maxelev)
    if R is None: return None
    return L + R

def emit_leaf(out, name, cs, lo, hi, v, stmt, unfold, private=True):
    """theorem name (v) (h0 : lo ≤ v) (h1 : v ≤ hi) : 0 < stmt ; stmt equals sum cs[i] v^i after unfolding."""
    lo, hi = Fr(lo), Fr(hi)
    pieces = uni_split(cs, lo, hi)
    if pieces is None: raise RuntimeError(f"leaf {name} failed on [{float(lo)},{float(hi)}]")
    unf = f"unfold {unfold}\n  " if unfold else ""
    pv = "private " if private else ""
    for li, (a_, b_, bb) in enumerate(pieces):
        n = len(bb) - 1
        eps = min(bb)
        af, bf, H = ilin(a_, b_, v)
        cs_ = [(bb[i] - eps) * comb(n, i) for i in range(n + 1)]
        M = 1
        for c in cs_: M = lcm(M, c.denominator)
        ci = [int(c * M) for c in cs_]
        K = M * H**n
        terms = []
        for i in range(n + 1):
            if ci[i] == 0: continue
            fs = [str(ci[i])] + [f for f in (pw("a", i), pw("b", n - i)) if f]
            terms.append(" * ".join(fs))
        S = " + ".join(terms) if terms else "0"
        out.append(f"""{pv}theorem {name}_bp{li} (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ {S} := by positivity

{pv}theorem {name}_l{li} ({v} : ℝ) (h0 : {lnum(a_)} ≤ {v}) (h1 : {v} ≤ {lnum(b_)}) :
    0 < {stmt} := by
  {unf}linear_combination (1 / {K} : ℝ) * {name}_bp{li} {af} {bf} (by linarith) (by linarith)
""")
    if len(pieces) == 1:
        return 1, f"{name}_l0"
    body = []; cur = "h0"
    for li in range(len(pieces)):
        a_, b_, _ = pieces[li]
        if li == len(pieces) - 1:
            body.append(f"  exact {name}_l{li} {v} {cur} h1")
        else:
            body.append(f"  rcases le_total {v} {lnum(b_)} with hc{li} | hc{li}")
            body.append(f"  · exact {name}_l{li} {v} {cur} hc{li}")
            cur = f"hc{li}"
    out.append(f"""{pv}theorem {name} ({v} : ℝ) (h0 : {lnum(lo)} ≤ {v}) (h1 : {v} ≤ {lnum(hi)}) :
    0 < {stmt} := by
""" + "\n".join(body) + "\n")
    return len(pieces), name

# ---------------------------------------------------------------- nested certificates
def nested_coeffs(P, n1=None, n2=None):
    """P dict over (e1,e2,e3) -> d[i][j] = list of v3-coefficients."""
    N1 = max(m[0] for m in P); N2 = max(m[1] for m in P); N3 = max(m[2] for m in P)
    d = [[[Fr(0)] * (N3 + 1) for _ in range(N2 + 1)] for _ in range(N1 + 1)]
    for (e1, e2, e3), c in P.items():
        d[e1][e2][e3] += c
    return d

def lin_str(ws, terms):
    """sum ws[i] * terms[i] (omit zero weights; weight 1 -> bare term)."""
    out = []
    for w, t in zip(ws, terms):
        if w == 0: continue
        out.append(t if w == 1 else f"{lnum(w)} * {t}")
    return " + ".join(out) if out else "0"

def polyy(cs_strs, y):
    """c0 + c1 * y + c2 * y ^ 2 ... with given coefficient strings (parenthesized)."""
    parts = [cs_strs[0]] + [f"{c} * {pw(y, i)}" for i, c in enumerate(cs_strs) if i >= 1]
    return " + ".join(parts)

def emit_nested(lib, X, P, vars3, boxes, doc="", defs=True, dexpr=None, kset=None, emit_box=True, kpublic=False):
    """Certificates 0 < X v1 v2 v3 on each box in `boxes`: list of ((lo1,hi1),(lo2,hi2),(lo3,hi3)).
    Emits the coefficient defs and X (if defs) and one theorem `X_pos{b}` per box.
    Returns (code, nleaves, theorem names)."""
    v1, v2, v3 = vars3
    d = nested_coeffs(P)
    N1 = len(d) - 1; N2 = len(d[0]) - 1
    out = []
    dn = lambda i, j: f"{X}_d{i}_{j}"
    nz = [[any(c != 0 for c in d[i][j]) for j in range(N2 + 1)] for i in range(N1 + 1)]
    if defs:
        for i in range(N1 + 1):
            for j in range(N2 + 1):
                if nz[i][j]:
                    body_ = upoly(d[i][j], v3) if dexpr is None else dexpr(i, j)[0]
                    out.append(f"/-- Coefficient of `{v1}^{i} {v2}^{j}` in `{X}`. -/\nnoncomputable def {dn(i,j)} ({v3} : ℝ) : ℝ :=\n  {body_}\n")
    def Cstr(i):
        ts = []
        for j in range(N2 + 1):
            if not nz[i][j]: continue
            base = f"{dn(i,j)} {v3}"
            ts.append(base if j == 0 else f"{base} * {pw(v2, j)}")
        return "(" + (" + ".join(ts) if ts else "0") + ")"
    Cs = [Cstr(i) for i in range(N1 + 1)]
    if defs:
        out.append(f"""/-- {doc} (nested form). -/
noncomputable def {X} ({v1} {v2} {v3} : ℝ) : ℝ :=
  {polyy(Cs, v1)}
""")
    nleaves = 0
    names = []
    for b, ((lo1, hi1), (lo2, hi2), (lo3, hi3)) in enumerate(boxes):
        lo1, hi1, lo2, hi2, lo3, hi3 = map(Fr, (lo1, hi1, lo2, hi2, lo3, hi3))
        V1 = lib.weights(N1, lo1, hi1); V2 = lib.weights(N2, lo2, hi2)
        I1 = lib.interval(N1, lo1, hi1) if emit_box else None
        I2 = lib.interval(N2, lo2, hi2) if (kset is None or len(kset) > 0) else None
        k_thms = []
        for k in range(N1 + 1):
            k_thms.append(f"{X}_b{b}_k{k}")
            if kset is not None and k not in kset: continue
            en = lambda j: f"{X}_e{b}_{k}_{j}"
            ecs = []
            for j in range(N2 + 1):
                cs = [Fr(0)] * len(d[0][0])
                for i in range(N1 + 1):
                    if V1[k][i] == 0 or not nz[i][j]: continue
                    for e_, c_ in enumerate(d[i][j]): cs[e_] += V1[k][i] * c_
                ecs.append(cs)
                out.append(f"noncomputable def {en(j)} ({v3} : ℝ) : ℝ :=\n  {upoly(cs, v3)}\n")
            Es = [f"{en(j)} {v3}" for j in range(N2 + 1)]
            alle = " ".join(en(j) for j in range(N2 + 1))
            l_names = []
            for l in range(N2 + 1):
                cs = [Fr(0)] * len(d[0][0])
                for j in range(N2 + 1):
                    if V2[l][j] == 0: continue
                    for e_, c_ in enumerate(ecs[j]): cs[e_] += V2[l][j] * c_
                stmt = lin_str(V2[l], Es)
                unf = " ".join(en(j) for j in range(N2 + 1) if V2[l][j] != 0)
                lname = f"{X}_b{b}_k{k}_l{l}"
                npc, nm_ = emit_leaf(out, lname, cs, lo3, hi3, v3, stmt, unf)
                nleaves += npc
                l_names.append(nm_)
            hyp1 = lin_str(V1[k], Cs)
            usedd = " ".join(dn(i, j) for i in range(N1 + 1) for j in range(N2 + 1) if nz[i][j] and V1[k][i] != 0)
            if dexpr is not None:
                extra = sorted({nm for i in range(N1 + 1) for j in range(N2 + 1) if nz[i][j] and V1[k][i] != 0 for nm in dexpr(i, j)[1]})
                usedd = usedd + " " + " ".join(extra)
            kname = f"{X}_b{b}_k{k}"
            kpv = "" if kpublic else "private "
            out.append(f"""{kpv}theorem {kname} ({v2} {v3} : ℝ) (h2l : {lnum(lo2)} ≤ {v2}) (h2h : {v2} ≤ {lnum(hi2)})
    (h3l : {lnum(lo3)} ≤ {v3}) (h3h : {v3} ≤ {lnum(hi3)}) :
    0 < {hyp1} := by
  have e : {hyp1} = {polyy(Es, v2)} := by
    unfold {usedd} {alle}
    ring
  rw [e]
  exact {I2} h2l h2h {" ".join(f"({ln} {v3} h3l h3h)" for ln in l_names)}
""")
        if not emit_box:
            continue
        pname = f"{X}_pos{b}" if len(boxes) > 1 else f"{X}_pos"
        out.append(f"""/-- **Positivity of `{X}`** on `[{lo1}, {hi1}] × [{lo2}, {hi2}] × [{lo3}, {hi3}]`. -/
theorem {pname} ({v1} {v2} {v3} : ℝ) (h1l : {lnum(lo1)} ≤ {v1}) (h1h : {v1} ≤ {lnum(hi1)})
    (h2l : {lnum(lo2)} ≤ {v2}) (h2h : {v2} ≤ {lnum(hi2)}) (h3l : {lnum(lo3)} ≤ {v3}) (h3h : {v3} ≤ {lnum(hi3)}) :
    0 < {X} {v1} {v2} {v3} := by
  unfold {X}
  exact {I1} h1l h1h {" ".join(f"({kn} {v2} {v3} h2l h2h h3l h3h)" for kn in k_thms)}
""")
        names.append(pname)
    return "\n".join(out), nleaves, names
