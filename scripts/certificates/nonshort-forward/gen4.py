"""Nested Bernstein certificates through generic lemmas with abstract coefficients.

A polynomial P(h, j, y) is written as  sum_i ( sum_l D_il(h) s^l ) y^i,  s = j - jlo, with
univariate polynomials D_il (Lean definitions).  Positivity on
    h0 <= h <= h1,   0 <= s <= g(h)  (g linear in h),   y in numeric pieces [ylo, yhi]
is proved in three levels:
  * y-level: `nsfBernI_*` (numeric interval, abstract coefficients c_i = sum_l D_il s^l);
  * s-level: `nsfBern0g*` (interval [0, g], abstract coefficients E_l = sum_i w_ki D_il);
  * h-level: each Bernstein coefficient is a univariate polynomial in h, positive on [h0, h1] by a
    univariate Bernstein certificate (subdivision), checked by `linear_combination`.
Exponents are written `^ (n : ℕ)` (fast elaboration).  Lean re-checks every identity.
"""
from fractions import Fraction as Fr
from math import comb, lcm
from plan3 import padd, pmul, pscale, bern1
from plan4 import coeffs_in, shift_scale, bern01

def lnum(q):
    q = Fr(q)
    if q.denominator == 1:
        return str(q.numerator) if q.numerator >= 0 else f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})" if q.numerator >= 0 else f"(({q.numerator}) / {q.denominator})"

def P_(name, e):
    if e == 0: return None
    if e == 1: return name
    return f"{name} ^ ({e} : ℕ)"

def upoly(cs, var):
    """Lean string for sum cs[i] var^i (Fractions)."""
    terms = []
    for i, c in enumerate(cs):
        if c == 0: continue
        a = abs(c)
        f = [lnum(a)] if (a != 1 or i == 0) else []
        if i: f.append(P_(var, i))
        terms.append(("-" if c < 0 else "+", " * ".join(f)))
    if not terms: return "0"
    s = ("-" if terms[0][0] == "-" else "") + terms[0][1]
    for sg, b in terms[1:]: s += f" {sg} {b}"
    return s

def dict_to_list(d):
    n = max([m[0] for m in d] + [0])
    cs = [d.get((i,), Fr(0)) for i in range(n+1)]
    while len(cs) > 1 and cs[-1] == 0: cs = cs[:-1]
    return cs

# ---------------- generic lemmas ----------------
def beta0g_str(n, k, cs, g):
    """C(n,k) beta_k on [0, g] for coefficient strings cs (list), g string."""
    parts = []
    for i in range(k+1):
        w = comb(n-i, k-i)
        fs = [] if w == 1 else [str(w)]
        fs.append(cs[i])
        if i: fs.append(f"{g} ^ ({i} : ℕ)" if i > 1 else g)
        parts.append(" * ".join(fs))
    return " + ".join(parts)

def poly_str(cs, y):
    return " + ".join([cs[0]] + [f"{cs[i]} * {y}" if i == 1 else f"{cs[i]} * {y} ^ ({i} : ℕ)" for i in range(1, len(cs))])

def lemma0g(n):
    cs = [f"c{i}" for i in range(n+1)]
    poly = poly_str(cs, "y")
    betas = [beta0g_str(n, k, cs, "g") for k in range(n+1)]
    hyps = "\n    ".join(f"(hb{k} : 0 < {betas[k]})" for k in range(n+1))
    def term(k):
        fs = [f"({betas[k]})"]
        if k >= 1: fs.append(P_("y", k))
        if n-k >= 1: fs.append(P_("(g - y)", n-k))
        return " * ".join(fs)
    rhs = " + ".join(term(k) for k in range(n+1))
    args = " ".join(f"hb{k}" for k in range(n+1))
    return f"""/-- Bernstein positivity of degree {n} on `[0, g]`, with abstract coefficients. -/
theorem nsfBern0g{n} {{g y {' '.join(cs)} : ℝ}} (h0 : 0 ≤ y) (h1 : y ≤ g) (hg : 0 < g)
    {hyps} :
    0 < {poly} := by
  have hpos := nsfBernPos{n} (a := y) (b := g - y) h0 (by linarith) (by linarith) {args}
  have e : g ^ ({n} : ℕ) * ({poly}) = {rhs} := by ring
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)
"""

def wI(n, lo, hi):
    """weights: C(n,k) beta_k = sum_i w[k][i] c_i on [lo, hi]"""
    W = []
    for k in range(n+1):
        row = []
        for i in range(n+1):
            s = Fr(0)
            for l in range(max(0, i-(n-k)), min(k, i)+1):
                s += Fr(comb(k, l)*comb(n-k, i-l)*comb(n, k), comb(n, i)) * Fr(hi)**l * Fr(lo)**(i-l)
            row.append(s)
        W.append(row)
    return W

def lin_str(ws, cs):
    parts = []
    for w, c in zip(ws, cs):
        if w == 0: continue
        parts.append(c if w == 1 else f"{lnum(w)} * {c}")
    return " + ".join(parts) if parts else "0"

def ivname(n, lo, hi):
    def f(q):
        q = Fr(q); return f"{q.numerator}_{q.denominator}"
    return f"nsfBernI{n}_{f(lo)}_{f(hi)}"

def lemmaI(n, lo, hi):
    lo, hi = Fr(lo), Fr(hi)
    cs = [f"c{i}" for i in range(n+1)]
    poly = poly_str(cs, "y")
    W = wI(n, lo, hi)
    betas = [lin_str(W[k], cs) for k in range(n+1)]
    hyps = "\n    ".join(f"(hb{k} : 0 < {betas[k]})" for k in range(n+1))
    A = f"(y - {lnum(lo)})"; B = f"({lnum(hi)} - y)"
    def term(k):
        fs = [f"({betas[k]})"]
        if k >= 1: fs.append(P_(A, k))
        if n-k >= 1: fs.append(P_(B, n-k))
        return " * ".join(fs)
    rhs = " + ".join(term(k) for k in range(n+1))
    args = " ".join(f"hb{k}" for k in range(n+1))
    return f"""/-- Bernstein positivity of degree {n} on `[{lo}, {hi}]`, with abstract coefficients. -/
theorem {ivname(n, lo, hi)} {{y {' '.join(cs)} : ℝ}} (h0 : {lnum(lo)} ≤ y) (h1 : y ≤ {lnum(hi)})
    {hyps} :
    0 < {poly} := by
  have hpos := nsfBernPos{n} (a := {A}) (b := {B}) (by linarith) (by linarith) (by linarith) {args}
  have e : ({lnum(hi - lo)} : ℝ) ^ ({n} : ℕ) * ({poly}) = {rhs} := by ring
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos (by norm_num)
"""

# ---------------- univariate leaves ----------------
def uni_split(cs, lo, hi, depth=0, maxdepth=14):
    b = bern1(cs, lo, hi)
    if min(b) > 0: return [(lo, hi, b)]
    if depth >= maxdepth or b[0] <= 0 or b[-1] <= 0:
        raise RuntimeError(f"uni_split failed near [{float(lo)},{float(hi)}]")
    mid = (lo + hi) / 2
    return uni_split(cs, lo, mid, depth+1, maxdepth) + uni_split(cs, mid, hi, depth+1, maxdepth)

def lin_forms(lo, hi, var):
    D = lcm(lo.denominator, hi.denominator)
    A = int(lo * D); B = int(hi * D)
    if D == 1:
        a = f"({var} - {lnum(A)})" if A != 0 else var
        b = f"({lnum(B)} - {var})"
    else:
        a = f"({D} * {var} - {lnum(A)})" if A != 0 else f"({D} * {var})"
        b = f"({lnum(B)} - {D} * {var})"
    return a, b, B - A

class Out:
    def __init__(self): self.code = []; self.nleaf = 0
    def add(self, s): self.code.append(s)

def emit_leaf(out, name, cs, h0, h1, stmt, unfold):
    """theorem name (h) (hh0 : h0 ≤ h) (hh1 : h ≤ h1) : 0 < stmt, where stmt (after `unfold`) equals
    the univariate polynomial with coefficients cs."""
    h0, h1 = Fr(h0), Fr(h1)
    leaves = uni_split(cs, h0, h1)
    unf = f"unfold {unfold}; " if unfold else ""
    for li, (a_, b_, bb) in enumerate(leaves):
        n_ = len(bb) - 1
        eps = min(bb)
        af, bf, H = lin_forms(a_, b_, "h")
        cs_ = [(bb[i] - eps) * comb(n_, i) for i in range(n_+1)]
        M = 1
        for c in cs_ + [eps]: M = lcm(M, c.denominator)
        ci = [int(c * M) for c in cs_]
        K = M * H**n_
        terms = []
        for i in range(n_+1):
            if ci[i] == 0: continue
            fs = [str(ci[i])] + [f for f in (P_("a", i), P_("b", n_-i)) if f]
            terms.append(" * ".join(fs))
        S = " + ".join(terms) if terms else "0"
        out.add(f"""private theorem {name}_bp{li} (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 ≤ {S} := by positivity

private theorem {name}_l{li} (h : ℝ) (h0 : {lnum(a_)} ≤ h) (h1 : h ≤ {lnum(b_)}) :
    0 < {stmt} := by
  {unf}linear_combination (1 / {K} : ℝ) * {name}_bp{li} {af} {bf} (by linarith) (by linarith)
""")
        out.nleaf += 1
    if len(leaves) == 1:
        return f"{name}_l0"
    body = []; cur = "h0"
    for li in range(len(leaves)):
        a_, b_, _ = leaves[li]
        if li == len(leaves) - 1:
            body.append(f"  exact {name}_l{li} h {cur} h1")
        else:
            body.append(f"  rcases le_total h {lnum(b_)} with hc{li} | hc{li}")
            body.append(f"  · exact {name}_l{li} h {cur} hc{li}")
            cur = f"hc{li}"
    out.add(f"""private theorem {name} (h : ℝ) (h0 : {lnum(h0)} ≤ h) (h1 : h ≤ {lnum(h1)}) :
    0 < {stmt} := by
""" + "\n".join(body) + "\n")
    return name

def uni_count(cs, lo, hi):
    try: return len(uni_split(cs, Fr(lo), Fr(hi)))
    except RuntimeError: return None

# ---------------- planning ----------------
def structure(d, jlo):
    """d: dict in (h, j, y) -> D[i][l] univariate coefficient lists, s = j - jlo."""
    # shift j -> s + jlo
    cs = coeffs_in(d, 1)   # coefficients of j^l, dicts in (h, y)
    one = {(0, 0): Fr(1)}
    lo = {(0, 0): Fr(jlo)} if jlo else {}
    sh = shift_scale(cs, lo, one, one)   # coefficients of s^l, dicts in (h, y)
    ny = max([m[1] for c in sh for m in c] + [0])
    nl = len(sh) - 1
    D = [[[] for _ in range(nl+1)] for _ in range(ny+1)]
    for l, c in enumerate(sh):
        by_y = coeffs_in(c, 1) if c else []
        for i in range(ny+1):
            di = by_y[i] if i < len(by_y) else {}
            D[i][l] = dict_to_list(di) if di else [Fr(0)]
    return D

def lpoly_mul(a, b):
    r = [Fr(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def lpoly_add(a, b, s=1):
    n = max(len(a), len(b)); r = [Fr(0)]*n
    for i, x in enumerate(a): r[i] += x
    for i, y in enumerate(b): r[i] += s*y
    return r
def lpoly_scale(a, s): return [x*s for x in a]

def betas_j(E, g, mdeg):
    """E: list (l) of univariate coefficient lists; g: univariate list; returns list (m) of univariate
    lists: C(mdeg, m) beta_m = sum_{l<=m} C(mdeg-l, m-l) E_l g^l"""
    gp = [[Fr(1)]]
    for _ in range(mdeg): gp.append(lpoly_mul(gp[-1], g))
    out = []
    for m in range(mdeg+1):
        acc = [Fr(0)]
        for l in range(min(m, len(E)-1)+1):
            acc = lpoly_add(acc, lpoly_scale(lpoly_mul(E[l], gp[l]), comb(mdeg-l, m-l)))
        while len(acc) > 1 and acc[-1] == 0: acc = acc[:-1]
        out.append(acc)
    return out

def plan_piece(D, g, h0, h1, ylo, yhi, eys=(0, 1, 2), ejs=(0, 1, 2, 3, 4, 5, 6)):
    ny = len(D) - 1; nl = len(D[0]) - 1
    for ey in eys:
        n = ny + ey
        if n > 20: break
        W = wI(n, ylo, yhi)
        plan_k = []; ok = True; tot = 0
        for k in range(n+1):
            E = []
            for l in range(nl+1):
                acc = [Fr(0)]
                for i in range(ny+1):
                    if W[k][i] != 0: acc = lpoly_add(acc, lpoly_scale(D[i][l], W[k][i]))
                E.append(acc)
            found = None
            for ej in ejs:
                md = nl + ej
                if md > 20: break
                bs = betas_j(E, g, md)
                cnt = 0
                for bm in bs:
                    c = uni_count(bm, h0, h1)
                    if c is None: cnt = None; break
                    cnt += c
                if cnt is not None: found = (md, cnt, E, bs); break
            if found is None: ok = False; break
            plan_k.append(found); tot += found[1]
        if ok: return (n, W, plan_k, tot)
    return None

def plan_all(D, g, h0, h1, ylo, yhi, depth=0, maxdepth=4):
    r = plan_piece(D, g, h0, h1, ylo, yhi)
    if r is not None: return [(ylo, yhi, r)]
    if depth >= maxdepth: raise RuntimeError(f"plan failed on y in [{float(ylo)},{float(yhi)}]")
    mid = (ylo + yhi) / 2
    return plan_all(D, g, h0, h1, ylo, mid, depth+1, maxdepth) + plan_all(D, g, h0, h1, mid, yhi, depth+1, maxdepth)

# ---------------- emission ----------------
def emit_job(out, X, D, g, gstr, jlo, h0, h1, plan, needI, need0g):
    """X: name prefix. D: structure. g: univariate list for g(h), gstr: Lean string of g(h).
    s-variable string: (j - jlo). Emits D defs, leaves, levels, and X_pos."""
    ny = len(D) - 1; nl = len(D[0]) - 1
    sstr = "j" if jlo == 0 else f"(j - {lnum(jlo)})"
    # D definitions
    for i in range(ny+1):
        for l in range(nl+1):
            out.add(f"/-- Coefficient of `y^{i} s^{l}` in `{X}`. -/\nnoncomputable def {X}D{i}_{l} (h : ℝ) : ℝ :=\n  {upoly(D[i][l], 'h')}\n")
    allD = " ".join(f"{X}D{i}_{l}" for i in range(ny+1) for l in range(nl+1))
    # c_i strings (padded with zeros for elevation): sum_l D_il h * s^l
    def cstr(i, n):
        if i > ny: return "0"
        return "(" + poly_str([f"{X}D{i}_{l} h" for l in range(nl+1)], sstr) + ")"
    for pi, (ylo, yhi, (n, W, plan_k, tot)) in enumerate(plan):
        needI.add((n, ylo, yhi))
        cs = [cstr(i, n) for i in range(n+1)]
        kthms = []
        for k in range(n+1):
            md, cnt, E, bs = plan_k[k]
            need0g.add(md)
            # E_l definitions (expanded univariate polynomials)
            Es = []
            for l in range(md+1):
                if l > nl: Es.append("0"); continue
                out.add(f"noncomputable def {X}E{pi}_{k}_{l} (h : ℝ) : ℝ := {upoly(E[l], 'h')}\n")
                Es.append(f"{X}E{pi}_{k}_{l} h")
            leafnames = []
            for m in range(md+1):
                stmt = beta0g_str(md, m, Es, f"({gstr})")
                used = [f"{X}E{pi}_{k}_{l}" for l in range(min(m, nl)+1)]
                nm = emit_leaf(out, f"{X}_y{pi}_k{k}_m{m}", bs[m], h0, h1, stmt, " ".join(used))
                leafnames.append(nm)
            yb = lin_str(W[k], cs)
            target = poly_str(Es, sstr)
            Eunf = " ".join(f"{X}E{pi}_{k}_{l}" for l in range(min(md, nl)+1)) + " " + " ".join(sorted({f"{X}D{i}_{l}" for i in range(min(ny, n)+1) for l in range(nl+1) if W[k][i] != 0}))
            out.add(f"""private theorem {X}_y{pi}_k{k} (h j : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) :
    0 < {yb} := by
  have e : {yb} = {target} := by unfold {Eunf}; ring
  rw [e]
  exact nsfBern0g{md} hs0 hs1 (by linarith) {' '.join(f'({nm} h hh0 hh1)' for nm in leafnames)}
""")
            kthms.append(f"{X}_y{pi}_k{k}")
        unpadded = poly_str([cstr(i, ny) for i in range(ny+1)], "y")
        padded = poly_str(cs, "y")
        conv = "" if n == ny else f"""
  have e : {unpadded} = {padded} := by ring
  rw [e]"""
        out.add(f"""private theorem {X}_y{pi} (h j y : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hy0 : {lnum(ylo)} ≤ y) (hy1 : y ≤ {lnum(yhi)}) :
    0 < {unpadded} := by{conv}
  exact {ivname(n, ylo, yhi)} hy0 hy1 {' '.join(f'({k} h j hh0 hh1 hs0 hs1)' for k in kthms)}
""")
    # final: the polynomial in the unpadded form sum_{i<=ny} c_i y^i
    final = poly_str([cstr(i, ny) for i in range(ny+1)], "y")
    body = []; cur = "hy0"
    for pi, (ylo, yhi, (n, *_)) in enumerate(plan):
        line = f"{X}_y{pi} h j y hh0 hh1 hs0 hs1 {cur} {'hy1' if pi == len(plan)-1 else f'hc{pi}'}"
        if pi == len(plan) - 1:
            body.append(f"  exact {line}")
        else:
            body.append(f"  rcases le_total y {lnum(yhi)} with hc{pi} | hc{pi}")
            body.append(f"  · exact {line}")
            cur = f"hc{pi}"
    out.add(f"""/-- **Positivity of `{X}`** on `{h0} ≤ h ≤ {h1}`, `0 ≤ s ≤ g(h)`, `{plan[0][0]} ≤ y ≤ {plan[-1][1]}`. -/
theorem {X}_pos (h j y : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hy0 : {lnum(plan[0][0])} ≤ y) (hy1 : y ≤ {lnum(plan[-1][1])}) :
    0 < {final} := by
""" + "\n".join(body) + "\n")
    return final

def plan_sym0g(D, g, h0, h1, Y, eys=(0, 1, 2), ejs=(0, 1, 2)):
    """y in [0, Y(h)] (Y univariate list). Bernstein weights: C(n,k) beta_k = sum_{i<=k} C(n-i,k-i) c_i Y^i."""
    ny = len(D) - 1; nl = len(D[0]) - 1
    for ey in eys:
        n = ny + ey
        if n > 20: break
        Yp = [[Fr(1)]]
        for _ in range(n): Yp.append(lpoly_mul(Yp[-1], Y))
        plan_k = []; ok = True; tot = 0
        for k in range(n+1):
            E = []
            for l in range(nl+1):
                acc = [Fr(0)]
                for i in range(min(k, ny)+1):
                    acc = lpoly_add(acc, lpoly_scale(lpoly_mul(D[i][l], Yp[i]), comb(n-i, k-i)))
                E.append(acc)
            found = None
            for ej in ejs:
                md = nl + ej
                if md > 20: break
                bs = betas_j(E, g, md)
                cnt = 0
                for bm in bs:
                    c = uni_count(bm, h0, h1)
                    if c is None: cnt = None; break
                    cnt += c
                if cnt is not None: found = (md, cnt, E, bs); break
            if found is None: ok = False; break
            plan_k.append(found); tot += found[1]
        if ok: return (n, None, plan_k, tot)
    return None


def lemma_pos(d):
    def term(j):
        fs = [f"c{j}"]
        if j >= 1: fs.append(P_("a", j))
        if d-j >= 1: fs.append(P_("b", d-j))
        return " * ".join(fs)
    cs = " ".join(f"c{j}" for j in range(d+1))
    hs = " ".join(f"(h{j} : 0 < c{j})" for j in range(d+1))
    expr = " + ".join(term(j) for j in range(d+1))
    rest0 = " + ".join(term(j) for j in range(1, d+1))
    restd = " + ".join(term(j) for j in range(0, d))
    return f"""/-- A Bernstein form of degree {d} with positive coefficients is positive. -/
theorem nsfBernPos{d} {{a b : ℝ}} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {{{cs} : ℝ}}
    {hs} :
    0 < {expr} := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < {term(d)} := by positivity
    have h'' : 0 ≤ {restd} := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < {term(0)} := by positivity
    have h'' : 0 ≤ {rest0} := by positivity
    linarith
"""
