import re
"""Lean emission of a certified Claim (see claim.py)."""
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import Claim, lq, lmono, lpoly_terms, z, A, s, mu

XV = sp.symbols('x al be u')


def lexpr(e):
    """sympy expression in x al be u -> Lean string (variables x a b u)."""
    s_ = sp.sstr(e, order='none').replace('al', 'a').replace('be', 'b')
    s_ = re.sub(r"\*\*(\d+)", r" ^ (\1 : ℕ)", s_)
    return s_


def lfr(fr):
    return lq(fr)


def poly_lean_xabu(num):
    """Expanded polynomial in x al be u -> Lean string."""
    P = sp.Poly(num, *XV)
    terms = []
    for mon, cf in P.terms():
        parts = []
        for v, e in zip(('x', 'a', 'b', 'u'), mon):
            if e == 1:
                parts.append(v)
            elif e > 1:
                parts.append(f"{v} ^ ({e} : ℕ)")
        m = " * ".join(parts) if parts else "1"
        terms.append((Fr(int(sp.Rational(cf).p), int(sp.Rational(cf).q)), m))
    return lpoly_terms(terms)


def balanced_sum(items):
    """items: list of (lean_term, lean_proof). Returns (term, proof) of the sum, balanced."""
    if not items:
        return "0", "le_refl _"
    while len(items) > 1:
        nxt = []
        for i in range(0, len(items) - 1, 2):
            (t1, p1), (t2, p2) = items[i], items[i + 1]
            nxt.append((f"({t1} + {t2})", f"(add_nonneg {p1} {p2})"))
        if len(items) % 2:
            nxt.append(items[-1])
        items = nxt
    return items[0]


def prefix(i, j, l, hz='hz', hA='hA0', hm='hm0'):
    parts, prfs = [], []
    if i:
        parts.append(f"z ^ ({i} : ℕ)"); prfs.append(f"(pow_nonneg {hz} {i})")
    if j:
        parts.append(f"A ^ ({j} : ℕ)"); prfs.append(f"(pow_nonneg {hA} {j})")
    if l:
        parts.append(f"m ^ ({l} : ℕ)"); prfs.append(f"(pow_nonneg {hm} {l})")
    if not parts:
        return "1", "zero_le_one"
    t = parts[0]; p = prfs[0]
    for pt, pp in zip(parts[1:], prfs[1:]):
        t = f"{t} * {pt}"; p = f"(mul_nonneg {p} {pp})"
    return t, p


def emit_claim(c: Claim, lean_name, lean_expr, unfold, doc):
    """Return Lean source of a theorem `lean_name : 0 ≤ lean_expr` under the domain hypotheses."""
    X0, sx, Zmax = c.X0, c.sx, c.Zmax
    c0, c1 = c.Amax
    C0, tmax, mumax = c.C0, c.tmax, c.mumax
    # original-variable numerator/denominator
    num, den = c.num_x, c.den_x
    num_l = poly_lean_xabu(num)
    den_l = lexpr(den)
    # hypotheses
    if sx == 1:
        xlo, xhi = X0, X0 + Zmax
        amax_x = f"{lfr(c0)} + {lfr(c1)} * (x - {lfr(X0)})"
        zdef = f"x - {lfr(X0)}"; xsub = f"{lfr(X0)} + z"
    else:
        xlo, xhi = X0 - Zmax, X0
        amax_x = f"{lfr(c0)} + {lfr(c1)} * ({lfr(X0)} - x)"
        zdef = f"{lfr(X0)} - x"; xsub = f"{lfr(X0)} - z"
    hyps = [f"(hx0 : {lfr(xlo)} ≤ x)", f"(hx1 : x ≤ {lfr(xhi)})", "(ha0 : 1 ≤ a)",
            f"(ha1 : a - 1 ≤ {amax_x})"]
    if c.has_b:
        hyps += [f"(hb0 : x + {lfr(C0 - tmax)} * (a - 1) ≤ b)", f"(hb1 : b ≤ x + {lfr(C0 + tmax)} * (a - 1))"]
    if c.has_u:
        hyps += ["(hu0 : 3 / 4 ≤ u)", f"(hu1 : u ≤ 3 / 4 + {lfr(mumax)})"]
    L = []
    L.append("set_option maxHeartbeats 2000000 in")
    L.append(f"/-- {doc} -/")
    L.append(f"theorem {lean_name} {{x a b u : ℝ}} " + " ".join(hyps) + " :")
    L.append(f"    0 ≤ {lean_expr} := by")
    L.append("  have hx : 0 < x := by linarith only [hx0]")
    L.append("  have ha : 0 < a := by linarith only [ha0]")
    if c.has_b:
        L.append(f"  have hb : 0 < b := by linarith only [hx0, hb0, mul_nonneg (show (0 : ℝ) ≤ {lfr(C0 - tmax)} by norm_num) (show (0 : ℝ) ≤ a - 1 by linarith only [ha0])]")
    L.append(f"  have hden : 0 < {den_l} := by positivity")
    L.append(f"  have key : ({lean_expr}) * ({den_l}) = {num_l} := by")
    L.append(f"    simp only [{', '.join(unfold)}]")
    L.append("    field_simp")
    L.append("    ring")
    L.append(f"  have hP : 0 ≤ {num_l} := by")
    L.append(f"    obtain ⟨z, rfl⟩ : ∃ z, x = {xsub} := ⟨{zdef}, by ring⟩")
    L.append("    obtain ⟨A, rfl⟩ : ∃ A, a = 1 + A := ⟨a - 1, by ring⟩")
    if c.has_b:
        L.append(f"    obtain ⟨s, rfl⟩ : ∃ s, b = {xsub} + {lfr(C0)} * A + s := ⟨b - ({xsub}) - {lfr(C0)} * A, by ring⟩")
    if c.has_u:
        L.append("    obtain ⟨m, rfl⟩ : ∃ m, u = 3 / 4 + m := ⟨u - 3 / 4, by ring⟩")
    L.append("    have hz : 0 ≤ z := by linarith only [hx0, hx1]")
    L.append(f"    have hz1 : z ≤ {lfr(Zmax)} := by linarith only [hx0, hx1]")
    L.append("    have hA0 : 0 ≤ A := by linarith only [ha0]")
    L.append(f"    have hA1 : A ≤ {lfr(c0)} + {lfr(c1)} * z := by linarith only [ha1]")
    if c.has_b:
        L.append(f"    have hs : |s| ≤ {lfr(tmax)} * A := abs_le.2 ⟨by linarith only [hb0], by linarith only [hb1]⟩")
    if c.has_u:
        L.append("    have hm0 : 0 ≤ m := by linarith only [hu0]")
        L.append(f"    have hm1 : m ≤ {lfr(mumax)} := by linarith only [hu1]")
    # termwise terms
    amax_z = f"({lfr(c0)} + {lfr(c1)} * z)"
    items = []
    for (i, j, k, l, p) in c.T1:
        pt, pp = prefix(i, j, l)
        ap = abs(p)
        if p > 0:
            t = f"{lfr(ap)} * ({pt}) * (s ^ ({k} : ℕ) + ({lfr(tmax)} * A) ^ ({k} : ℕ))"
            pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(ap)}) {pp}) (hh1_tw_spos {k} hs))"
        else:
            t = f"{lfr(ap)} * ({pt}) * (({lfr(tmax)} * A) ^ ({k} : ℕ) - s ^ ({k} : ℕ))"
            pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(ap)}) {pp}) (hh1_tw_sneg {k} hs))"
        items.append((t, pr))
    for (i, j, l, v) in c.T2:
        if v == 0:
            continue
        if v > 0:
            pt, pp = prefix(i, j, l)
            items.append((f"{lfr(v)} * ({pt})", f"(mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(v)}) {pp})"))
        else:
            pt, pp = prefix(i, j, 0)
            items.append((f"{lfr(-v)} * ({pt}) * ({lfr(mumax)} ^ ({l} : ℕ) - m ^ ({l} : ℕ))",
                          f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(-v)}) {pp}) (hh1_tw_sub {l} hm0 hm1))"))
    for (i, j, v) in c.T3:
        if v == 0:
            continue
        if v > 0:
            pt, pp = prefix(i, j, 0)
            items.append((f"{lfr(v)} * ({pt})", f"(mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(v)}) {pp})"))
        else:
            pt, pp = prefix(i, 0, 0)
            items.append((f"{lfr(-v)} * ({pt}) * ({amax_z} ^ ({j} : ℕ) - A ^ ({j} : ℕ))",
                          f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(-v)}) {pp}) (hh1_tw_sub {j} hA0 hA1))"))
    # H and its Bernstein certificate (single piece)
    H = c.H
    n = max(H) if H else 0
    Hl = lpoly_terms([(H[i], lmono(i, 0, 0, 0)) for i in sorted(H)])
    assert c.cert is not None and len(c.cert) == 1, "multi-piece Bernstein not implemented"
    Zm = Zmax
    bs = []
    for k in range(n + 1):
        bk = sum(Fr(comb(k, i), comb(n, i)) * H.get(i, Fr(0)) * Zm ** i for i in range(k + 1))
        bs.append(bk)
    bitems = []
    for k, bk in enumerate(bs):
        coef = bk * comb(n, k)
        t = f"{lfr(coef)} * z ^ ({k} : ℕ) * ({lfr(Zm)} - z) ^ ({n - k} : ℕ)"
        pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(coef)}) (pow_nonneg hz {k})) (pow_nonneg hZ {n - k}))"
        bitems.append((t, pr))
    bt, bp = balanced_sum(bitems)
    L.append(f"    have hZ : 0 ≤ {lfr(Zm)} - z := by linarith only [hz1]")
    L.append(f"    have hB := {bp}")
    L.append(f"    have hH : 0 ≤ {Hl} :=")
    L.append(f"      (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < ({lfr(Zm)} : ℝ) ^ ({n} : ℕ))).1")
    L.append("        (le_of_le_of_eq hB (by ring))")
    tt, tp = balanced_sum(items)
    L.append(f"    have hT := {tp}")
    L.append("    exact le_of_le_of_eq (add_nonneg hH hT) (by ring)")
    L.append(f"  have h : 0 ≤ ({lean_expr}) * ({den_l}) := by rw [key]; exact hP")
    L.append("  exact (mul_nonneg_iff_of_pos_right hden).1 h")
    return "\n".join(L)
