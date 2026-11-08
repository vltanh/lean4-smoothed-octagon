"""Univariate positivity certificates: 0 < f(v) on [V0, V1], f rational in v."""
import re
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import lq, lpoly_terms, F

w = sp.symbols('w')


def lfr(fr):
    return lq(fr)


def bern_coeffs(H, W):
    n = max(H)
    return [sum(Fr(comb(k, i), comb(n, i)) * H.get(i, Fr(0)) * W ** i for i in range(k + 1)) for k in range(n + 1)]


def lpow(var, k):
    return f"{var} ^ ({k} : ℕ)"


def emit_uni(name, v, num, den_factors, V0, V1, side, lean_head, lean_hyps, lean_prelude, doc, vname=None):
    """num: sympy polynomial in v (numerator, positive on [V0,V1] after sign fix).
    den_factors: list of (lean_string, proof_string) of positive factors whose product is DEN.
    side: 'hi' -> v = V1 - w, 'lo' -> v = V0 + w.
    lean_head: Lean statement `0 < EXPR`; lean_prelude: proof lines establishing
    `key : EXPR * DEN = NUM(v)` (must end with key in context)."""
    W = Fr(V1) - Fr(V0)
    V0s = sp.Rational(Fr(V0).numerator, Fr(V0).denominator)
    V1s = sp.Rational(Fr(V1).numerator, Fr(V1).denominator)
    sub = (V1s - w) if side == 'hi' else (V0s + w)
    Pw = sp.Poly(sp.expand(num.subs(v, sub)), w)
    H = {mon[0]: F(c) for mon, c in Pw.terms()}
    n = max(H)
    bs = bern_coeffs(H, W)
    assert all(b > 0 for b in bs), "Bernstein coefficients not all positive"
    m = min(bs)
    Pv = sp.Poly(num, v)
    vn = vname or str(v)
    num_l = lpoly_terms([(F(c), (lpow(vn, mon[0]) if mon[0] > 1 else (vn if mon[0] == 1 else "1"))) for mon, c in Pv.terms()])
    L = ["set_option maxHeartbeats 4000000 in", f"/-- {doc} -/",
         f"theorem {name} " + " ".join(lean_hyps) + " :", f"    {lean_head} := by"]
    L += lean_prelude
    # NUM > 0
    if side == 'hi':
        L.append(f"  obtain ⟨w, hw⟩ : ∃ w, w = {lfr(V1)} - {vn} := ⟨_, rfl⟩")
        L.append(f"  have hw0 : 0 ≤ w := by rw [hw]; linarith")
        L.append(f"  have hw1 : 0 ≤ {lfr(W)} - w := by rw [hw]; linarith")
        L.append(f"  have hv : {vn} = {lfr(V1)} - w := by rw [hw]; ring")
    else:
        L.append(f"  obtain ⟨w, hw⟩ : ∃ w, w = {vn} - {lfr(V0)} := ⟨_, rfl⟩")
        L.append(f"  have hw0 : 0 ≤ w := by rw [hw]; linarith")
        L.append(f"  have hw1 : 0 ≤ {lfr(W)} - w := by rw [hw]; linarith")
        L.append(f"  have hv : {vn} = {lfr(V0)} + w := by rw [hw]; ring")
    items = []
    for k in range(n + 1):
        cf = (bs[k] - m) * comb(n, k)
        if cf == 0:
            continue
        items.append((f"{lfr(cf)} * w ^ ({k} : ℕ) * ({lfr(W)} - w) ^ ({n - k} : ℕ)",
                      f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(cf)}) (pow_nonneg hw0 {k})) (pow_nonneg hw1 {n - k}))"))
    from emit import balanced_sum
    st, sp_ = balanced_sum(items)
    L.append(f"  have hS := {sp_}")
    L.append(f"  have hN : 0 < {num_l} := by")
    L.append(f"    have hpos : 0 < ({lfr(W)} : ℝ) ^ ({n} : ℕ) * ({num_l}) :=")
    L.append(f"      lt_of_lt_of_eq (add_pos_of_nonneg_of_pos hS (by norm_num : (0 : ℝ) < {lfr(m)} * ({lfr(W)} : ℝ) ^ ({n} : ℕ))) (by rw [hv]; ring)")
    L.append(f"    exact pos_of_mul_pos_right hpos (by norm_num)")
    for i, (f, p) in enumerate(den_factors):
        L.append(f"  have hf{i} : 0 < {f} := {p}")
    pr = "hf0"
    for i in range(1, len(den_factors)):
        pr = f"(mul_pos {pr} hf{i})"
    L.append("  have hden : 0 < " + " * ".join(f"({f})" for f, _ in den_factors) + f" := {pr}")
    L.append("  exact pos_of_mul_pos_left (by rw [key]; exact hN) hden.le")
    return "\n".join(L)
