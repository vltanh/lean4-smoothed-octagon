"""Lean emission of a certified Claim3 (variables z, A, t = b - x, m)."""
import re
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import lq, lpoly_terms
from emit import balanced_sum, prefix

XT = sp.symbols('x al t u')


def lfr(fr):
    return lq(fr)


def lexpr(e):
    s_ = sp.sstr(e, order='none').replace('al', 'a')
    s_ = re.sub(r"\*\*(\d+)", r" ^ (\1 : ℕ)", s_)
    return s_


def poly_lean(num, names=('x', 'a', 't', 'u'), gens=XT):
    P = sp.Poly(num, *gens)
    terms = []
    for mon, cf in P.terms():
        parts = []
        for v, e in zip(names, mon):
            if e == 1:
                parts.append(v)
            elif e > 1:
                parts.append(f"{v} ^ ({e} : ℕ)")
        mm = " * ".join(parts) if parts else "1"
        cf = sp.Rational(cf)
        terms.append((Fr(int(cf.p), int(cf.q)), mm))
    return lpoly_terms(terms)


def bern_lines(H, Zm, var='z', hz='hz', hZ='hZ', name='hH', indent='    '):
    """Lines proving `0 ≤ H(var)` on [0, Zm] (single Bernstein piece). Returns (lines, Hlean)."""
    n = max(H) if H else 0
    Hl = lpoly_terms([(H[i], (f"{var} ^ ({i} : ℕ)" if i > 1 else (var if i == 1 else "1"))) for i in sorted(H)])
    bitems = []
    for k in range(n + 1):
        bk = sum(Fr(comb(k, i), comb(n, i)) * H.get(i, Fr(0)) * Zm ** i for i in range(k + 1))
        assert bk > 0
        coef = bk * comb(n, k)
        tt = f"{lfr(coef)} * {var} ^ ({k} : ℕ) * ({lfr(Zm)} - {var}) ^ ({n - k} : ℕ)"
        pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(coef)}) (pow_nonneg {hz} {k})) (pow_nonneg {hZ} {n - k}))"
        bitems.append((tt, pr))
    bt, bp = balanced_sum(bitems)
    L = [f"{indent}have {hZ} : 0 ≤ {lfr(Zm)} - {var} := by linarith only [{hz}1]",
         f"{indent}have {name}B := {bp}",
         f"{indent}have {name} : 0 ≤ {Hl} :=",
         f"{indent}  (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < ({lfr(Zm)} : ℝ) ^ ({n} : ℕ))).1",
         f"{indent}    (le_of_le_of_eq {name}B (by ring))"]
    return L, Hl


def emit_claim3(c, lean_name, lean_expr, unfold, doc, pre_key=()):
    X0, sx, Zmax = c.X0, c.sx, c.Zmax
    c0, c1 = c.Amax
    Clo, Chi, mumax = c.Clo, c.Chi, c.mumax
    num_l = poly_lean(c.num_x)
    den_l = lexpr(c.den_x)
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
        hyps += [f"(hb0 : x + {lfr(Clo)} * (a - 1) ≤ b)", f"(hb1 : b ≤ x + {lfr(Chi)} * (a - 1))"]
    if c.has_u:
        hyps += ["(hu0 : 3 / 4 ≤ u)", f"(hu1 : u ≤ 3 / 4 + {lfr(mumax)})"]
    L = ["set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 20000 in",
         f"/-- {doc} -/",
         f"theorem {lean_name} {{x a b u : ℝ}} " + " ".join(hyps) + " :",
         f"    0 ≤ {lean_expr} := by",
         "  have hx : 0 < x := by linarith only [hx0]",
         "  have ha : 0 < a := by linarith only [ha0]"]
    if c.has_b:
        L += ["  obtain ⟨t, rfl⟩ : ∃ t, b = x + t := ⟨b - x, by ring⟩",
              f"  have hCA : 0 ≤ {lfr(Clo)} * (a - 1) := mul_nonneg (by norm_num) (by linarith only [ha0])",
              "  have ht : 0 ≤ t := by linarith only [hb0, hCA]"]
    fl = sp.factor_list(c.den_x)
    facs = []
    if fl[0] != 1:
        facs.append((f"({lexpr(fl[0])} : ℝ)", "by norm_num"))
    hyp_names = "hx0, hx1, ha0" + (", ht, hb0" if c.has_b else "")
    for f_, k_ in fl[1]:
        coeffs = sp.Poly(f_, *XT).coeffs()
        prf = "by positivity" if all(cc > 0 for cc in coeffs) else f"by nlinarith only [{hyp_names}]"
        fs = lexpr(f_)
        if k_ > 1:
            facs.append((f"({fs}) ^ ({k_} : ℕ)", f"pow_pos ({prf}) {k_}"))
        else:
            facs.append((f"({fs})", prf))
    den_l = " * ".join(f_ for f_, _ in facs)
    for i_, (f_, p_) in enumerate(facs):
        L.append(f"  have hf{i_} : 0 < {f_} := {p_}")
    pr_ = "hf0"
    for i_ in range(1, len(facs)):
        pr_ = f"(mul_pos {pr_} hf{i_})"
    L += [f"  {pk}" for pk in pre_key]
    L += [f"  have hden : 0 < {den_l} := {pr_}",
          f"  have key : ({re.sub(r'(?<![A-Za-z0-9_])b(?![A-Za-z0-9_])', '(x + t)', lean_expr) if c.has_b else lean_expr}) * ({den_l}) = {num_l} := by",
          f"    simp only [{', '.join(unfold)}]",
          "    field_simp",
          "    ring",
          f"  have hP : 0 ≤ {num_l} := by",
          f"    obtain ⟨z, rfl⟩ : ∃ z, x = {xsub} := ⟨{zdef}, by ring⟩",
          "    obtain ⟨A, rfl⟩ : ∃ A, a = 1 + A := ⟨a - 1, by ring⟩"]
    if c.has_u:
        L.append("    obtain ⟨m, rfl⟩ : ∃ m, u = 3 / 4 + m := ⟨u - 3 / 4, by ring⟩")
    L += ["    have hz : 0 ≤ z := by linarith only [hx0, hx1]",
          f"    have hz1 : z ≤ {lfr(Zmax)} := by linarith only [hx0, hx1]",
          "    have hA0 : 0 ≤ A := by linarith only [ha0]",
          f"    have hA1 : A ≤ {lfr(c0)} + {lfr(c1)} * z := by linarith only [ha1]"]
    if c.has_b:
        L += [f"    have hClo : 0 ≤ {lfr(Clo)} * A := mul_nonneg (by norm_num) hA0",
              f"    have htlo : {lfr(Clo)} * A ≤ t := by linarith only [hb0]",
              f"    have hthi : t ≤ {lfr(Chi)} * A := by linarith only [hb1]"]
    if c.has_u:
        L += ["    have hm0 : 0 ≤ m := by linarith only [hu0]",
              f"    have hm1 : m ≤ {lfr(mumax)} := by linarith only [hu1]"]
    amax_z = f"({lfr(c0)} + {lfr(c1)} * z)"
    items = []
    for (i, j, k, l, p) in c.T1:
        pt, pp = prefix(i, j, l)
        ap = abs(p)
        if p > 0:
            tt = f"{lfr(ap)} * ({pt}) * (t ^ ({k} : ℕ) - ({lfr(Clo)} * A) ^ ({k} : ℕ))"
            pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(ap)}) {pp}) (hh1_tw_sub {k} hClo htlo))"
        else:
            tt = f"{lfr(ap)} * ({pt}) * (({lfr(Chi)} * A) ^ ({k} : ℕ) - t ^ ({k} : ℕ))"
            pr = f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(ap)}) {pp}) (hh1_tw_sub {k} ht hthi))"
        items.append((tt, pr))
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
    assert c.cert is not None and len(c.cert) == 1
    bl, Hl = bern_lines(c.H, Zmax)
    L += bl
    tt, tp = balanced_sum(items)
    L.append(f"    have hT := {tp}")
    L.append("    exact le_of_le_of_eq (add_nonneg hH hT) (by ring)")
    L.append(f"  exact (mul_nonneg_iff_of_pos_right hden).1 (by rw [key]; exact hP)")
    return "\n".join(L)
