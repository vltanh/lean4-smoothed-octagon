"""Lean emission of a certified ClaimG."""
import re
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from claim import lq, lpoly_terms
from emit import balanced_sum
from emit3 import bern_lines


def lfr(fr):
    return lq(fr)


def lexpr(e, ren):
    s_ = sp.sstr(e, order='none')
    for k, v in ren.items():
        s_ = re.sub(rf"(?<![A-Za-z0-9_]){k}(?![A-Za-z0-9_])", v, s_)
    s_ = re.sub(r"\*\*(\d+)", r" ^ (\1 : ℕ)", s_)
    return s_


def poly_lean(num, gens, names):
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


def emit_claimg(c, lean_name, lean_expr, unfold, doc, vnames, xname='x', extra_hyps=(),
                pos_hyps=(), fac_hyps=None, extra_binders='', key_lines=None):
    """c: certified ClaimG. vnames: Lean names of the termwise variables (same order as c.tvars).
    The theorem binds {xname, vnames...}; hypotheses: X0 ≤ x ≤ X0+Zmax, lo_i ≤ v_i ≤ lo_i + hi_i(x)."""
    X0, sx, Zmax = c.X0, c.sx, c.Zmax
    assert sx == 1
    allv = [xname] + list(vnames)
    gens = [c.xsym] + [t[0] for t in c.tvars]
    ren = {str(g): n for g, n in zip(gens, allv)}
    num_l = poly_lean(c.num_x, gens, allv)
    hyps = [f"(hx0 : {lfr(X0)} ≤ {xname})", f"(hx1 : {xname} ≤ {lfr(X0 + Zmax)})"]
    for i, ((s_, lo, (c0, c1)), vn) in enumerate(zip(c.tvars, vnames)):
        lo = Fr(lo); c0 = Fr(c0); c1 = Fr(c1)
        hyps.append(f"(hv{i}0 : {lfr(lo)} ≤ {vn})")
        hi = f"{lfr(lo + c0 - c1 * X0)} + {lfr(c1)} * {xname}" if c1 != 0 else f"{lfr(lo + c0)}"
        hyps.append(f"(hv{i}1 : {vn} ≤ {hi})")
    hyps += list(extra_hyps)
    L = ["set_option maxHeartbeats 4000000 in", "set_option maxRecDepth 20000 in",
         f"/-- {doc} -/",
         f"theorem {lean_name} {{{' '.join(allv)}{(' ' + extra_binders) if extra_binders else ''} : ℝ}} " + " ".join(hyps) + " :",
         f"    0 ≤ {lean_expr} := by"]
    # denominator factors
    fl = sp.factor_list(c.den_x)
    facs = []
    bases = []
    if fl[0] != 1:
        bases.append((f"({lexpr(fl[0], ren)} : ℝ)", "by norm_num"))
        facs.append((f"({lexpr(fl[0], ren)} : ℝ)", "hb0"))
    hlist = ", ".join(["hx0", "hx1"] + [f"hv{i}0, hv{i}1" for i in range(len(vnames))])
    for f_, k_ in fl[1]:
        fs = lexpr(f_, ren)
        prf = f"by nlinarith only [{hlist}]"
        if fac_hyps and str(f_) in fac_hyps:
            prf = fac_hyps[str(f_)]
        nb = len(bases)
        bases.append((f"({fs})", prf))
        if k_ > 1:
            facs.append((f"({fs}) ^ ({k_} : ℕ)", f"pow_pos hb{nb} {k_}"))
        else:
            facs.append((f"({fs})", f"hb{nb}"))
    for ph in pos_hyps:
        L.append(f"  {ph}")
    for i_, (f_, p_) in enumerate(bases):
        L.append(f"  have hb{i_} : 0 < {f_} := {p_}")
        L.append(f"  have hn{i_} : {f_} ≠ 0 := hb{i_}.ne'")
    for i_, (f_, p_) in enumerate(facs):
        L.append(f"  have hf{i_} : 0 < {f_} := {p_}")
    pr_ = "hf0"
    for i_ in range(1, len(facs)):
        pr_ = f"(mul_pos {pr_} hf{i_})"
    den_l = " * ".join(f_ for f_, _ in facs)
    L += [f"  have hden : 0 < {den_l} := {pr_}",
          f"  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = {num_l} := ⟨_, rfl⟩",
          f"  have key : ({lean_expr}) * ({den_l}) = N := by",
          "    rw [hN]",
          ] + (["    " + kl for kl in key_lines] if key_lines else [
          f"    simp only [{', '.join(unfold)}]" if unfold else "    skip",
          "    field_simp",
          "    ring"]) + [
          "  have hP : 0 ≤ N := by",
          "    rw [hN]"]
    # substitutions
    L.append(f"    obtain ⟨z, rfl⟩ : ∃ z, {xname} = {lfr(X0)} + z := ⟨{xname} - {lfr(X0)}, by ring⟩")
    wn = [f"w{i}" for i in range(len(vnames))]
    for i, ((s_, lo, _), vn) in enumerate(zip(c.tvars, vnames)):
        L.append(f"    obtain ⟨{wn[i]}, rfl⟩ : ∃ w, {vn} = {lfr(Fr(lo))} + w := ⟨{vn} - {lfr(Fr(lo))}, by ring⟩")
    L.append(f"    have hz : 0 ≤ z := by linarith only [hx0]")
    L.append(f"    have hz1 : z ≤ {lfr(Zmax)} := by linarith only [hx1]")
    hiz = []
    for i, (s_, lo, (c0, c1)) in enumerate(c.tvars):
        c0 = Fr(c0); c1 = Fr(c1)
        h = f"({lfr(c0)} + {lfr(c1)} * z)"
        hiz.append(h)
        L.append(f"    have hw{i}0 : 0 ≤ {wn[i]} := by linarith only [hv{i}0]")
        L.append(f"    have hw{i}1 : {wn[i]} ≤ {h} := by linarith only [hv{i}1]")
    # termwise items
    items = []
    for (lev, T) in c.levels:
        for key, v in T:
            i = key[0]
            js = key[1:1 + lev + 1]
            j = js[lev]
            parts, prfs = [], []
            if i:
                parts.append(f"z ^ ({i} : ℕ)"); prfs.append(f"(pow_nonneg hz {i})")
            for k_ in range(lev):
                if js[k_]:
                    parts.append(f"{wn[k_]} ^ ({js[k_]} : ℕ)"); prfs.append(f"(pow_nonneg hw{k_}0 {js[k_]})")
            if v > 0:
                parts.append(f"{wn[lev]} ^ ({j} : ℕ)"); prfs.append(f"(pow_nonneg hw{lev}0 {j})")
            pt = " * ".join(parts) if parts else "1"
            pp = prfs[0] if prfs else "zero_le_one"
            for q in prfs[1:]:
                pp = f"(mul_nonneg {pp} {q})"
            if v > 0:
                items.append((f"{lfr(v)} * ({pt})", f"(mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(v)}) {pp})"))
            else:
                items.append((f"{lfr(-v)} * ({pt}) * ({hiz[lev]} ^ ({j} : ℕ) - {wn[lev]} ^ ({j} : ℕ))",
                              f"(mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ {lfr(-v)}) {pp}) (hh1_tw_sub {j} hw{lev}0 hw{lev}1))"))
    bl, Hl = bern_lines(c.H, Zmax)
    L += bl
    tt, tp = balanced_sum(items)
    L.append(f"    have hT := {tp}")
    L.append("    exact le_of_le_of_eq (add_nonneg hH hT) (by ring)")
    L.append("  exact (mul_nonneg_iff_of_pos_right hden).1 (by rw [key]; exact hP)")
    return "\n".join(L)
