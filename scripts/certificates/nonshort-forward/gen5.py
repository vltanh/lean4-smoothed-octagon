"""Nested Bernstein certificates through generic lemmas with abstract coefficients (v5).

A polynomial is given as  P = sum_i c_i(h, s) y^i  with  c_i = sum_l D_il(h) s^l,  s = j - jlo
(univariate Lean definitions D_il).  With multipliers M_i(h, s) (polynomials) the certificate proves
    0 < sum_i (c_i * M_i) * z^i     on  h0 <= h <= h1,  0 <= s <= g(h),  z in [zlo, zhi]
(numeric pieces), in three levels:
  * z-level: `nsfBernI*` (numeric interval, abstract coefficients);
  * s-level: `nsfBern0g*` (interval [0, g(h)], abstract coefficients E_l(h), Lean definitions);
  * h-level: univariate Bernstein certificates for every coefficient (subdivision), checked by
    `linear_combination`.
Typical multipliers: M_i = 1 (z = y), M_i = Y(h)^i (z = y/Y), M_i = (h - j)^i (1 + 2j)^(n - i)
(z = y(1 + 2j)/(h - j)).  Exponents are written `^ (n : ℕ)`.
"""
from fractions import Fraction as Fr
from math import comb, lcm
from plan3 import padd, pmul, pscale, bern1
from plan4 import coeffs_in, shift_scale
from gen4 import (lnum, P_, upoly, hvar, dict_to_list, beta0g_str, poly_str, lemma0g, wI, lin_str, ivname,
                  lemmaI, uni_split, lin_forms, Out, emit_leaf, uni_count, lpoly_mul, lpoly_add,
                  lpoly_scale, betas_j, structure)

def mult_dicts(Ms):
    return Ms

def plan_piece(D, Ms, g, h0, h1, zlo, zhi, eys=(0, 1, 2), ejs=(0, 1, 2, 3, 4, 5, 6)):
    """D[i][l] univariate lists; Ms[i]: dict in (h, s). Returns (n, W, plan_k, total)."""
    ny = len(D) - 1
    # c_i * M_i as dicts in (h, s)
    CM = []
    for i in range(ny+1):
        ci = {}
        for l, cl in enumerate(D[i]):
            for e, c in enumerate(cl):
                if c != 0: ci[(e, l)] = ci.get((e, l), Fr(0)) + c
        CM.append(pmul(ci, Ms[i]))
    for ey in eys:
        n = ny + ey
        if n > 20: break
        W = wI(n, zlo, zhi)
        plan_k = []; ok = True; tot = 0
        for k in range(n+1):
            bk = {}
            for i in range(ny+1):
                if W[k][i] != 0: bk = padd(bk, pscale(CM[i], W[k][i]))
            E = [dict_to_list(c) if c else [Fr(0)] for c in coeffs_in(bk, 1)] if bk else [[Fr(0)]]
            found = None
            for ej in ejs:
                md = len(E) - 1 + ej
                if md > 24: break
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

def plan_all(D, Ms, g, h0, h1, zlo, zhi, depth=0, maxdepth=4):
    r = plan_piece(D, Ms, g, h0, h1, zlo, zhi)
    if r is not None: return [(zlo, zhi, r)]
    if depth >= maxdepth: raise RuntimeError(f"plan failed on z in [{float(zlo)},{float(zhi)}]")
    mid = (zlo + zhi) / 2
    return plan_all(D, Ms, g, h0, h1, zlo, mid, depth+1, maxdepth) + \
        plan_all(D, Ms, g, h0, h1, mid, zhi, depth+1, maxdepth)

def emit_job(out, X, D, Mstrs, gstr, jlo, h0, h1, plan, needI, need0g, extra_unfold=""):
    """Emits D defs, E defs, leaves, levels, and `X_pos`. Mstrs[i]: Lean string of M_i (in h, j)."""
    ny = len(D) - 1; nl = max(len(D[i]) for i in range(ny+1)) - 1
    sstr = "j" if jlo == 0 else f"(j - {lnum(jlo)})"
    for i in range(ny+1):
        for l in range(len(D[i])):
            out.add(f"/-- Coefficient of `y^{i} s^{l}` in `{X}`. -/\nnoncomputable def {X}D{i}_{l} ({hvar(D[i][l])} : ℝ) : ℝ :=\n  {upoly(D[i][l], 'h')}\n")
    def cstr(i):
        if i > ny: return "0"
        base = "(" + poly_str([f"{X}D{i}_{l} h" for l in range(len(D[i]))], sstr) + ")"
        return base if Mstrs[i] == "1" else f"({base} * {Mstrs[i]})"
    unpadded = poly_str([cstr(i) for i in range(ny+1)], "z")
    for pi, (zlo, zhi, (n, W, plan_k, tot)) in enumerate(plan):
        needI.add((n, zlo, zhi))
        cs = [cstr(i) for i in range(n+1)]
        kthms = []
        for k in range(n+1):
            md, cnt, E, bs = plan_k[k]
            need0g.add(md)
            Es = []
            for l in range(md+1):
                if l >= len(E): Es.append("0"); continue
                out.add(f"noncomputable def {X}E{pi}_{k}_{l} ({hvar(E[l])} : ℝ) : ℝ := {upoly(E[l], 'h')}\n")
                Es.append(f"{X}E{pi}_{k}_{l} h")
            leafnames = []
            for m in range(md+1):
                stmt = beta0g_str(md, m, Es, f"({gstr})")
                used = [f"{X}E{pi}_{k}_{l}" for l in range(min(m, len(E)-1)+1)]
                nm = emit_leaf(out, f"{X}_z{pi}_k{k}_m{m}", bs[m], h0, h1, stmt, " ".join(used))
                leafnames.append(nm)
            zb = lin_str(W[k], cs)
            target = poly_str(Es, sstr)
            Dused = sorted({f"{X}D{i}_{l}" for i in range(min(ny, n)+1) for l in range(len(D[i])) if W[k][i] != 0})
            Eunf = " ".join([f"{X}E{pi}_{k}_{l}" for l in range(len(E))] + Dused) + (" " + extra_unfold if extra_unfold else "")
            out.add(f"""private theorem {X}_z{pi}_k{k} (h j : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) :
    0 < {zb} := by
  have e : {zb} = {target} := by unfold {Eunf}; ring
  rw [e]
  exact nsfBern0g{md} hs0 hs1 (by linarith) {' '.join(f'({nm} h hh0 hh1)' for nm in leafnames)}
""")
            kthms.append(f"{X}_z{pi}_k{k}")
        padded = poly_str(cs, "z")
        conv = "" if n == ny else f"""
  have e : {unpadded} = {padded} := by ring
  rw [e]"""
        if n == 0:
            needI.discard((n, zlo, zhi))
            out.add(f"""private theorem {X}_z{pi} (h j z : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (_hz0 : {lnum(zlo)} ≤ z) (_hz1 : z ≤ {lnum(zhi)}) :
    0 < {unpadded} :=
  {kthms[0]} h j hh0 hh1 hs0 hs1
""")
        else:
            out.add(f"""private theorem {X}_z{pi} (h j z : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hz0 : {lnum(zlo)} ≤ z) (hz1 : z ≤ {lnum(zhi)}) :
    0 < {unpadded} := by{conv}
  exact {ivname(n, zlo, zhi)} hz0 hz1 {' '.join(f'({k} h j hh0 hh1 hs0 hs1)' for k in kthms)}
""")
    body = []; cur = "hz0"
    for pi, (zlo, zhi, _) in enumerate(plan):
        line = f"{X}_z{pi} h j z hh0 hh1 hs0 hs1 {cur} {'hz1' if pi == len(plan)-1 else f'hc{pi}'}"
        if pi == len(plan) - 1:
            body.append(f"  exact {line}")
        else:
            body.append(f"  rcases le_total z {lnum(zhi)} with hc{pi} | hc{pi}")
            body.append(f"  · exact {line}")
            cur = f"hc{pi}"
    out.add(f"""/-- **Positivity of the certificate polynomial `{X}`**. -/
theorem {X}_pos (h j z : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hz0 : {lnum(plan[0][0])} ≤ z) (hz1 : z ≤ {lnum(plan[-1][1])}) :
    0 < {unpadded} := by
""" + "\n".join(body) + "\n")
    return unpadded, [cstr(i) for i in range(ny+1)]

def sym_M(i, Ys):
    return "1" if i == 0 else (Ys if i == 1 else f"{Ys} ^ ({i} : ℕ)")
def zpar_M(i, n):
    parts = []
    if i: parts.append("(h - j)" if i == 1 else f"(h - j) ^ ({i} : ℕ)")
    if n-i: parts.append("(1 + 2 * j)" if n-i == 1 else f"(1 + 2 * j) ^ ({n-i} : ℕ)")
    return " * ".join(parts) if parts else "1"
def cM(c, M):
    return c if M == "1" else f"({c} * {M})"

def zgen_M(i, n, Nm, Dn):
    parts = []
    if i: parts.append(f"({Nm})" if i == 1 else f"({Nm}) ^ ({i} : ℕ)")
    if n-i: parts.append(f"({Dn})" if n-i == 1 else f"({Dn}) ^ ({n-i} : ℕ)")
    return " * ".join(parts) if parts else "1"

def lemma_tr(kind, n, Ys="h"):
    if kind == 'zgen':
        cs = [f"c{i}" for i in range(n+1)]
        zf = zform_sub(poly_str([cM(cs[i], zgen_M(i, n, "a", "b")) for i in range(n+1)], "z"), "(y * (b) / (a))")
        return f"""theorem nsfZgenTr{n} {{a b y {' '.join(cs)} : ℝ}} (ha : a ≠ 0) :
    {zf} = (b) ^ ({n} : ℕ) * ({poly_str(cs, 'y')}) := by
  field_simp
"""
    cs = [f"c{i}" for i in range(n+1)]
    if kind == 'sym':
        zf = zform_sub(poly_str([cM(cs[i], sym_M(i, Ys)) for i in range(n+1)], "z"), f"(y / {Ys})")
        return f"""theorem nsfSymTr{n} {{h y {' '.join(cs)} : ℝ}} (hh : {Ys} ≠ 0) :
    {zf} = {poly_str(cs, 'y')} := by
  field_simp
"""
    zf = zform_sub(poly_str([cM(cs[i], zpar_M(i, n)) for i in range(n+1)], "z"), "(y * (1 + 2 * j) / (h - j))")
    return f"""theorem nsfZparTr{n} {{h j y {' '.join(cs)} : ℝ}} (hh : h - j ≠ 0) :
    {zf} = (1 + 2 * j) ^ ({n} : ℕ) * ({poly_str(cs, 'y')}) := by
  field_simp
"""

def emit_pos_y(out, X, D, kind, gstr, jlo, h0, h1, zform, cs_plain, ny, Yc=None):
    """theorem X_pos_y (h j y) (domain) (hy0 : 0 ≤ y) (hy1 : y-bound) : 0 < sum_i c_i y^i."""
    sstr = "j" if jlo == 0 else f"(j - {lnum(jlo)})"
    yform = poly_str(cs_plain, "y")
    if kind == 'zpar':
        zsub = "(y * (1 + 2 * j) / (h - j))"
        out.add(f"""/-- **The certificate in the event-factor variable** `y = q - 1 ∈ [0, (h - j)/(1 + 2j)]`. -/
theorem {X}_pos_y (h j y : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hjh : j < h) (hy0 : 0 ≤ y)
    (hy1 : y * (1 + 2 * j) ≤ h - j) :
    0 < {yform} := by
  have hhj : 0 < h - j := by linarith
  have hj2 : 0 < 1 + 2 * j := by linarith
  have hz := {X}_pos h j {zsub} hh0 hh1 hs0 hs1 (by positivity) (by rw [div_le_one hhj]; exact hy1)
  rw [nsfZparTr{ny} hhj.ne'] at hz
  exact pos_of_mul_pos_right hz (by positivity)
""")
    elif kind == 'zgen':
        Nm, Dn = Yc
        zsub = f"(y * ({Dn}) / ({Nm}))"
        out.add(f"""/-- **The certificate in the event-factor variable** `y = q - 1 ∈ [0, Nm/Dn]`. -/
theorem {X}_pos_y (h j y : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hN : 0 < {Nm}) (_hD : 0 < {Dn}) (hy0 : 0 ≤ y)
    (hy1 : y * ({Dn}) ≤ {Nm}) :
    0 < {yform} := by
  have hz := {X}_pos h j {zsub} hh0 hh1 hs0 hs1 (by positivity) (by rw [div_le_one hN]; exact hy1)
  rw [nsfZgenTr{ny} hN.ne'] at hz
  exact pos_of_mul_pos_right hz (by positivity)
""")
    elif kind == 'sym':
        Ys = "h" if Yc == 1 else f"({lnum(Yc)} * h)"
        zsub = f"(y / {Ys})"
        out.add(f"""/-- **The certificate in the event-factor variable** `y = q - 1 ∈ [0, {Ys}]`. -/
theorem {X}_pos_y (h j y : ℝ) (hh0 : {lnum(h0)} ≤ h) (hh1 : h ≤ {lnum(h1)})
    (hs0 : 0 ≤ {sstr}) (hs1 : {sstr} ≤ {gstr}) (hy0 : 0 ≤ y) (hy1 : y ≤ {Ys}) :
    0 < {yform} := by
  have hY : 0 < {Ys} := by linarith
  have hz := {X}_pos h j {zsub} hh0 hh1 hs0 hs1 (by positivity) (by rw [div_le_one hY]; exact hy1)
  rwa [nsfSymTr{ny} hY.ne'] at hz
""")
    return yform

def zform_sub(zform, zsub):
    import re
    return re.sub(r'\bz\b', zsub, zform)
