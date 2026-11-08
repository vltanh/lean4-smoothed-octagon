"""Shift lemma: Q(v1, a, v3) = P(v1, a - lo(v3), v3), both in nested form (v1 | a | v3)."""
import sys
from fractions import Fraction as Fr
from leangen import nested_coeffs, upoly, pw, polyy, lnum

def nz_names(X, d):
    N1 = len(d) - 1; N2 = len(d[0]) - 1
    return [[(f"{X}_d{i}_{j}" if any(c != 0 for c in d[i][j]) else None) for j in range(N2 + 1)] for i in range(N1 + 1)]

def emit_defs(X, P, vars3, doc):
    """Coefficient defs and nested def of X (no certificate)."""
    v1, v2, v3 = vars3
    d = nested_coeffs(P)
    names = nz_names(X, d)
    out = []
    for i in range(len(d)):
        for j in range(len(d[0])):
            if names[i][j]:
                out.append(f"/-- Coefficient of `{v1}^{i} {v2}^{j}` in `{X}`. -/\nnoncomputable def {names[i][j]} ({v3} : ℝ) : ℝ :=\n  {upoly(d[i][j], v3)}\n")
    Cs = [Cstr(names, i, v2, v3) for i in range(len(d))]
    out.append(f"""/-- {doc} (nested form). -/
noncomputable def {X} ({v1} {v2} {v3} : ℝ) : ℝ :=
  {polyy(Cs, v1)}
""")
    return "\n".join(out)

def Cstr(names, i, v2, v3, sub=None):
    ts = []
    for j, nm in enumerate(names[i]):
        if not nm: continue
        base = f"{nm} {v3}"
        y = v2 if sub is None else sub
        ts.append(base if j == 0 else f"{base} * {pw(y, j)}")
    return "(" + (" + ".join(ts) if ts else "0") + ")"

def emit_shift(XQ, Q, XP, P, vars3, lostr):
    """theorem XQ_shift : XQ v1 a v3 = XP v1 (a - lo) v3."""
    v1, v2, v3 = vars3
    dQ = nested_coeffs(Q); dP = nested_coeffs(P)
    nQ = nz_names(XQ, dQ); nP = nz_names(XP, dP)
    N1 = max(len(dQ), len(dP)) - 1
    out = []
    hs = []
    sub = f"({v2} - {lostr})"
    for i in range(N1 + 1):
        lq = Cstr(nQ, i, v2, v3) if i < len(dQ) else "0"
        rp = Cstr(nP, i, v2, v3, sub=sub) if i < len(dP) else "0"
        unf = " ".join([n for n in (nQ[i] if i < len(dQ) else []) if n] + [n for n in (nP[i] if i < len(dP) else []) if n])
        out.append(f"""private theorem {XQ}_sh{i} ({v2} {v3} : ℝ) :
    {lq} = {rp} := by
  unfold {unf}
  ring
""")
        hs.append(f"{XQ}_sh{i} {v2} {v3}")
    comb = " + ".join([f"({hs[0]})"] + [f"({h}) * {pw(v1, i)}" for i, h in enumerate(hs) if i >= 1])
    out.append(f"""/-- The shift `{v2} ↦ {v2} - ({lostr})` from `{XQ}` to `{XP}`. -/
theorem {XQ}_shift ({v1} {v2} {v3} : ℝ) : {XQ} {v1} {v2} {v3} = {XP} {v1} ({v2} - {lostr}) {v3} := by
  unfold {XQ} {XP}
  linear_combination {comb}
""")
    return "\n".join(out)
