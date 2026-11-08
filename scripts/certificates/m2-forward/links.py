import pickle, re
def subst(yform, hs, js, ys):
    s = re.sub(r'(?<![\w.])h(?![\w.])', hs, yform)
    s = re.sub(r'(?<![\w.])j(?![\w.])', js, s)
    s = re.sub(r'(?<![\w.])y(?![\w.])', ys, s)
    return s
def Dnames(X):
    G = pickle.load(open(f'{X}.gen.pkl','rb'))
    D = G['D']
    return [f"{X}D{i}_{l}" for i in range(len(D)) for l in range(len(D[i]))]
def yform_tx(X):
    G = pickle.load(open(f'{X}.gen.pkl','rb'))
    return subst(G['final'], "(1 - 2 * t)", "(2 * t + x - 1)", "(q - 1)")
def link(X, name, lhs, unfold_extra, doc):
    rhs = yform_tx(X)
    D = " ".join(Dnames(X))
    return f"""/-- {doc} -/
theorem {name} (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    {lhs} =
      {rhs} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
  unfold {D}
  unfold fhComb fhTP fhKt fhHt fhE0 nhN {unfold_extra}
  field_simp
  ring
"""

def yform_sub(X, hs, js, ys, var='y'):
    G = pickle.load(open(f'{X}.gen.pkl','rb'))
    s = G['final']
    s = re.sub(r'(?<![\w.])h(?![\w.])', hs, s)
    s = re.sub(r'(?<![\w.])j(?![\w.])', js, s)
    s = re.sub(rf'(?<![\w.]){var}(?![\w.])', ys, s)
    return s
def link2(X, name, args, hyps, lhs, rhs, unfolds, doc, pre=""):
    D = " ".join(Dnames(X))
    return f"""/-- {doc} -/
theorem {name} {args} {hyps} :
    {lhs} =
      {rhs} := by
{pre}  unfold {D}
  unfold {unfolds}
  field_simp
  ring
"""

import json
NUMS = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'nums.json')))
def link3(X, name, kind, al, M, K, doc):
    """kind 'LR': v = fhVhat, F = 0; kind 'LG': v = fhVG, F = nhFl."""
    rhs = yform_tx(X)
    D = " ".join(Dnames(X))
    pre = "48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15)"
    if kind == 'LR':
        vexpr, Fexpr = "(fhVhat t x q)", "0"
        hv = f"""  have hv : fhVhat t x q = ({NUMS['Nvh']}) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2 * (q + 1)) := by
    unfold fhVhat fhVG nhFl; field_simp; ring
"""
        rws = "rw [fh_comb_dec, hv]\n  unfold nhLp"
        clear = "fh_clear_LR"
    else:
        vexpr, Fexpr = "(fhVG t x)", "(nhFl t x q)"
        hv = f"""  have hv : fhVG t x = ({NUMS['NVG']}) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2) := by
    unfold fhVG; field_simp; ring
  have hF : nhFl t x q = ({NUMS['NFl']}) / (6 * (1 + x) ^ 2 * (q + 1)) := by
    unfold nhFl; field_simp; ring
"""
        rws = "rw [fh_comb_dec, hv, hF]\n  unfold nhLp"
        clear = "fh_clear_LG"
    extra = "fhAlA fhMA " if 'fhAlA' in al else ""
    return f"""/-- {doc} -/
theorem {name} (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    {pre} * fhComb {al} {M} t x {K} q {vexpr} (nhLp q) {Fexpr} =
      {rhs} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
{hv}  {rws}
  apply mul_left_cancel₀ (mul_ne_zero hW hq.ne')
  rw [{clear} hW hq.ne' hq1 hR]
  unfold {D}
  unfold {extra}fhComb fhCv fhCL fhTPv fhTP fhKt fhHt fhE0 nhN nhNv nhNL
  ring
"""
