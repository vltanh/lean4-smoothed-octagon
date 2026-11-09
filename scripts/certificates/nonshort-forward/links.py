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
  unfold nsfComb nsfTP nsfKt nsfHt nsfE0 nsrN {unfold_extra}
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
    """kind 'LR': v = nsfVhat, F = 0; kind 'LG': v = nsfVG, F = nsrFl."""
    rhs = yform_tx(X)
    D = " ".join(Dnames(X))
    pre = "48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15)"
    if kind == 'LR':
        vexpr, Fexpr = "(nsfVhat t x q)", "0"
        hv = f"""  have hv : nsfVhat t x q = ({NUMS['Nvh']}) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2 * (q + 1)) := by
    unfold nsfVhat nsfVG nsrFl; field_simp; ring
"""
        rws = "rw [nsf_comb_dec, hv]\n  unfold nsrLp"
        clear = "nsf_clear_LR"
    else:
        vexpr, Fexpr = "(nsfVG t x)", "(nsrFl t x q)"
        hv = f"""  have hv : nsfVG t x = ({NUMS['NVG']}) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2) := by
    unfold nsfVG; field_simp; ring
  have hF : nsrFl t x q = ({NUMS['NFl']}) / (6 * (1 + x) ^ 2 * (q + 1)) := by
    unfold nsrFl; field_simp; ring
"""
        rws = "rw [nsf_comb_dec, hv, hF]\n  unfold nsrLp"
        clear = "nsf_clear_LG"
    extra = "nsfAlA nsfMA " if 'nsfAlA' in al else ""
    return f"""/-- {doc} -/
theorem {name} (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    {pre} * nsfComb {al} {M} t x {K} q {vexpr} (nsrLp q) {Fexpr} =
      {rhs} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
{hv}  {rws}
  apply mul_left_cancel₀ (mul_ne_zero hW hq.ne')
  rw [{clear} hW hq.ne' hq1 hR]
  unfold {D}
  unfold {extra}nsfComb nsfCv nsfCL nsfTPv nsfTP nsfKt nsfHt nsfE0 nsrN nsrNv nsrNL
  ring
"""
