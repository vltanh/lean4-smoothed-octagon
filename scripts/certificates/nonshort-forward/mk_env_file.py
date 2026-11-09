"""Regenerate only the remaining Casimir-excess identity in the analytic envelope proof."""
from pathlib import Path
from links import *

import json as _json
N2 = _json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'nums2.json')))
_rhsP = yform_sub('nsfCPn', "(2 / 5 - t)", "(2 * t + x - 1)", "(k - 1)", var='z')
_DP = " ".join(Dnames('nsfCPn'))
lP = f"""/-- The cleared Casimir excess at `v = V` is the certificate polynomial `nsfCPn`. -/
theorem nsf_Pn_link (t x k : ℝ) (ht : 0 < t) (hx : 0 < x) :
    3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      {_rhsP} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ht' : t ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hNV : (1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x = {N2['NV']} := by
    unfold nsfVq; field_simp; ring
  have hNK : t * nsfK0 t x k = {N2['NK']} := by
    unfold nsfK0; field_simp; ring
  have hNP : t * nsfPv t x k = {N2['NP']} := by
    unfold nsfPv; field_simp; ring
  have hND0 : t * (t + x) * (1 + x) ^ 2 * nsfD0 t x k = {N2['ND0']} := by
    unfold nsfD0 nsfK0 nsfg; field_simp; ring
  have hNDp : t * (t + x) * (1 + x) * nsfDp t x k = {N2['NDp']} := by
    unfold nsfDp nsfPv; field_simp; ring
  have e : 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      3125 * (4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x) * (t * nsfK0 t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 3 * (x ^ 2 + 6 * x + 6))
        + 4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x) ^ 2 * (t * nsfPv t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 2)
        - ((x ^ 2 + 6 * x + 6) * (t * (t + x) * (1 + x) ^ 2 * nsfD0 t x k)
          + (t * (t + x) * (1 + x) * nsfDp t x k) * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x)) ^ 2)
      - 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) := by
    unfold nsfNen; ring
  rw [e, hNV, hNK, hNP, hND0, hNDp]
  unfold {_DP}
  ring
"""
p = Path(__file__).resolve().parents[3] / 'SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/SmallGap/EnvelopeCasimir.lean'
s = p.read_text()
start = s.index('/-- The cleared Casimir excess')
end = s.index('/-- **Concavity in the incoming norm**', start)
p.write_text(s[:start] + lP + '\n' + s[end:])
