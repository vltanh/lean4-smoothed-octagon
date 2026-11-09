from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/')
rhs = yform_sub('nsfCChi', "(1 - 2 * t)", "(2 * t + x - 1)", "(q - 1)")
lk = link2('nsfCChi', 'nsf_chi_link', '(t x q : ℝ)', '(hq : 0 < q) (hx : 0 < x)',
  '12 * (q + 1) * (1 + x) ^ 2 * nsrN t x 1 q (nsfV2 t x) (nsrLp q)', rhs, 'nsrN nsfV2 nsrLp',
  'The cleared unit-shape residual with `v ↦ V₂`, `log q ↦ L₊` is the certificate polynomial `nsfCChi`.',
  pre="  have hW : (1 + x) ≠ 0 := by linarith\n  have hq1 : q + 1 ≠ 0 := by linarith\n")
s = '''module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiSigns

/-!
# Case M2, forward successor: the forward ratio `χ` on the small-gap domain

If `1/3 ≤ t ≤ 19/50`, `0 ≤ j ≤ 1/30`, `k ≥ 1`, `q > 1`, the
exact incoming secant `v ≤ U(t)` and `N_k < 0`, then `χ = pq/W > 4/7`.

Route: instead of the concavity of `N₁` in `q` and its two endpoint signs, the shape monotonicity
lowers `k` to one, the substitutions `v ↦ V₂`, `log q ↦ L₊` lower `N₁` (negative coefficients),
and the resulting rational function is positive on the whole interval `1 ≤ q ≤ 4W/(7p)` by the
certificate `nsfCChi_pos`.

## Main API

* `nsf_chi_link`; `nsf_chi_core`: **`7pq > 4W`**.
-/

@[expose] public section

namespace SmoothedOctagon

''' + lk + '''
/-- **The forward ratio exceeds `4/7`**). -/
theorem nsf_chi_core {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 19 / 50) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hq : 1 < q) (hv : v = nsrSecN t x)
    (hvU : v ≤ 1 - t + t ^ 2) (hN : nsrN t x k q v (Real.log q) < 0) :
    4 * (1 + x) < 7 * (t + x) * q := by
  by_contra hc
  push Not at hc
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos hq0 hq.ne'
  have hmono := nsrN_mono_k (k := 1) (k' := k) (by linarith) (by linarith) hx hq.le hvU hL hk
  -- the substitutions `v ↦ V₂`, `log q ↦ L₊`
  have hV2 := nsf_secN_lt_V2 hx (by linarith : t < 1)
  rw [← hv] at hV2
  have hLp := nsr_log_lt_Lp hq
  have hNv := nsrNv_nonpos (t := t) (x := x) (k := 1) (q := q) (by linarith) hx.le hq.le (by linarith)
  have hNL := nsrNL_nonpos (t := t) (x := x) (k := 1) (q := q) (by linarith) hx.le hq0.le (by norm_num)
  have e1 := nsrN_sub_v t x 1 q v (nsfV2 t x) (Real.log q)
  have e2 := nsrN_sub_L t x 1 q (nsfV2 t x) (Real.log q) (nsrLp q)
  have m1 : 0 ≤ (v - nsfV2 t x) * nsrNv t x 1 q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNv
  have m2 : 0 ≤ (Real.log q - nsrLp q) * nsrNL t x 1 q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNL
  -- the certificate
  have hy1 : (q - 1) * (7 * (1 + (1 - 2 * t)) / 2 + 7 * (2 * t + x - 1)) ≤
      (1 + (1 - 2 * t)) / 2 - 3 * (2 * t + x - 1) := by nlinarith
  have hP := nsfCChi_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith) hj0 hj1
    (by linarith) (by linarith) (by linarith) hy1
  rw [← nsf_chi_link t x q hq0 hx] at hP
  have hpos : 0 < nsrN t x 1 q (nsfV2 t x) (nsrLp q) := pos_of_mul_pos_right hP (by positivity)
  linarith

end SmoothedOctagon
'''
open(LEAN + 'SmallGap/Chi.lean', 'w').write(s)
