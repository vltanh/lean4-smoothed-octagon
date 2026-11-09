from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/FwdHand/')
rhs = yform_sub('fhCChi', "(1 - 2 * t)", "(2 * t + x - 1)", "(q - 1)")
lk = link2('fhCChi', 'fh_chi_link', '(t x q : ℝ)', '(hq : 0 < q) (hx : 0 < x)',
  '12 * (q + 1) * (1 + x) ^ 2 * nhN t x 1 q (fhV2 t x) (nhLp q)', rhs, 'nhN fhV2 nhLp',
  'The cleared unit-shape residual with `v ↦ V₂`, `log q ↦ L₊` is the certificate polynomial `fhCChi`.',
  pre="  have hW : (1 + x) ≠ 0 := by linarith\n  have hq1 : q + 1 ≠ 0 := by linarith\n")
s = '''module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Secant
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertChi

/-!
# Case M2, forward successor by hand: the forward ratio `χ` on the small-gap domain

`MIXED_NONSHORT_SMALL_GAP_CHI_BOUND`: if `1/3 ≤ t ≤ 19/50`, `0 ≤ j ≤ 1/30`, `k ≥ 1`, `q > 1`, the
exact incoming secant `v ≤ U(t)` and `N_k < 0`, then `χ = pq/W > 4/7`.

Route: instead of the concavity of `N₁` in `q` and its two endpoint signs, the shape monotonicity
lowers `k` to one, the substitutions `v ↦ V₂`, `log q ↦ L₊` lower `N₁` (negative coefficients),
and the resulting rational function is positive on the whole interval `1 ≤ q ≤ 4W/(7p)` by the
generated certificate `CertChi`.

## Main API

* `fh_chi_link`; `fh_chi_core`: **`7pq > 4W`**.
-/

@[expose] public section

namespace SmoothedOctagon

''' + lk + '''
/-- **The forward ratio exceeds `4/7`** (`MIXED_NONSHORT_SMALL_GAP_CHI_BOUND` (2)). -/
theorem fh_chi_core {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 19 / 50) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hq : 1 < q) (hv : v = nhSecN t x)
    (hvU : v ≤ 1 - t + t ^ 2) (hN : nhN t x k q v (Real.log q) < 0) :
    4 * (1 + x) < 7 * (t + x) * q := by
  by_contra hc
  push Not at hc
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos hq0 hq.ne'
  have hmono := nhN_mono_k (k := 1) (k' := k) (by linarith) (by linarith) hx hq.le hvU hL hk
  -- the substitutions `v ↦ V₂`, `log q ↦ L₊`
  have hV2 := fh_secN_lt_V2 hx (by linarith : t < 1)
  rw [← hv] at hV2
  have hLp := nh_log_lt_Lp hq
  have hNv := nhNv_nonpos (t := t) (x := x) (k := 1) (q := q) (by linarith) hx.le hq.le (by linarith)
  have hNL := nhNL_nonpos (t := t) (x := x) (k := 1) (q := q) (by linarith) hx.le hq0.le (by norm_num)
  have e1 := nhN_sub_v t x 1 q v (fhV2 t x) (Real.log q)
  have e2 := nhN_sub_L t x 1 q (fhV2 t x) (Real.log q) (nhLp q)
  have m1 : 0 ≤ (v - fhV2 t x) * nhNv t x 1 q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNv
  have m2 : 0 ≤ (Real.log q - nhLp q) * nhNL t x 1 q := mul_nonneg_of_nonpos_of_nonpos (by linarith) hNL
  -- the certificate
  have hy1 : (q - 1) * (7 * (1 + (1 - 2 * t)) / 2 + 7 * (2 * t + x - 1)) ≤
      (1 + (1 - 2 * t)) / 2 - 3 * (2 * t + x - 1) := by nlinarith
  have hP := fhCChi_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith) hj0 hj1
    (by linarith) (by linarith) (by linarith) hy1
  rw [← fh_chi_link t x q hq0 hx] at hP
  have hpos : 0 < nhN t x 1 q (fhV2 t x) (nhLp q) := pos_of_mul_pos_right hP (by positivity)
  linarith

end SmoothedOctagon
'''
open(LEAN + 'Chi.lean', 'w').write(s)
