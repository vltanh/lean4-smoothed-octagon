module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiSigns

/-!
# Case M2, forward successor: the forward ratio `χ` on the small-gap domain

If `1/3 ≤ t ≤ 19/50`, `0 ≤ j ≤ 1/30`, `k ≥ 1`, `q > 1`, the
exact incoming secant `v ≤ U(t)` and `N_k < 0`, then `χ = pq/W > 4/7`.

The shape monotonicity
lowers `k` to one, the substitutions `v ↦ V₂`, `log q ↦ L₊` lower `N₁` (negative coefficients),
and the resulting rational function is positive on the whole interval `1 ≤ q ≤ 4W/(7p)` by the
certificate `nsfCChi_pos`.

## Main API

* `nsf_chi_link`; `nsf_chi_core`: **`7pq > 4W`**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared unit-shape residual with `v ↦ V₂`, `log q ↦ L₊` is the certificate polynomial `nsfCChi`. -/
theorem nsf_chi_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    12 * (q + 1) * (1 + x) ^ 2 * nsrN t x 1 q (nsfV2 t x) (nsrLp q) =
      (nsfCChiD0_0 (1 - 2 * t) + nsfCChiD0_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCChiD0_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCChiD0_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCChiD0_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCChiD0_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCChiD0_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCChiD0_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ)) + (nsfCChiD1_0 (1 - 2 * t) + nsfCChiD1_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCChiD1_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCChiD1_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCChiD1_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCChiD1_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCChiD1_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCChiD1_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ)) * (q - 1) + (nsfCChiD2_0 (1 - 2 * t) + nsfCChiD2_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCChiD2_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCChiD2_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCChiD2_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCChiD2_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCChiD2_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCChiD2_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ)) * (q - 1) ^ (2 : ℕ) + (nsfCChiD3_0 (1 - 2 * t) + nsfCChiD3_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCChiD3_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCChiD3_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCChiD3_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCChiD3_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCChiD3_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCChiD3_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ)) * (q - 1) ^ (3 : ℕ) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hq1 : q + 1 ≠ 0 := by linarith
  unfold nsfCChiD0_0 nsfCChiD0_1 nsfCChiD0_2 nsfCChiD0_3 nsfCChiD0_4 nsfCChiD0_5 nsfCChiD0_6 nsfCChiD0_7 nsfCChiD1_0 nsfCChiD1_1 nsfCChiD1_2 nsfCChiD1_3 nsfCChiD1_4 nsfCChiD1_5 nsfCChiD1_6 nsfCChiD1_7 nsfCChiD2_0 nsfCChiD2_1 nsfCChiD2_2 nsfCChiD2_3 nsfCChiD2_4 nsfCChiD2_5 nsfCChiD2_6 nsfCChiD2_7 nsfCChiD3_0 nsfCChiD3_1 nsfCChiD3_2 nsfCChiD3_3 nsfCChiD3_4 nsfCChiD3_5 nsfCChiD3_6 nsfCChiD3_7
  unfold nsrN nsfV2 nsrLp
  field_simp
  ring

/-- **The forward ratio exceeds `4/7`**: `7pq > 4W` on the small-gap domain. -/
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
