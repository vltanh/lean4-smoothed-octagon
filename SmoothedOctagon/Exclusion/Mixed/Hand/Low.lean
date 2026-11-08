module

public import SmoothedOctagon.Exclusion.Mixed.Hand.ReverseCore
public import SmoothedOctagon.Exclusion.Mixed.Hand.CertLow

/-!
# Case M2 by hand: the low-scale region `k ≥ 17t²`

`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` with `MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION`. On the
necessary domain with `k ≥ 17t²` (that is, `a ≤ 1/2`), `N_k > 0`:

* `t < T(x) = (-2x³ - x² + 10x + 12)/(3(x + 2)³)` from `v ≥ g_c(d)` and `v < v̄` (identity (2));
* `t < 7/20` (domain reduction §1);
* if `k ≥ 2t + x`, the scalar reverse exclusion `nh_reverse_core` applies (its other hypotheses
  hold here); otherwise `k < 2t + x` (the common order of `MIXED_NONSHORT_REVERSE_HAND_EXCLUSION`
  §5) and `k` is lowered to the unit face `k = 1` (`t ≤ 1/4`) or to the high-ratio face
  `k = 2t + 1/2` (`t ≥ 1/4`), where the quartic `Q` of (7) is positive by the six signs (9)
  (`nh_quartic_pos`, certificates `Hand/CertLow`).

## Main API

* `nh_quartic_pos`: the univariate reduction of §3.
* `nh_low_unit`, `nh_low_kh`: the two faces.
* `nh_vbar_sub_g`, `nh_low_t`: `t < T(x)` and `t < 7/20`.
* `nh_low_core`: **the scalar low-scale exclusion**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The univariate reduction** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` §3): the six signs (9)
force the quartic to be positive for every `y ≥ 0`. -/
theorem nh_quartic_pos {P0 P1 P2 P3 P4 y : ℝ} (hy : 0 ≤ y) (h0 : 0 < P0) (h1 : 0 < P1 + 2 * P0)
    (h2 : 0 < P2 + 48 * P0) (h3 : 0 < P3 + 4 * P2) (h4 : 0 < P3 - P0) (h5 : 0 < P4 - P0) :
    0 < P0 + P1 * y + P2 * y ^ 2 + P3 * y ^ 3 + P4 * y ^ 4 := by
  have f : 1 / 25 ≤ 1 - 2 * y - 1 / 4 * y ^ 2 + y ^ 3 + y ^ 4 := by
    nlinarith [mul_nonneg hy (sq_nonneg (y - 2 / 3)), mul_nonneg (sq_nonneg y) (sq_nonneg (y - 2 / 3)),
      sq_nonneg (y - 2 / 3 + 1 / 20), sq_nonneg (y - 2 / 3)]
  have g : 1 / 7 ≤ 1 - 2 * y - 48 * y ^ 2 + 192 * y ^ 3 := by
    nlinarith [mul_nonneg hy (sq_nonneg (y - 1 / 6)), sq_nonneg (y - 1 / 6 - 1 / 16)]
  have hA : 0 ≤ (P1 + 2 * P0) * y := mul_nonneg h1.le hy
  have hE : 0 ≤ (P4 - P0) * y ^ 4 := mul_nonneg h5.le (by positivity)
  rcases le_or_gt 0 P2 with hB | hB
  · have hB' : 0 ≤ P2 * y ^ 2 := mul_nonneg hB (by positivity)
    have hC : 0 ≤ (P3 - P0) * y ^ 3 := mul_nonneg h4.le (by positivity)
    have w : 0 ≤ P0 * ((1 - 2 * y - 1 / 4 * y ^ 2 + y ^ 3 + y ^ 4) + 1 / 4 * y ^ 2 - 1 / 25) :=
      mul_nonneg h0.le (by nlinarith [sq_nonneg y])
    linear_combination hA + hB' + hC + hE + w + (1 / 25 : ℝ) * h0
  rcases le_or_gt (-(1 / 4) * P0) P2 with hB2 | hB2
  · have hB' : 0 ≤ (P2 + 1 / 4 * P0) * y ^ 2 := mul_nonneg (by linarith) (by positivity)
    have hC : 0 ≤ (P3 - P0) * y ^ 3 := mul_nonneg h4.le (by positivity)
    have w : 0 ≤ P0 * ((1 - 2 * y - 1 / 4 * y ^ 2 + y ^ 3 + y ^ 4) - 1 / 25) :=
      mul_nonneg h0.le (by linarith)
    linear_combination hA + hB' + hC + hE + w + (1 / 25 : ℝ) * h0
  · have hC : 0 ≤ (P3 + 4 * P2) * y ^ 3 := mul_nonneg h3.le (by positivity)
    have w1 : 0 ≤ (48 * P0 + P2) * ((1 - 2 * y - 1 / 4 * y ^ 2 + y ^ 3 + y ^ 4) - 1 / 25) :=
      mul_nonneg (by linarith) (by linarith)
    have w2 : 0 ≤ (-P2 - 1 / 4 * P0) * ((1 - 2 * y - 48 * y ^ 2 + 192 * y ^ 3) + y ^ 4 - 1 / 25) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (y ^ 2)])
    linear_combination hA + hC + hE + (4 / 191 : ℝ) * w1 + (4 / 191 : ℝ) * w2 + (1 / 25 : ℝ) * h0

/-- The cleared low-scale quartic on the unit face. -/
theorem nhLU_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nhN t x 1 q (nhVbar t x) (nhLp q) - (-nhNv t x 1 q) * (nhVbar t x - nhFl t x q)) =
      nhLU0 t x + nhLU1 t x * (q - 1) + nhLU2 t x * (q - 1) ^ 2 + nhLU3 t x * (q - 1) ^ 3
        + nhLU4 t x * (q - 1) ^ 4 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nhN nhNv nhVbar nhLp nhFl nhLU0 nhLU1 nhLU2 nhLU3 nhLU4
  field_simp
  ring

/-- The cleared low-scale quartic on the high-ratio face. -/
theorem nhLH_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nhN t x (2 * t + 1 / 2) q (nhVbar t x) (nhLp q) -
        (-nhNv t x (2 * t + 1 / 2) q) * (nhVbar t x - nhFl t x q)) =
      nhLH0 t x + nhLH1 t x * (q - 1) + nhLH2 t x * (q - 1) ^ 2 + nhLH3 t x * (q - 1) ^ 3
        + nhLH4 t x * (q - 1) ^ 4 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nhN nhNv nhVbar nhLp nhFl nhLH0 nhLH1 nhLH2 nhLH3 nhLH4
  field_simp
  ring

/-- The common relaxation step on a low-scale face: positivity of the cleared quartic gives
`N > 0`. -/
theorem nh_low_relax {t x k q v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : 2 * t ≤ k)
    (hq : 1 < q) (hv : v = nhSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v)
    (hP : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nhN t x k q (nhVbar t x) (nhLp q) - (-nhNv t x k q) * (nhVbar t x - nhFl t x q))) :
    0 < nhN t x k q v (Real.log q) := by
  have hpos : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 := by
    have : 0 < q + 1 := by linarith
    positivity
  have hNv := nhNv_nonpos ht.le hx.le hq.le hk
  refine nh_N_pos_of_relax (vb := nhVbar t x) (Lb := nhLp q) (Fl := nhFl t x q)
    (m := -nhNv t x k q) ?_ (nh_log_lt_Lp hq).le hNv
    (nhNL_nonpos ht.le hx.le (by linarith) (by linarith))
    ((nh_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith)
    (pos_of_mul_pos_right hP hpos.le)
  rw [hv]
  exact (nh_secN_lt_vbar hx ht1).le

/-- **The unit low-scale face** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` (3)): for
`0 < t ≤ 1/4`, `1/2 < x ≤ 7/3`, `x ≥ 1 - 2t`, `t ≤ T(x)`, `N(1) > 0`. -/
theorem nh_low_unit {t x q v : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 4) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12)
    (hq : 1 < q) (hv : v = nhSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nhN t x 1 q v (Real.log q) := by
  have hx : 0 < x := by linarith
  have j0 := nhLUJ0_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j1 := nhLUJ1_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j2 := nhLUJ2_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j3 := nhLUJ3_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j4 := nhLUJ4_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j5 := nhLUJ5_dom t x hx0 hx1 ht.le ht1 hxt hT
  have e0 : nhLUJ0 t x = nhLU0 t x := by unfold nhLUJ0 nhLU0; ring
  have e1 : nhLUJ1 t x = nhLU1 t x + 2 * nhLU0 t x := by unfold nhLUJ1 nhLU0 nhLU1; ring
  have e2 : nhLUJ2 t x = nhLU2 t x + 48 * nhLU0 t x := by unfold nhLUJ2 nhLU0 nhLU2; ring
  have e3 : nhLUJ3 t x = nhLU3 t x + 4 * nhLU2 t x := by unfold nhLUJ3 nhLU2 nhLU3; ring
  have e4 : nhLUJ4 t x = nhLU3 t x - nhLU0 t x := by unfold nhLUJ4 nhLU0 nhLU3; ring
  have e5 : nhLUJ5 t x = nhLU4 t x - nhLU0 t x := by unfold nhLUJ5 nhLU0 nhLU4; ring
  rw [e0] at j0; rw [e1] at j1; rw [e2] at j2; rw [e3] at j3; rw [e4] at j4; rw [e5] at j5
  have hQ := nh_quartic_pos (y := q - 1) (by linarith) j0 j1 j2 j3 j4 j5
  refine nh_low_relax ht (by linarith) hx (by linarith) hq hv hF ?_
  rw [nhLU_P_eq hx (by linarith)]
  exact hQ

/-- **The high-ratio low-scale face** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` (4)): for
`1/4 ≤ t ≤ 7/20`, `1/2 ≤ x ≤ 1`, `N(2t + 1/2) > 0`. -/
theorem nh_low_kh {t x q v : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x)
    (hx1 : x ≤ 1) (hq : 1 < q) (hv : v = nhSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nhN t x (2 * t + 1 / 2) q v (Real.log q) := by
  have hx : 0 < x := by linarith
  have j0 := nhLHJ0_dom t x ht0 ht1 hx0 hx1
  have j1 := nhLHJ1_dom t x ht0 ht1 hx0 hx1
  have j2 := nhLHJ2_dom t x ht0 ht1 hx0 hx1
  have j3 := nhLHJ3_dom t x ht0 ht1 hx0 hx1
  have j4 := nhLHJ4_dom t x ht0 ht1 hx0 hx1
  have j5 := nhLHJ5_dom t x ht0 ht1 hx0 hx1
  have e0 : nhLHJ0 t x = nhLH0 t x := by unfold nhLHJ0 nhLH0; ring
  have e1 : nhLHJ1 t x = nhLH1 t x + 2 * nhLH0 t x := by unfold nhLHJ1 nhLH0 nhLH1; ring
  have e2 : nhLHJ2 t x = nhLH2 t x + 48 * nhLH0 t x := by unfold nhLHJ2 nhLH0 nhLH2; ring
  have e3 : nhLHJ3 t x = nhLH3 t x + 4 * nhLH2 t x := by unfold nhLHJ3 nhLH2 nhLH3; ring
  have e4 : nhLHJ4 t x = nhLH3 t x - nhLH0 t x := by unfold nhLHJ4 nhLH0 nhLH3; ring
  have e5 : nhLHJ5 t x = nhLH4 t x - nhLH0 t x := by unfold nhLHJ5 nhLH0 nhLH4; ring
  rw [e0] at j0; rw [e1] at j1; rw [e2] at j2; rw [e3] at j3; rw [e4] at j4; rw [e5] at j5
  have hQ := nh_quartic_pos (y := q - 1) (by linarith) j0 j1 j2 j3 j4 j5
  refine nh_low_relax (by linarith) (by linarith) hx (by linarith) hq hv hF ?_
  rw [nhLH_P_eq hx (by linarith)]
  exact hQ

/-- `v̄ - g = (1 - t)x(N(x) - 3X³t)/(3W²X³)` (`MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION` (4)). -/
theorem nh_vbar_sub_g {t x : ℝ} (hx : 0 < x) :
    (nhVbar t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) * (3 * (1 + x) ^ 2 * (x + 2) ^ 3) =
      (1 - t) * x * (-2 * x ^ 3 - x ^ 2 + 10 * x + 12 - 3 * (x + 2) ^ 3 * t) := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  unfold nhVbar
  field_simp
  ring

/-- **The secant ceiling**: `v ≥ g_c(d)` and `v < v̄` give `t < T(x)`, i.e.
`3(x + 2)³t < -2x³ - x² + 10x + 12`. -/
theorem nh_t_lt_T {t x v : ℝ} (ht1 : t < 1) (hx : 0 < x) (hv : v = nhSecN t x)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) :
    3 * (x + 2) ^ 3 * t < -2 * x ^ 3 - x ^ 2 + 10 * x + 12 := by
  have hvb := nh_secN_lt_vbar hx ht1
  rw [← hv] at hvb
  have e := nh_vbar_sub_g (t := t) hx
  have h1 : 0 < (nhVbar t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) * (3 * (1 + x) ^ 2 * (x + 2) ^ 3) :=
    mul_pos (by linarith) (by positivity)
  rw [e] at h1
  have h2 : 0 < (1 - t) * x := mul_pos (by linarith) hx
  have := pos_of_mul_pos_right h1 h2.le
  linarith

/-- **The scalar low-scale exclusion** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`): on the
necessary domain with `k ≥ 17t²`, `N_k > 0`. -/
theorem nh_low_core {t x k q v : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) (hx : 0 < x) (hk1 : 1 ≤ k)
    (hk17 : 17 * t ^ 2 ≤ k) (hgap : k < 2 * t + 2 * x + x ^ 2) (hdur : x < 7 / 3 - 10 / 3 * t)
    (hq : 1 < q) (hqW : q < (1 + x) / (t + x)) (hv : v = nhSecN t x) (hvU : v ≤ 1 - t + t ^ 2)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nhN t x k q v (Real.log q) := by
  have hT := nh_t_lt_T (by linarith) hx hv hg
  -- `t < 7/20`
  have ht7 : t < 7 / 20 := by
    by_contra h
    push Not at h
    have hx8 : 8 / 15 < x := by nlinarith
    have := nh_T_anti (xa := 8 / 15) (by norm_num) hx8.le ht.le hT.le
    norm_num at this
    linarith
  -- if `k ≥ 2t + x`, the scalar reverse exclusion applies
  by_cases hko : 2 * t + x ≤ k
  · exact nh_reverse_core ht (by linarith) hx hk1 hko (by nlinarith) hgap hdur hq hqW hv hvU hF
  push Not at hko
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos (by linarith) hq.ne'
  have mono : ∀ k', k' ≤ k → nhN t x k' q v (Real.log q) ≤ nhN t x k q v (Real.log q) :=
    fun k' hk' => nhN_mono_k ht (by linarith) hx hq.le hvU hL hk'
  rcases le_total t (1 / 4) with h4 | h4
  · exact lt_of_lt_of_le (nh_low_unit ht h4 (by linarith) (by linarith) (by linarith) hT.le hq hv hF)
      (mono 1 hk1)
  · have hkh : 2 * t + 1 / 2 ≤ k := by nlinarith
    have hx1 : x ≤ 1 := by
      by_contra h
      push Not at h
      have := nh_T_anti (xa := 1) (by norm_num) h.le ht.le hT.le
      norm_num at this
      linarith
    exact lt_of_lt_of_le (nh_low_kh h4 ht7.le (by nlinarith) hx1 hq hv hF) (mono _ hkh)

end SmoothedOctagon
