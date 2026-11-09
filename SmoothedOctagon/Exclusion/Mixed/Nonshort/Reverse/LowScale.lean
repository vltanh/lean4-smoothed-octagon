module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.Core
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.LowScale.Signs

/-!
# Case M2, reverse successor: the low-scale region `k ≥ 17t²`

On the necessary domain with `k ≥ 17t²` (that is, `a ≤ 1/2`), `N_k > 0`:

* `t < T(x) = (-2x³ - x² + 10x + 12)/(3(x + 2)³)` from `v ≥ g_c(d)` and `v < v̄` (the identity
  `nsr_vbar_sub_g`);
* `t < 7/20`: for `t ≥ 7/20`, `17t² ≤ k < 2t + 2x + x²` gives `x > 8/15`, and `T` is decreasing
  with `T(8/15) < 7/20`;
* if `k ≥ 2t + x`, the scalar reverse exclusion `nsr_reverse_core` applies (its other hypotheses
  hold here); otherwise `k < 2t + x`, and by shape monotonicity `k` is lowered to the unit face
  `k = 1` (`t ≤ 1/4`) or to the high-ratio face `k = 2t + 1/2` (`t ≥ 1/4`), where the cleared
  quartic `Q = P₀ + P₁y + ⋯ + P₄y⁴` is positive by six coefficient signs (`nsr_quartic_pos`,
  certificates `Nonshort/Reverse/LowScale/Signs`).

## Main API

* `nsr_quartic_pos`: the univariate reduction (six coefficient signs give a positive quartic).
* `nsr_low_unit`, `nsr_low_kh`: the two faces.
* `nsr_vbar_sub_g`, `nsr_low_t`: `t < T(x)` and `t < 7/20`.
* `nsr_low_core`: **the scalar low-scale exclusion**.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The univariate reduction**: the six signs `P₀ > 0`, `P₁ + 2P₀ > 0`, `P₂ + 48P₀ > 0`,
`P₃ + 4P₂ > 0`, `P₃ - P₀ > 0`, `P₄ - P₀ > 0` force the quartic `P₀ + P₁y + ⋯ + P₄y⁴` to be positive
for every `y ≥ 0`. -/
theorem nsr_quartic_pos {P0 P1 P2 P3 P4 y : ℝ} (hy : 0 ≤ y) (h0 : 0 < P0) (h1 : 0 < P1 + 2 * P0)
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
theorem nsrLU_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nsrN t x 1 q (nsrVbar t x) (nsrLp q) - (-nsrNv t x 1 q) * (nsrVbar t x - nsrFl t x q)) =
      nsrLU0 t x + nsrLU1 t x * (q - 1) + nsrLU2 t x * (q - 1) ^ 2 + nsrLU3 t x * (q - 1) ^ 3
        + nsrLU4 t x * (q - 1) ^ 4 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrNv nsrVbar nsrLp nsrFl nsrLU0 nsrLU1 nsrLU2 nsrLU3 nsrLU4
  field_simp
  ring

/-- The cleared low-scale quartic on the high-ratio face. -/
theorem nsrLH_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nsrN t x (2 * t + 1 / 2) q (nsrVbar t x) (nsrLp q) -
        (-nsrNv t x (2 * t + 1 / 2) q) * (nsrVbar t x - nsrFl t x q)) =
      nsrLH0 t x + nsrLH1 t x * (q - 1) + nsrLH2 t x * (q - 1) ^ 2 + nsrLH3 t x * (q - 1) ^ 3
        + nsrLH4 t x * (q - 1) ^ 4 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrNv nsrVbar nsrLp nsrFl nsrLH0 nsrLH1 nsrLH2 nsrLH3 nsrLH4
  field_simp
  ring

/-- The common relaxation step on a low-scale face: positivity of the cleared quartic gives
`N > 0`. -/
theorem nsr_low_relax {t x k q v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : 2 * t ≤ k)
    (hq : 1 < q) (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v)
    (hP : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nsrN t x k q (nsrVbar t x) (nsrLp q) - (-nsrNv t x k q) * (nsrVbar t x - nsrFl t x q))) :
    0 < nsrN t x k q v (Real.log q) := by
  have hpos : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 := by
    have : 0 < q + 1 := by linarith
    positivity
  have hNv := nsrNv_nonpos ht.le hx.le hq.le hk
  refine nsr_N_pos_of_relax (vb := nsrVbar t x) (Lb := nsrLp q) (Fl := nsrFl t x q)
    (m := -nsrNv t x k q) ?_ (nsr_log_lt_Lp hq).le hNv
    (nsrNL_nonpos ht.le hx.le (by linarith) (by linarith))
    ((nsr_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith)
    (pos_of_mul_pos_right hP hpos.le)
  rw [hv]
  exact (nsr_secN_lt_vbar hx ht1).le

/-- **The unit low-scale face**: for
`0 < t ≤ 1/4`, `1/2 < x ≤ 7/3`, `x ≥ 1 - 2t`, `t ≤ T(x)`, `N(1) > 0`. -/
theorem nsr_low_unit {t x q v : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 4) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12)
    (hq : 1 < q) (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x 1 q v (Real.log q) := by
  have hx : 0 < x := by linarith
  have j0 := nsrLUJ0_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j1 := nsrLUJ1_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j2 := nsrLUJ2_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j3 := nsrLUJ3_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j4 := nsrLUJ4_dom t x hx0 hx1 ht.le ht1 hxt hT
  have j5 := nsrLUJ5_dom t x hx0 hx1 ht.le ht1 hxt hT
  have e0 : nsrLUJ0 t x = nsrLU0 t x := by unfold nsrLUJ0 nsrLU0; ring
  have e1 : nsrLUJ1 t x = nsrLU1 t x + 2 * nsrLU0 t x := by unfold nsrLUJ1 nsrLU0 nsrLU1; ring
  have e2 : nsrLUJ2 t x = nsrLU2 t x + 48 * nsrLU0 t x := by unfold nsrLUJ2 nsrLU0 nsrLU2; ring
  have e3 : nsrLUJ3 t x = nsrLU3 t x + 4 * nsrLU2 t x := by unfold nsrLUJ3 nsrLU2 nsrLU3; ring
  have e4 : nsrLUJ4 t x = nsrLU3 t x - nsrLU0 t x := by unfold nsrLUJ4 nsrLU0 nsrLU3; ring
  have e5 : nsrLUJ5 t x = nsrLU4 t x - nsrLU0 t x := by unfold nsrLUJ5 nsrLU0 nsrLU4; ring
  rw [e0] at j0; rw [e1] at j1; rw [e2] at j2; rw [e3] at j3; rw [e4] at j4; rw [e5] at j5
  have hQ := nsr_quartic_pos (y := q - 1) (by linarith) j0 j1 j2 j3 j4 j5
  refine nsr_low_relax ht (by linarith) hx (by linarith) hq hv hF ?_
  rw [nsrLU_P_eq hx (by linarith)]
  exact hQ

/-- **The high-ratio low-scale face**: for
`1/4 ≤ t ≤ 7/20`, `1/2 ≤ x ≤ 1`, `N(2t + 1/2) > 0`. -/
theorem nsr_low_kh {t x q v : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x)
    (hx1 : x ≤ 1) (hq : 1 < q) (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x (2 * t + 1 / 2) q v (Real.log q) := by
  have hx : 0 < x := by linarith
  have j0 := nsrLHJ0_dom t x ht0 ht1 hx0 hx1
  have j1 := nsrLHJ1_dom t x ht0 ht1 hx0 hx1
  have j2 := nsrLHJ2_dom t x ht0 ht1 hx0 hx1
  have j3 := nsrLHJ3_dom t x ht0 ht1 hx0 hx1
  have j4 := nsrLHJ4_dom t x ht0 ht1 hx0 hx1
  have j5 := nsrLHJ5_dom t x ht0 ht1 hx0 hx1
  have e0 : nsrLHJ0 t x = nsrLH0 t x := by unfold nsrLHJ0 nsrLH0; ring
  have e1 : nsrLHJ1 t x = nsrLH1 t x + 2 * nsrLH0 t x := by unfold nsrLHJ1 nsrLH0 nsrLH1; ring
  have e2 : nsrLHJ2 t x = nsrLH2 t x + 48 * nsrLH0 t x := by unfold nsrLHJ2 nsrLH0 nsrLH2; ring
  have e3 : nsrLHJ3 t x = nsrLH3 t x + 4 * nsrLH2 t x := by unfold nsrLHJ3 nsrLH2 nsrLH3; ring
  have e4 : nsrLHJ4 t x = nsrLH3 t x - nsrLH0 t x := by unfold nsrLHJ4 nsrLH0 nsrLH3; ring
  have e5 : nsrLHJ5 t x = nsrLH4 t x - nsrLH0 t x := by unfold nsrLHJ5 nsrLH0 nsrLH4; ring
  rw [e0] at j0; rw [e1] at j1; rw [e2] at j2; rw [e3] at j3; rw [e4] at j4; rw [e5] at j5
  have hQ := nsr_quartic_pos (y := q - 1) (by linarith) j0 j1 j2 j3 j4 j5
  refine nsr_low_relax (by linarith) (by linarith) hx (by linarith) hq hv hF ?_
  rw [nsrLH_P_eq hx (by linarith)]
  exact hQ

/-- `v̄ - g = (1 - t)x(N(x) - 3X³t)/(3W²X³)`, `N(x) = -2x³ - x² + 10x + 12`. -/
theorem nsr_vbar_sub_g {t x : ℝ} (hx : 0 < x) :
    (nsrVbar t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) * (3 * (1 + x) ^ 2 * (x + 2) ^ 3) =
      (1 - t) * x * (-2 * x ^ 3 - x ^ 2 + 10 * x + 12 - 3 * (x + 2) ^ 3 * t) := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  unfold nsrVbar
  field_simp
  ring

/-- **The secant ceiling**: `v ≥ g_c(d)` and `v < v̄` give `t < T(x)`, i.e.
`3(x + 2)³t < -2x³ - x² + 10x + 12`. -/
theorem nsr_t_lt_T {t x v : ℝ} (ht1 : t < 1) (hx : 0 < x) (hv : v = nsrSecN t x)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) :
    3 * (x + 2) ^ 3 * t < -2 * x ^ 3 - x ^ 2 + 10 * x + 12 := by
  have hvb := nsr_secN_lt_vbar hx ht1
  rw [← hv] at hvb
  have e := nsr_vbar_sub_g (t := t) hx
  have h1 : 0 < (nsrVbar t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) * (3 * (1 + x) ^ 2 * (x + 2) ^ 3) :=
    mul_pos (by linarith) (by positivity)
  rw [e] at h1
  have h2 : 0 < (1 - t) * x := mul_pos (by linarith) hx
  have := pos_of_mul_pos_right h1 h2.le
  linarith

/-- **The scalar low-scale exclusion**: on the necessary domain with `k ≥ 17t²`, `N_k > 0`. -/
theorem nsr_low_core {t x k q v : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) (hx : 0 < x) (hk1 : 1 ≤ k)
    (hk17 : 17 * t ^ 2 ≤ k) (hgap : k < 2 * t + 2 * x + x ^ 2) (hdur : x < 7 / 3 - 10 / 3 * t)
    (hq : 1 < q) (hqW : q < (1 + x) / (t + x)) (hv : v = nsrSecN t x) (hvU : v ≤ 1 - t + t ^ 2)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x k q v (Real.log q) := by
  have hT := nsr_t_lt_T (by linarith) hx hv hg
  -- `t < 7/20`
  have ht7 : t < 7 / 20 := by
    by_contra h
    push Not at h
    have hx8 : 8 / 15 < x := by nlinarith
    have := nsr_T_anti (xa := 8 / 15) (by norm_num) hx8.le ht.le hT.le
    norm_num at this
    linarith
  -- if `k ≥ 2t + x`, the scalar reverse exclusion applies
  by_cases hko : 2 * t + x ≤ k
  · exact nsr_reverse_core ht (by linarith) hx hk1 hko (by nlinarith) hgap hdur hq hqW hv hvU hF
  push Not at hko
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos (by linarith) hq.ne'
  have mono : ∀ k', k' ≤ k → nsrN t x k' q v (Real.log q) ≤ nsrN t x k q v (Real.log q) :=
    fun k' hk' => nsrN_mono_k ht (by linarith) hx hq.le hvU hL hk'
  rcases le_total t (1 / 4) with h4 | h4
  · exact lt_of_lt_of_le (nsr_low_unit ht h4 (by linarith) (by linarith) (by linarith) hT.le hq hv hF)
      (mono 1 hk1)
  · have hkh : 2 * t + 1 / 2 ≤ k := by nlinarith
    have hx1 : x ≤ 1 := by
      by_contra h
      push Not at h
      have := nsr_T_anti (xa := 1) (by norm_num) h.le ht.le hT.le
      norm_num at this
      linarith
    exact lt_of_lt_of_le (nsr_low_kh h4 ht7.le (by nlinarith) hx1 hq hv hF) (mono _ hkh)

end SmoothedOctagon
