module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Scale
public import SmoothedOctagon.Exclusion.Mixed.Hand.Low
public import SmoothedOctagon.Exclusion.Mixed.Hand.Gap
public import SmoothedOctagon.Exclusion.Mixed.Hand.CertHighT

/-!
# Case M2 by hand: the high-ratio exclusion `t < 2/5`

If `t ≥ 2/5`, the sharpened scale `a² < 2/3`
(`nh_a_sq`) gives `k > 7t²`; `t < T(x)` gives `x < 1/3` and the centre gap gives `x > 1/7`.
Lowering `k` to `7t²`, the cleared cubic `P = C₀ + C₁y + C₂y² + C₃y³` is positive: `C₀ > 0` and,
on each of the four `x`-rows, `C₁ > b`, `C₂ > -M`, `C₃ > c` with `4bc > M²`
(`Hand/CertHighT`), so `C₁ + C₂y + C₃y² > 0` for `y ≥ 0`. Hence `N > 0`, contrary to `N < 0`.

## Main API

* `nh_row_cubic`: the row argument.
* `nhT_P_eq`, `nhT_poly_pos`.
* `nh_high_t'`: **`t < 2/5`** for every actual window.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The row argument: `C₁ > b`, `C₂ > -M`, `C₃ > c`, `4bc > M²`, `c > 0`, `C₀ > 0` give
`C₀ + C₁y + C₂y² + C₃y³ > 0` for `y ≥ 0`. -/
theorem nh_row_cubic {C0 C1 C2 C3 b M c y : ℝ} (hy : 0 ≤ y) (h0 : 0 < C0) (h1 : b < C1)
    (h2 : -M < C2) (h3 : c < C3) (hc : 0 < c) (hd : M ^ 2 < 4 * b * c) :
    0 < C0 + C1 * y + C2 * y ^ 2 + C3 * y ^ 3 := by
  have hq : 0 < b - M * y + c * y ^ 2 := by
    have : 0 < 4 * c * (b - M * y + c * y ^ 2) := by nlinarith [sq_nonneg (2 * c * y - M)]
    have h4c : 0 < 4 * c := by linarith
    exact pos_of_mul_pos_right this h4c.le
  have k1 : 0 ≤ (C1 - b) * y := mul_nonneg (by linarith) hy
  have k2 : 0 ≤ (C2 + M) * y ^ 2 := mul_nonneg (by linarith) (by positivity)
  have k3 : 0 ≤ (C3 - c) * y ^ 3 := mul_nonneg (by linarith) (by positivity)
  have k4 : 0 ≤ y * (b - M * y + c * y ^ 2) := mul_nonneg hy hq.le
  nlinarith

/-- The cleared cubic on the face `k = 7t²`. -/
theorem nhT_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nhN t x (7 * t ^ 2) q (nhVbar t x) (nhLp q) - (q - 1) * (nhVbar t x - nhFl t x q)) =
      nhTC0 t x + nhTC1 t x * (q - 1) + nhTC2 t x * (q - 1) ^ 2 + nhTC3 t x * (q - 1) ^ 3 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nhN nhVbar nhLp nhFl nhTC0 nhTC1 nhTC2 nhTC3
  field_simp
  ring

/-- The cubic is positive on the rectangle `2/5 ≤ t ≤ 1/2`, `1/7 ≤ x ≤ 1/3`, for `y ≥ 0`. -/
theorem nhT_poly_pos {t x y : ℝ} (ht0 : 2 / 5 ≤ t) (ht1 : t ≤ 1 / 2) (hx0 : 1 / 7 ≤ x)
    (hx1 : x ≤ 1 / 3) (hy : 0 ≤ y) :
    0 < nhTC0 t x + nhTC1 t x * y + nhTC2 t x * y ^ 2 + nhTC3 t x * y ^ 3 := by
  have h0 := nhTC0_pos t x ht0 ht1 hx0 hx1
  rcases le_total x (1 / 5) with h1 | h1
  · have a := nhTC1_r0_pos t x ht0 ht1 hx0 h1
    have b := nhTC2_r0_pos t x ht0 ht1 hx0 h1
    have c := nhTC3_r0_pos t x ht0 ht1 hx0 h1
    exact nh_row_cubic (b := 9 / 10) (M := 1) (c := 20) hy h0 (by linarith) (by linarith)
      (by linarith) (by norm_num) (by norm_num)
  rcases le_total x (3 / 10) with h2 | h2
  · have a := nhTC1_r1_pos t x ht0 ht1 h1 h2
    have b := nhTC2_r1_pos t x ht0 ht1 h1 h2
    have c := nhTC3_r1_pos t x ht0 ht1 h1 h2
    exact nh_row_cubic (b := 3 / 2) (M := 10) (c := 26) hy h0 (by linarith) (by linarith)
      (by linarith) (by norm_num) (by norm_num)
  rcases le_total x (8 / 25) with h3 | h3
  · have a := nhTC1_r2_pos t x ht0 ht1 h2 h3
    have b := nhTC2_r2_pos t x ht0 ht1 h2 h3
    have c := nhTC3_r2_pos t x ht0 ht1 h2 h3
    exact nh_row_cubic (b := 17 / 10) (M := 13) (c := 38) hy h0 (by linarith) (by linarith)
      (by linarith) (by norm_num) (by norm_num)
  · have a := nhTC1_r3_pos t x ht0 ht1 h3 hx1
    have b := nhTC2_r3_pos t x ht0 ht1 h3 hx1
    have c := nhTC3_r3_pos t x ht0 ht1 h3 hx1
    exact nh_row_cubic (b := 3 / 2) (M := 31 / 2) (c := 41) hy h0 (by linarith) (by linarith)
      (by linarith) (by norm_num) (by norm_num)

/-- **The high-ratio exclusion**: `t < 2/5`. -/
theorem nh_high_t' (W : M2Window) : W.nt < 2 / 5 := by
  obtain ⟨ht, ht2, hx, hk1, hq, hqW, hv, hvU, hg, hF, hak⟩ := nh_window_basic W
  by_contra hcon
  push Not at hcon
  have ha2 := nh_a_sq W
  have ha := W.a_pos
  -- `k > 7t²`
  have hk7 : 7 * W.nt ^ 2 < W.nk := by
    have hkt : 0 < W.nk - W.nt ^ 2 := by
      have : 0 < W.a ^ 2 := by positivity
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos this.le h
      nlinarith
    nlinarith [mul_lt_mul_of_pos_right ha2 hkt]
  have hgap : W.nk < 2 * W.nt + 2 * W.nx + W.nx ^ 2 := by
    have h := nh_centre_gap' W
    have hT : 0 < W.a + W.c := by linarith [W.a_lt_c]
    unfold M2Window.nk M2Window.nt M2Window.nx
    rw [div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hT := nh_t_lt_T (by linarith) hx hv hg
  -- `x < 1/3`
  have hx3 : W.nx < 1 / 3 := by
    by_contra h; push Not at h
    have := nh_T_anti (xa := 1 / 3) (by norm_num) h ht.le hT.le
    norm_num at this
    linarith
  -- `x > 1/7`
  have hx7 : 1 / 7 < W.nx := by
    by_contra h; push Not at h
    nlinarith
  -- lower `k` to `7t²`
  have hL : Real.log W.nq < W.nq - 1 := Real.log_lt_sub_one_of_pos (by linarith) hq.ne'
  have hmono := nhN_mono_k ht (by linarith) hx hq.le hvU hL hk7.le
  have hpos : 0 < nhN W.nt W.nx (7 * W.nt ^ 2) W.nq W.v (Real.log W.nq) := by
    have hc := nhT_poly_pos hcon ht2.le hx7.le hx3.le (by linarith : (0 : ℝ) ≤ W.nq - 1)
    rw [← nhT_P_eq hx (by linarith)] at hc
    have h6 : 0 < 6 * (W.nq + 1) * (1 + W.nx) ^ 2 * (W.nx + 2) ^ 3 := by
      have : 0 < W.nq + 1 := by linarith
      positivity
    have hP := pos_of_mul_pos_right hc h6.le
    refine nh_N_pos_of_relax (vb := nhVbar W.nt W.nx) (Lb := nhLp W.nq)
      (Fl := nhFl W.nt W.nx W.nq) (m := W.nq - 1) ?_ (nh_log_lt_Lp hq).le
      (nhNv_nonpos ht.le hx.le hq.le (by nlinarith))
      (nhNL_nonpos ht.le hx.le (by linarith) (by positivity))
      ((nh_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith) hP
    rw [hv]; exact (nh_secN_lt_vbar hx (by linarith)).le
  linarith [nh_window_N_neg W]

end SmoothedOctagon
