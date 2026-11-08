module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Unit
public import SmoothedOctagon.Exclusion.Mixed.Hand.CertStrip

/-!
# Case M2 by hand: the reverse scale strip `k = 29t²/4`

`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` §§2-3: on `13/35 ≤ t ≤ 2/5`, `0 < x ≤ 9/35` with the
centre gap `29t²/4 < 2t + 2x + x²`, the exact incoming secant and its floor give `N(29t²/4) > 0`.
Route: the cleared cubic `P_{29t²/4}` satisfies the six signs of the unit shape directly
(`Hand/CertStrip`), so the comparison with the unit shape at `t₀ = 13/35` is not needed.

## Main API

* `nhS_P_eq`, `nhS_signs`, `nh_strip`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared cubic on the scale face `k = 29t²/4`. -/
theorem nhS_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nhN t x (29 / 4 * t ^ 2) q (nhVbar t x) (nhLp q) - (q - 1) * (nhVbar t x - nhFl t x q)) =
      nhSC0 t x + nhSC1 t x * (q - 1) + nhSC2 t x * (q - 1) ^ 2 + nhSC3 t x * (q - 1) ^ 3 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nhN nhVbar nhLp nhFl nhSC0 nhSC1 nhSC2 nhSC3
  field_simp
  ring

/-- The strip lies in `x ≥ 7061/58240` (`x ≥ 3/25`, then the chord bound on `2x + x²`). -/
theorem nhS_x_lower {t x : ℝ} (ht0 : 13 / 35 ≤ t) (hx : 0 < x) (hx1 : x ≤ 9 / 35)
    (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) : 7061 / 58240 ≤ x := by
  have hf : 1261 / 4900 ≤ 29 / 4 * t ^ 2 - 2 * t := by nlinarith
  have hx3 : 3 / 25 ≤ x := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h.le hx.le]
  have hchord : (x - 3 / 25) * (x - 9 / 35) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- **The six signs on the scale strip.** -/
theorem nhS_signs {t x : ℝ} (ht0 : 13 / 35 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 0 < x) (hx1 : x ≤ 9 / 35)
    (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) :
    0 < nhSC0 t x ∧ 0 < 20 * x * nhSC1 t x + 3 * nhSC0 t x ∧
      0 < 53 * nhSC0 t x + 20 * x ^ 2 * nhSC2 t x ∧
      0 < 24 * x ^ 3 * nhSC3 t x + 12 * x ^ 2 * nhSC2 t x - nhSC0 t x ∧
      0 < 40 * x ^ 3 * nhSC3 t x + 30 * x ^ 2 * nhSC2 t x + 7 * nhSC0 t x ∧
      0 < 24 * x ^ 3 * nhSC3 t x - nhSC0 t x := by
  have hxl := nhS_x_lower ht0 hx hx1 hgap
  have hx2 : 0 < x ^ 2 := by positivity
  have g : 0 < (9 / 35 : ℝ) - 7061 / 58240 := by norm_num
  have e0 : nhSC0 t x = x ^ 2 * nhSJr0 t x := by unfold nhSC0 nhSJr0; ring
  have e1 : 20 * x * nhSC1 t x + 3 * nhSC0 t x = x ^ 2 * nhSJr1 t x := by
    unfold nhSC0 nhSC1 nhSJr1; ring
  have e2 : 53 * nhSC0 t x + 20 * x ^ 2 * nhSC2 t x = x ^ 2 * nhSJr2 t x := by
    unfold nhSC0 nhSC2 nhSJr2; ring
  have e3 : 24 * x ^ 3 * nhSC3 t x + 12 * x ^ 2 * nhSC2 t x - nhSC0 t x = x ^ 2 * nhSJr3 t x := by
    unfold nhSC0 nhSC2 nhSC3 nhSJr3; ring
  have e4 : 40 * x ^ 3 * nhSC3 t x + 30 * x ^ 2 * nhSC2 t x + 7 * nhSC0 t x = x ^ 2 * nhSJr4 t x := by
    unfold nhSC0 nhSC2 nhSC3 nhSJr4; ring
  have e5 : 24 * x ^ 3 * nhSC3 t x - nhSC0 t x = x ^ 2 * nhSJr5 t x := by
    unfold nhSC0 nhSC3 nhSJr5; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact mul_pos hx2 (nhSJr0_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e1]; exact mul_pos hx2 (nhSJr1_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e2]; exact mul_pos hx2 (nhSJr2_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e3]; exact mul_pos hx2 (nhSJr3_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e4]; exact mul_pos hx2 (nhSJr4_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e5]; exact mul_pos hx2 (nhSJr5_pos0 t x ht0 ht1 hxl hx1 g)

/-- **The scale strip** (`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` §§2-3): `N(29t²/4) > 0`. -/
theorem nh_strip {t x q v : ℝ} (ht0 : 13 / 35 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 0 < x)
    (hx1 : x ≤ 9 / 35) (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q)
    (hv : v = nhSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nhN t x (29 / 4 * t ^ 2) q v (Real.log q) := by
  have ht : 0 < t := by linarith
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := nhS_signs ht0 ht1 hx hx1 hgap
  have hc := nh_cubic_pos hx (by linarith : (0 : ℝ) ≤ q - 1) s0 s1 s2 s3 s4 s5
  rw [← nhS_P_eq hx (by linarith)] at hc
  have hpos : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 := by
    have : 0 < q + 1 := by linarith
    positivity
  have hP := pos_of_mul_pos_right hc hpos.le
  refine nh_N_pos_of_relax (vb := nhVbar t x) (Lb := nhLp q) (Fl := nhFl t x q) (m := q - 1)
    ?_ (nh_log_lt_Lp hq).le (nhNv_nonpos ht.le hx.le hq.le (by nlinarith))
    (nhNL_nonpos ht.le hx.le (by linarith) (by positivity))
    ((nh_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith) hP
  rw [hv]; exact (nh_secN_lt_vbar hx (by linarith)).le

end SmoothedOctagon
