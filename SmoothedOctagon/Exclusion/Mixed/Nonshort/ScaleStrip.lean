module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.ScaleStrip.Signs

/-!
# Case M2, reverse successor: the reverse scale strip `k = 29t²/4`

On `13/35 ≤ t ≤ 2/5`, `0 < x ≤ 9/35` with the centre gap `29t²/4 < 2t + 2x + x²`, the exact
incoming secant and its floor give `N(29t²/4) > 0`: the cleared cubic `P_{29t²/4}` satisfies the
six signs of the unit shape (`Nonshort/ScaleStrip/Signs`), so it is positive for every `y ≥ 0`.

## Main API

* `nsrS_P_eq`, `nsrS_signs`, `nsr_strip`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared cubic on the scale face `k = 29t²/4`. -/
theorem nsrS_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nsrN t x (29 / 4 * t ^ 2) q (nsrVbar t x) (nsrLp q) - (q - 1) * (nsrVbar t x - nsrFl t x q)) =
      nsrSC0 t x + nsrSC1 t x * (q - 1) + nsrSC2 t x * (q - 1) ^ 2 + nsrSC3 t x * (q - 1) ^ 3 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrVbar nsrLp nsrFl nsrSC0 nsrSC1 nsrSC2 nsrSC3
  field_simp
  ring

/-- The strip lies in `x ≥ 7061/58240` (`x ≥ 3/25`, then the chord bound on `2x + x²`). -/
theorem nsrS_x_lower {t x : ℝ} (ht0 : 13 / 35 ≤ t) (hx : 0 < x) (hx1 : x ≤ 9 / 35)
    (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) : 7061 / 58240 ≤ x := by
  have hf : 1261 / 4900 ≤ 29 / 4 * t ^ 2 - 2 * t := by nlinarith
  have hx3 : 3 / 25 ≤ x := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h.le hx.le]
  have hchord : (x - 3 / 25) * (x - 9 / 35) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- **The six signs on the scale strip.** -/
theorem nsrS_signs {t x : ℝ} (ht0 : 13 / 35 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 0 < x) (hx1 : x ≤ 9 / 35)
    (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) :
    0 < nsrSC0 t x ∧ 0 < 20 * x * nsrSC1 t x + 3 * nsrSC0 t x ∧
      0 < 53 * nsrSC0 t x + 20 * x ^ 2 * nsrSC2 t x ∧
      0 < 24 * x ^ 3 * nsrSC3 t x + 12 * x ^ 2 * nsrSC2 t x - nsrSC0 t x ∧
      0 < 40 * x ^ 3 * nsrSC3 t x + 30 * x ^ 2 * nsrSC2 t x + 7 * nsrSC0 t x ∧
      0 < 24 * x ^ 3 * nsrSC3 t x - nsrSC0 t x := by
  have hxl := nsrS_x_lower ht0 hx hx1 hgap
  have hx2 : 0 < x ^ 2 := by positivity
  have g : 0 < (9 / 35 : ℝ) - 7061 / 58240 := by norm_num
  have e0 : nsrSC0 t x = x ^ 2 * nsrSJr0 t x := by unfold nsrSC0 nsrSJr0; ring
  have e1 : 20 * x * nsrSC1 t x + 3 * nsrSC0 t x = x ^ 2 * nsrSJr1 t x := by
    unfold nsrSC0 nsrSC1 nsrSJr1; ring
  have e2 : 53 * nsrSC0 t x + 20 * x ^ 2 * nsrSC2 t x = x ^ 2 * nsrSJr2 t x := by
    unfold nsrSC0 nsrSC2 nsrSJr2; ring
  have e3 : 24 * x ^ 3 * nsrSC3 t x + 12 * x ^ 2 * nsrSC2 t x - nsrSC0 t x = x ^ 2 * nsrSJr3 t x := by
    unfold nsrSC0 nsrSC2 nsrSC3 nsrSJr3; ring
  have e4 : 40 * x ^ 3 * nsrSC3 t x + 30 * x ^ 2 * nsrSC2 t x + 7 * nsrSC0 t x = x ^ 2 * nsrSJr4 t x := by
    unfold nsrSC0 nsrSC2 nsrSC3 nsrSJr4; ring
  have e5 : 24 * x ^ 3 * nsrSC3 t x - nsrSC0 t x = x ^ 2 * nsrSJr5 t x := by
    unfold nsrSC0 nsrSC3 nsrSJr5; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact mul_pos hx2 (nsrSJr0_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e1]; exact mul_pos hx2 (nsrSJr1_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e2]; exact mul_pos hx2 (nsrSJr2_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e3]; exact mul_pos hx2 (nsrSJr3_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e4]; exact mul_pos hx2 (nsrSJr4_pos0 t x ht0 ht1 hxl hx1 g)
  · rw [e5]; exact mul_pos hx2 (nsrSJr5_pos0 t x ht0 ht1 hxl hx1 g)

/-- **The scale strip**: `N(29t²/4) > 0`. -/
theorem nsr_strip {t x q v : ℝ} (ht0 : 13 / 35 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 0 < x)
    (hx1 : x ≤ 9 / 35) (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q)
    (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x (29 / 4 * t ^ 2) q v (Real.log q) := by
  have ht : 0 < t := by linarith
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := nsrS_signs ht0 ht1 hx hx1 hgap
  have hc := nsr_cubic_pos hx (by linarith : (0 : ℝ) ≤ q - 1) s0 s1 s2 s3 s4 s5
  rw [← nsrS_P_eq hx (by linarith)] at hc
  have hpos : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 := by
    have : 0 < q + 1 := by linarith
    positivity
  have hP := pos_of_mul_pos_right hc hpos.le
  refine nsr_N_pos_of_relax (vb := nsrVbar t x) (Lb := nsrLp q) (Fl := nsrFl t x q) (m := q - 1)
    ?_ (nsr_log_lt_Lp hq).le (nsrNv_nonpos ht.le hx.le hq.le (by nlinarith))
    (nsrNL_nonpos ht.le hx.le (by linarith) (by positivity))
    ((nsr_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith) hP
  rw [hv]; exact (nsr_secN_lt_vbar hx (by linarith)).le

end SmoothedOctagon
