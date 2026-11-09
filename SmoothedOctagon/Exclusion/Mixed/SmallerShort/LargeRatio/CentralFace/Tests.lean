module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.LowerFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.TauTwo1
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.TauTwo2
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.MaxDuration1
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.MaxDuration2
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.NearMaxDuration1
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.NearMaxDuration2

/-!
# Smaller-short window, large ratio: the three central tests

On the central domain `Dom_c`
(`12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, `x ≤ β ≤ x + c₀(x)(α - 1)`, `c₀ = x(7x + 1)/(4x² + 11x + 1)`),
the slope `c₀(x)` is enclosed by a constant `c_j` on four `x`-intervals (`lgr_slope_le`), beta
convexity (`lgr_cen_two_chord`, `lgr_cen_T_chord`, `lgr_cen_8_chord`) bounds each test by its values
at `β = x` (`lgr_low2`, `lgr_lowT`, `lgr_low8`) and at `β = x + c_j(α - 1)` (`lgrU2_0_neg`, …).

## Main API

* `lgr_central_two`, `lgr_central_T`, `lgr_central_8`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The strong-order slope `c₀(x)` is at most a constant `c` where `x(7x + 1) ≤ c(4x² + 11x + 1)`. -/
theorem lgr_slope_le {x a b c : ℝ} (hx : 0 < x) (ha : 1 ≤ a)
    (hc : x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1))
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : b ≤ x + c * (a - 1) := by
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have : x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ c * (a - 1) := by
    rw [div_le_iff₀ hR]
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ a - 1)
    nlinarith
  linarith

/-- **The central `τ = 2` test** is negative on `Dom_c`. -/
theorem lgr_central_two {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrG2 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := lgr_low2 hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := lgr_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := lgr_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU2_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := lgr_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := lgr_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU2_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := lgr_slope_le (c := 5 / 4) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := lgr_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU2_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := lgr_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := lgr_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU2_3_neg h3.le hx9 ha ha')
    linarith

/-- **The central duration test `lgrGT`** (`τ = T`) is negative on `Dom_c`. -/
theorem lgr_central_T {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrGT x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := lgr_lowT hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := lgr_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := lgr_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrUT_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := lgr_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := lgr_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrUT_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := lgr_slope_le (c := 6 / 5) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := lgr_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrUT_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := lgr_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := lgr_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrUT_3_neg h3.le hx9 ha ha')
    linarith

/-- **The central duration test `lgrG8`** (`τ = 8T/9`) is negative on `Dom_c`. -/
theorem lgr_central_8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrG8 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := lgr_low8 hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := lgr_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := lgr_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU8_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := lgr_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := lgr_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU8_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := lgr_slope_le (c := 6 / 5) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := lgr_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU8_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := lgr_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := lgr_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (lgrU8_3_neg h3.le hx9 ha ha')
    linarith

end SmoothedOctagon
