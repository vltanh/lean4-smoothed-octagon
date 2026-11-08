module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenLow
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen2a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen2b
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenTa
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenTb
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen8a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen8b

/-!
# Hand proof of the smaller-short case, gate S0: the three central tests

`archive/lighter-proofs/SHORT_DURATION_CENTRAL_TAU_TWO.md` §1 and
`SHORT_DURATION_CENTRAL_UPPER_FACES.md` §§1-2: on the central domain `Dom_c`
(`12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, `x ≤ β ≤ x + c₀(x)(α - 1)`, `c₀ = x(7x + 1)/(4x² + 11x + 1)`),
the slope `c₀(x)` is enclosed by a constant `c_j` on four `x`-intervals (`hl0_slope_le`), beta
convexity (`hl0_cen_two_chord`, `hl0_cen_T_chord`, `hl0_cen_8_chord`) bounds each test by its values
at `β = x` (`hl0_low2`, `hl0_lowT`, `hl0_low8`) and at `β = x + c_j(α - 1)` (`hl0U2_j_neg`, …).

## Main API

* `hl0_central_two`, `hl0_central_T`, `hl0_central_8`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The strong-order slope `c₀(x)` is at most a constant `c` where `x(7x + 1) ≤ c(4x² + 11x + 1)`. -/
theorem hl0_slope_le {x a b c : ℝ} (hx : 0 < x) (ha : 1 ≤ a)
    (hc : x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1))
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : b ≤ x + c * (a - 1) := by
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have : x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ c * (a - 1) := by
    rw [div_le_iff₀ hR]
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ a - 1)
    nlinarith
  linarith

/-- **The central `τ = 2` test** (`CENTRAL_TAU_TWO_SIGN` (3)) is negative on `Dom_c`. -/
theorem hl0_central_two {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : hl0G2 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := hl0_low2 hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := hl0_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := hl0_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U2_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := hl0_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := hl0_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U2_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := hl0_slope_le (c := 5 / 4) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := hl0_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U2_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := hl0_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := hl0_cen_two_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U2_3_neg h3.le hx9 ha ha')
    linarith

/-- **The central duration test `hl0GT`** (`CENTRAL_DURATION_FACES` (5)) is negative on `Dom_c`. -/
theorem hl0_central_T {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : hl0GT x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := hl0_lowT hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := hl0_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := hl0_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0UT_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := hl0_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := hl0_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0UT_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := hl0_slope_le (c := 6 / 5) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := hl0_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0UT_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := hl0_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := hl0_cen_T_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0UT_3_neg h3.le hx9 ha ha')
    linarith

/-- **The central duration test `hl0G8`** (`CENTRAL_DURATION_FACES` (5)) is negative on `Dom_c`. -/
theorem hl0_central_8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : hl0G8 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hlow := hl0_low8 hx hx9 ha ha'
  rcases le_or_gt x (5 / 2) with h1 | h1
  · have hb' := hl0_slope_le (c := 7 / 8) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)]) hb
    have h := hl0_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U8_0_neg hx h1 ha ha')
    linarith
  rcases le_or_gt x 3 with h2 | h2
  · have hb' := hl0_slope_le (c := 1) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 3 - x)]) hb
    have h := hl0_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U8_1_neg h1.le h2 ha ha')
    rw [one_mul] at h h'
    linarith
  rcases le_or_gt x 5 with h3 | h3
  · have hb' := hl0_slope_le (c := 6 / 5) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 3) (by linarith : (0 : ℝ) ≤ 5 - x)]) hb
    have h := hl0_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U8_2_neg h2.le h3 ha ha')
    linarith
  · have hb' := hl0_slope_le (c := 3 / 2) hx0 ha
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb
    have h := hl0_cen_8_chord hx hx9 ha ha' hxb hb'
    have h' := max_lt hlow (hl0U8_3_neg h3.le hx9 ha ha')
    linarith

end SmoothedOctagon
