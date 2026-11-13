module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Boundaries

/-!
# The three tests throughout the outer strip

The two exact beta boundary signs and the chord bound give the strip
signs. The order boundary satisfies `beta + alpha ≤ 2x` on this strip.
-/

@[expose] public section
namespace SmoothedOctagon.S0Outer

theorem upperBeta_add_alpha_le {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : 1 ≤ a) (ham : a ≤ (2 * x + 3) / 5) : S0Central.upperBeta x a + a ≤ 2 * x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hq := S0Central.denominator_pos hx0.le
  have hc : x * (7 * x + 1) ≤ 3 / 2 * S0Central.gapDenominator x := by
    unfold S0Central.gapDenominator
    nlinarith only [hx, mul_nonneg hx0.le (sub_nonneg.mpr hx9)]
  have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr ha)
  have hb : S0Central.upperBeta x a ≤ x + 3 / 2 * (a - 1) := by
    unfold S0Central.upperBeta
    have hh : x * (7 * x + 1) * (a - 1) / S0Central.gapDenominator x ≤ 3 / 2 * (a - 1) := by
      rw [div_le_iff₀ hq]
      nlinarith only [hm]
    linarith only [hh]
  linarith only [hb, ham]

theorem strip2_neg {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5)
    (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrO2 x a b (ssUhat x b) < 0 := by
  have hchord := lgr_strip_chord_2 hx hx9 ha ham hb hb' 
  exact lt_of_le_of_lt hchord
    (max_lt (Boundaries.lower2_neg hx ha ham) (Boundaries.upper2_neg hx ha ham))

theorem stripT_neg {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5)
    (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrOT x a b (ssUhat x b) < 0 := by
  have hchord := lgr_strip_chord_T hx hx9 ha ham hb hb' 
    (upperBeta_add_alpha_le hx hx9 (by linarith only [hx, ha]) ham)
  exact lt_of_le_of_lt hchord
    (max_lt (Boundaries.lowerT_neg hx ha ham) (Boundaries.upperT_neg hx ha ham))

theorem strip8_neg {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5)
    (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrO8 x a b (ssUhat x b) < 0 := by
  have hchord := lgr_strip_chord_8 hx hx9 ha ham hb hb' 
    (upperBeta_add_alpha_le hx hx9 (by linarith only [hx, ha]) ham)
  exact lt_of_le_of_lt hchord
    (max_lt (Boundaries.lower8_neg hx ha ham) (Boundaries.upper8_neg hx ha ham))

end SmoothedOctagon.S0Outer
