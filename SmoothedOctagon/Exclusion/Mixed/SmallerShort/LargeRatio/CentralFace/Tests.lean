module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.LowerFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.UpperBoundary

/-!
# Smaller-short window, large ratio: the three central tests

Beta convexity bounds each test by its values at `β = x` and at the exact
strong-order boundary `S0Central.upperBeta`. The lower-face signs and the
upper-boundary signs then give negativity throughout the central domain.
-/

@[expose] public section
namespace SmoothedOctagon

/-- **The central `τ = 2` test** is negative on `Dom_c`. -/
theorem lgr_central_two {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrG2 x a b < 0 := by
  have hlow := lgr_low2 hx hx9 ha ha'
  have hupp := S0Central.upper2_neg hx ha ha'
  have hchord := lgr_cen_two_chord hx hx9 ha ha' hxb hb
  exact lt_of_le_of_lt hchord (max_lt hlow hupp)

/-- **The central duration test `lgrGT`** (`τ = T`) is negative on `Dom_c`. -/
theorem lgr_central_T {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrGT x a b < 0 := by
  have hlow := lgr_lowT hx hx9 ha ha'
  have hupp := S0Central.upperT_neg hx ha ha'
  have hchord := lgr_cen_T_chord hx hx9 ha ha' hxb hb
  exact lt_of_le_of_lt hchord (max_lt hlow hupp)

/-- **The central duration test `lgrG8`** (`τ = 8T/9`) is negative on `Dom_c`. -/
theorem lgr_central_8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : lgrG8 x a b < 0 := by
  have hlow := lgr_low8 hx hx9 ha ha'
  have hupp := S0Central.upper8_neg hx ha ha'
  have hchord := lgr_cen_8_chord hx hx9 ha ha' hxb hb
  exact lt_of_le_of_lt hchord (max_lt hlow hupp)

end SmoothedOctagon
