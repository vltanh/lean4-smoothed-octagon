module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.LowerFace.Polynomials

/-!
# The central tests at beta equal to x

The normalized numerator polynomials have nonnegative coefficients and a
positive constant term. The three denominator-clearing identities transfer
their positivity to the lower-face tests.
-/

@[expose] public section
namespace SmoothedOctagon

/-- **The lower face of the `τ = T` test**: negative at `β = x`. -/
theorem lgr_lowT {x a : ℝ} (hx : 12 / 5 ≤ x) (_hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrGT x a x < 0 := by
  have hx1 : 1 < x := by linarith only [hx]
  apply lgr_GT_neg hx1 (by linarith only [ha]) hx1
  exact S0Central.Lower.numeratorT_pos hx ha ha'

/-- **The lower face of the `τ = 8T/9` test**: negative at `β = x`. -/
theorem lgr_low8 {x a : ℝ} (hx : 12 / 5 ≤ x) (_hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG8 x a x < 0 := by
  have hx1 : 1 < x := by linarith only [hx]
  apply lgr_G8_neg hx1 (by linarith only [ha]) hx1
  exact S0Central.Lower.numerator8_pos hx ha ha'

/-- **The lower face of the `τ = 2` test**: negative at `β = x`. -/
theorem lgr_low2 {x a : ℝ} (hx : 12 / 5 ≤ x) (_hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : lgrG2 x a x < 0 := by
  have hx1 : 1 < x := by linarith only [hx]
  apply lgr_G2_neg hx1 (by linarith only [ha]) hx1
  exact S0Central.Lower.numerator2_pos hx ha ha'

end SmoothedOctagon
