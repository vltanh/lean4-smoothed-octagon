module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.Scale.Bounds
public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv

/-!
# The residual decreases with scale

The negative scale derivative increases in both scale and order gap.
Its corner value is positive, so the residual decreases throughout the
rectangle. This reduces the required sign to the terminal scale face.
-/

@[expose] public section
namespace SmoothedOctagon.HighRatioScale

private theorem slope_h_derivative (h j y : ℝ) :
    (slopePolynomial j y).derivative.eval h =
      ((slopeRow0 Polynomial.X (Polynomial.C j)).derivative).eval h +
        ((slopeRow1 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 1 +
        ((slopeRow2 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 2 +
        ((slopeRow3 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 3 +
        ((slopeRow4 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 4 +
        ((slopeRow5 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 5 +
        ((slopeRow6 Polynomial.X (Polynomial.C j)).derivative).eval h * y ^ 6 := by
  simp only [slopePolynomial, slope, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_pow, mul_zero, add_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]

private theorem slope_h_positive {h j y : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    0 < (slopePolynomial j y).derivative.eval h := by
  have b0 := slope_h_coefficient0 h0 h1 j0 j1
  have b1 := mul_le_mul_of_nonneg_right (slope_h_coefficient1 h0 h1 j0 j1) (pow_nonneg y0 1)
  have b2 := mul_le_mul_of_nonneg_right (slope_h_coefficient2 h0 h1 j0 j1) (pow_nonneg y0 2)
  have b3 := mul_le_mul_of_nonneg_right (slope_h_coefficient3 h0 h1 j0 j1) (pow_nonneg y0 3)
  have b4 := mul_le_mul_of_nonneg_right (slope_h_coefficient4 h0 h1 j0 j1) (pow_nonneg y0 4)
  have b5 := mul_le_mul_of_nonneg_right (slope_h_coefficient5 h0 h1 j0 j1) (pow_nonneg y0 5)
  have b6 := mul_le_mul_of_nonneg_right (slope_h_coefficient6 h0 h1 j0 j1) (pow_nonneg y0 6)
  have yp : y ^ 6 ≤ (1 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ y0 y1 6
  rw [slope_h_derivative]
  linarith only [b0, b1, b2, b3, b4, b5, b6, yp]

private theorem slope_j_derivative (h j y : ℝ) :
    (slopeGapPolynomial h y).derivative.eval j =
      ((slopeRow0 (Polynomial.C h) Polynomial.X).derivative).eval j +
        ((slopeRow1 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 1 +
        ((slopeRow2 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 2 +
        ((slopeRow3 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 3 +
        ((slopeRow4 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 4 +
        ((slopeRow5 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 5 +
        ((slopeRow6 (Polynomial.C h) Polynomial.X).derivative).eval j * y ^ 6 := by
  simp only [slopeGapPolynomial, slope, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_pow, mul_zero, add_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]

private theorem slope_j_positive {h j y : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    0 < (slopeGapPolynomial h y).derivative.eval j := by
  have b0 := slope_j_coefficient0 h0 h1 j0 j1
  have b1 := mul_le_mul_of_nonneg_right (slope_j_coefficient1 h0 h1 j0 j1) (pow_nonneg y0 1)
  have b2 := mul_le_mul_of_nonneg_right (slope_j_coefficient2 h0 h1 j0 j1) (pow_nonneg y0 2)
  have b3 := mul_le_mul_of_nonneg_right (slope_j_coefficient3 h0 h1 j0 j1) (pow_nonneg y0 3)
  have b4 := mul_le_mul_of_nonneg_right (slope_j_coefficient4 h0 h1 j0 j1) (pow_nonneg y0 4)
  have b5 := mul_le_mul_of_nonneg_right (slope_j_coefficient5 h0 h1 j0 j1) (pow_nonneg y0 5)
  have b6 := mul_le_mul_of_nonneg_right (slope_j_coefficient6 h0 h1 j0 j1) (pow_nonneg y0 6)
  have yp : y ^ 6 ≤ (1 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ y0 y1 6
  rw [slope_j_derivative]
  linarith only [b0, b1, b2, b3, b4, b5, b6, yp]

private theorem corner_floor {y : ℝ} (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    128 * 500 ≤ slope (1 / 5 : ℝ) (1 / 30) y := by
  have lo (n : ℕ) : 0 ≤ y ^ n := pow_nonneg y0 n
  have tail : y ^ 6 ≤ y ^ 5 / 4 := by nlinarith only [mul_le_mul_of_nonneg_left y1 (lo 5)]
  norm_num [slope, slopeRow0, slopeRow1, slopeRow2, slopeRow3, slopeRow4, slopeRow5, slopeRow6]
  linarith only [tail, lo 1, lo 2, lo 3, lo 4, lo 5]

theorem slope_floor {h j y : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    128 * 500 ≤ slope h j y := by
  have hm := UnitShape.polynomial_mono (p := slopePolynomial (1 / 30) y) h0
    (fun _ hs0 hs1 => (slope_h_positive hs0 (hs1.trans h1)
      le_rfl (by norm_num) y0 y1).le)
  have jm := UnitShape.polynomial_mono (p := slopeGapPolynomial h y) j0
    (fun _ js0 js1 => (slope_j_positive h0 h1 js0 (js1.trans j1) y0 y1).le)
  rw [slopePolynomial_eval, slopePolynomial_eval] at hm
  rw [slopeGapPolynomial_eval, slopeGapPolynomial_eval] at jm
  exact (corner_floor y0 y1).trans (hm.trans jm)

theorem scale_reduce {h j y : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    value (1 / 4 : ℝ) j y ≤ value h j y := by
  have hm := poly_anti (fun s => (valuePolynomial j y).hasDerivAt s)
    (a := h) (b := 1 / 4) (by
      intro s hs0 hs1
      rw [value_derivative]
      have hf := slope_floor (h0.trans hs0) hs1 j0 j1 y0 y1
      linarith only [hf]) le_rfl h1 le_rfl
  simpa only [valuePolynomial_eval] using hm

end SmoothedOctagon.HighRatioScale
