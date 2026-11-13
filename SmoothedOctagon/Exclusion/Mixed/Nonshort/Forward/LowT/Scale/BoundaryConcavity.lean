module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryCalculus
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryCoefficients

/-!
# Concavity of the maximum-duration scale derivative

The high gap powers have a nonpositive combined contribution. A tangent
bound for the cube of the squared gap leaves a convex quartic, whose two
endpoint values are negative.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

theorem boundaryCurvature_eq (h j : ℝ) :
    (weightedDerivative 7 (weightedDerivative 6 (boundaryPolynomial h))).eval j =
      boundaryCurvature h j := by
  rw [weighted_second]
  have h1 := boundary_derivative_horner 1 h j
  have h2 := boundary_derivative_horner 2 h j
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h1 h2
  rw [h1, h2, boundary_eval_horner]
  norm_num [boundaryCurvature, Fin.sum_univ_succ, boundaryCurvatureCoefficient,
    boundaryCoefficients, nltDer, nltDerAux, polyHorner]
  ring

private def quartic (j : ℝ) : ℝ := -25 - 62 * j + 740 * j ^ 2 - 1600 * j ^ 4

private theorem quartic_ceiling {j : ℝ} (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) :
    quartic j ≤ -(1 / 2) := by
  let p : Polynomial ℝ := Polynomial.C 25 + 62 * Polynomial.X
    - 740 * Polynomial.X ^ 2 + 1600 * Polynomial.X ^ 4
  have hf := UnitShape.polynomial_floor (p := p) (m := 1 / 2) hj0 hj1
    (by
      intro s hs0 hs1
      have hsq : s ^ 2 ≤ 1 / 16 := by nlinarith only [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
      norm_num [p, Polynomial.derivative_mul, Polynomial.derivative_pow]
      nlinarith only [hsq])
    (by norm_num [p]) (by norm_num [p])
  norm_num [p] at hf
  unfold quartic
  linarith only [hf]

theorem boundary_curvature_ceiling {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : boundaryCurvature h j ≤ -30000 := by
  have e0 := mul_le_mul_of_nonneg_right (boundary_coefficient0_ceiling h0 h1) (pow_nonneg hj0 0)
  have e1 := mul_le_mul_of_nonneg_right (boundary_coefficient1_ceiling h0 h1) (pow_nonneg hj0 1)
  have e2 := mul_le_mul_of_nonneg_right (boundary_coefficient2_ceiling h0 h1) (pow_nonneg hj0 2)
  have e3 := mul_le_mul_of_nonneg_right (boundary_coefficient3_ceiling h0 h1) (pow_nonneg hj0 3)
  have e4 := mul_le_mul_of_nonneg_right (boundary_coefficient4_ceiling h0 h1) (pow_nonneg hj0 4)
  have e5 := mul_le_mul_of_nonneg_right (boundary_coefficient5_ceiling h0 h1) (pow_nonneg hj0 5)
  have e6 := mul_le_mul_of_nonneg_right (boundary_coefficient6_ceiling h0 h1) (pow_nonneg hj0 6)
  have e7 := mul_le_mul_of_nonneg_right (boundary_coefficient7_ceiling h0 h1) (pow_nonneg hj0 7)
  have e8 := mul_le_mul_of_nonneg_right (boundary_coefficient8_ceiling h0 h1) (pow_nonneg hj0 8)
  have e9 := mul_le_mul_of_nonneg_right (boundary_coefficient9_ceiling h0 h1) (pow_nonneg hj0 9)
  have e10 := mul_le_mul_of_nonneg_right (boundary_coefficient10_ceiling h0 h1) (pow_nonneg hj0 10)
  have e11 := mul_le_mul_of_nonneg_right (boundary_coefficient11_ceiling h0 h1) (pow_nonneg hj0 11)
  have e12 := mul_le_mul_of_nonneg_right (boundary_coefficient12_ceiling h0 h1) (pow_nonneg hj0 12)
  have e13 := mul_le_mul_of_nonneg_right (boundary_coefficient13_ceiling h0 h1) (pow_nonneg hj0 13)
  have e14 := mul_le_mul_of_nonneg_right (boundary_coefficient14_ceiling h) (pow_nonneg hj0 14)
  have step (n : ℕ) : j ^ (n + 1) ≤ (1 / 4 : ℝ) * j ^ n := nlt_pw hj0 hj1 n
  have htail : -1080000000 * j ^ 10 + 2106000000 * j ^ 11 + 1626000000 * j ^ 12
      + 474000000 * j ^ 13 + 48000000 * j ^ 14 ≤ 0 := by
    linarith only [step 10, step 11, step 12, step 13, pow_nonneg hj0 10]
  have hcore : boundaryCurvature h j ≤ -3180000 - 3720000 * j + 60000000 * j ^ 2
      + 180000000 * j ^ 3 - 96000000 * j ^ 4 - 1740000000 * j ^ 5
      - 5700000000 * j ^ 6 := by
    norm_num [boundaryCurvature, Fin.sum_univ_succ]
    linarith only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, htail]
  have hshort : boundaryCurvature h j ≤ -3180000 - 3720000 * j + 105000000 * j ^ 2
      - 96000000 * j ^ 4 - 12660000000 * j ^ 6 := by
    linarith only [hcore, step 2, step 5]
  have ht := mul_nonneg (sq_nonneg (j ^ 2 - 1 / 25))
    (show 0 ≤ j ^ 2 + 2 / 25 by positivity)
  have he : boundaryCurvature h j ≤ 60000 * quartic j := by
    unfold quartic
    nlinarith only [hshort, ht, sq_nonneg j]
  linarith only [he, quartic_ceiling hj0 hj1]

end SmoothedOctagon.LowTScale
