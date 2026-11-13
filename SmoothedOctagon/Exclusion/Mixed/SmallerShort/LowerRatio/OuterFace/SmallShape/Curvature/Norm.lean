module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Shapes

/-!
# The norm comparison for the reciprocal-shape curvature

The curvature coefficient is a concave quadratic in the norm parameter.
Its slope at `u = 3/4` is negative on the enlarged displacement interval
`1/2 ≤ C ≤ 4/5`, so its maximum occurs at the lower norm.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioCurvature

noncomputable def value (x C u : ℝ) : ℝ := 2 * lrb2 x C u + 5 * lrb3 x C u

noncomputable def normA (x : ℝ) : ℝ := x * (3 * x - 2) / 24
noncomputable def normB (x : ℝ) : ℝ := -x ^ 3 / 12 + x ^ 2 / 3 - x / 8 - 1 / 24
noncomputable def normK (x : ℝ) : ℝ := x * (26 * x + 11) / 96
noncomputable def normH (x : ℝ) : ℝ := x * (x + 1) * (2 * x + 1) / 48

/-- The norm slope at `u = 3/4`, with `e = x - C`. -/
noncomputable def normSlope (x e : ℝ) : ℝ :=
  -normA x * e + normB x - normK x / e + normH x / e ^ 2

theorem norm_difference {x C u : ℝ} (hx : 0 < x) (he : 0 < x - C) :
    value x C u - value x C (3 / 4) =
      (u - 3 / 4) * normSlope x (x - C) - (x + 1) ^ 2 * (u - 3 / 4) ^ 2 / 24 := by
  have hS : x + 1 ≠ 0 := by linarith
  simp only [value, normSlope, normA, normB, normK, normH,
    lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  field_simp
  ring

/-- The positive inverse-square term uses at most three fifths of the inverse term. -/
theorem norm_inverse_pair {x e : ℝ} (hx : 3 / 2 ≤ x) (he : x - 5 / 6 ≤ e) :
    5 * normH x ≤ 3 * normK x * e := by
  have hk : 0 ≤ normK x := by unfold normK; positivity
  have hpair : 0 ≤ x * (2 * x - 3) * (58 * x + 25) / 192 := by
    have : 0 ≤ 2 * x - 3 := by linarith
    positivity
  have hid : 3 * normK x * (x - 5 / 6) - 5 * normH x =
      x * (2 * x - 3) * (58 * x + 25) / 192 := by
    unfold normK normH
    ring
  nlinarith only [hid, hpair, mul_nonneg hk (sub_nonneg.mpr he)]

theorem norm_polynomial_bound {x : ℝ} (hx : 3 / 2 ≤ x) :
    normB x - (2 / 3) * normA x - (4 / 15) * normK x ≤ -7 / 96 := by
  have ht : 0 ≤ x - 3 / 2 := by linarith
  have hid : -(normB x - (2 / 3) * normA x - (4 / 15) * normK x) - 7 / 96 =
      (x - 3 / 2) * (30 * (x - 3 / 2) ^ 2 + 71 * (x - 3 / 2) + 93 / 2) / 360 := by
    unfold normA normB normK
    ring
  have hp : 0 ≤ (x - 3 / 2) *
      (30 * (x - 3 / 2) ^ 2 + 71 * (x - 3 / 2) + 93 / 2) / 360 := by positivity
  linarith only [hid, hp]

theorem norm_slope_bound {x e : ℝ} (hx : 3 / 2 ≤ x)
    (he0 : 2 / 3 ≤ e) (he1 : e ≤ 3 / 2) (he : x - 5 / 6 ≤ e) :
    normSlope x e ≤ -7 / 96 := by
  have hepos : 0 < e := by linarith
  have ha : 0 ≤ normA x := by
    unfold normA
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hk : 0 ≤ normK x := by unfold normK; positivity
  have hp := norm_inverse_pair hx he
  have hi : normH x / e ^ 2 ≤ (3 / 5) * (normK x / e) := by
    apply (div_le_iff₀ (sq_pos_of_pos hepos)).mpr
    have hid : (3 / 5) * (normK x / e) * e ^ 2 = (3 / 5) * normK x * e := by
      field_simp
    rw [hid]
    linarith only [hp]
  have hk' : (2 / 3) * normK x ≤ normK x / e := by
    apply (le_div_iff₀ hepos).mpr
    nlinarith only [mul_nonneg hk (sub_nonneg.mpr he1)]
  have ha' := mul_le_mul_of_nonneg_left he0 ha
  have hb := norm_polynomial_bound hx
  unfold normSlope
  linarith only [hi, hk', ha', hb]

/-- Increasing the norm can only lower the curvature coefficient. -/
theorem le_lower_norm {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 4 / 5) (hu : 3 / 4 ≤ u) :
    value x C u ≤ value x C (3 / 4) := by
  have hs := norm_slope_bound (e := x - C) hx (by linarith) (by linarith) (by linarith)
  have hd := norm_difference (u := u) (C := C) (by linarith : 0 < x) (by linarith)
  have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
    (show normSlope x (x - C) ≤ 0 by linarith)
  have hq : 0 ≤ (x + 1) ^ 2 * (u - 3 / 4) ^ 2 / 24 := by positivity
  linarith only [hd, hp, hq]

end SmoothedOctagon.LowerRatioCurvature
