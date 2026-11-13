module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# The boundary quadratic in the normalized order gap

Complete the square using its determinant. Near the first endpoint the
mixed coefficient is positive. In the middle the determinant is concave,
and near the other endpoint a cubic square bounds its Taylor polynomial.
The higher Taylor terms have nonnegative coefficients in both coordinates.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The constant coefficient minorant at the one-third boundary. -/
def nlrQA {R : Type*} [CommRing R] (z : R) : R :=
  168 + 2193 * z - 3560 * z ^ (2 : ℕ) - 290 * z ^ (3 : ℕ) + 1199 * z ^ (4 : ℕ) + 478 * z ^ (5 : ℕ) + 65 * z ^ (6 : ℕ)

/-- The mixed coefficient minorant at the same boundary. -/
def nlrQB {R : Type*} [CommRing R] (z : R) : R :=
  659 + 2836 * z - 17362 * z ^ (2 : ℕ) + 3591 * z ^ (3 : ℕ) + 8445 * z ^ (4 : ℕ) + 2621 * z ^ (5 : ℕ) + 280 * z ^ (6 : ℕ)

/-- The positive quadratic coefficient minorant. -/
def nlrQC {R : Type*} [CommRing R] (z : R) : R :=
  2122 + 1908 * z - 18349 * z ^ (2 : ℕ) + 19558 * z ^ (3 : ℕ) + 19424 * z ^ (4 : ℕ) + 5058 * z ^ (5 : ℕ) + 461 * z ^ (6 : ℕ)

private def nlrGram {R : Type*} [CommRing R] (z : R) : R :=
  4 * (nlrQA z - 4) * nlrQC z - nlrQB z ^ 2

private noncomputable def gramPoly : Polynomial ℝ := nlrGram Polynomial.X

private theorem gram_eval (z : ℝ) : gramPoly.eval z = nlrGram z := by
  simp [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC]

private theorem diagonal_left {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) : 20 < nlrQA z := by
  let v := 1 - z
  have hv : 0 ≤ v := sub_nonneg.mpr hz1
  have he : nlrQA z = 170 * z * (4 * z - 3) ^ 2 + 83 * (z ^ 3 + v ^ 3)
      + 1167 * z * v ^ 2 + 85 * v ^ 3 + z ^ 2 * v ^ 2 * (2350 + 608 * z + 65 * z ^ 2) := by
    dsimp [v, nlrQA]
    ring
  have hs : 1 / 4 ≤ z ^ 3 + v ^ 3 := by
    dsimp [v]
    nlinarith only [sq_nonneg (z - 1 / 2)]
  have hp : 0 ≤ 170 * z * (4 * z - 3) ^ 2 + 1167 * z * v ^ 2
      + 85 * v ^ 3 + z ^ 2 * v ^ 2 * (2350 + 608 * z + 65 * z ^ 2) := by positivity
  linarith only [he, hs, hp]

private theorem diagonal_right {z : ℝ} (hz : 0 ≤ z) : 0 < nlrQC z := by
  have he : nlrQC z = 1000 + 1122 * (1 - 4 * z ^ 2) ^ 2 + 1900 * z * (1 - 3 * z) ^ 2
      + 8 * z + 2027 * z ^ 2 + 2458 * z ^ 3 + 1472 * z ^ 4 + 5058 * z ^ 5 + 461 * z ^ 6 := by
    unfold nlrQC
    ring
  rw [he]
  positivity

private theorem mixed_left {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1 / 4) : 250 ≤ nlrQB z := by
  have hs : z ^ 2 ≤ z / 4 := by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have hp : 0 ≤ nlrQB z - (650 + 2800 * z - 17600 * z ^ 2) := by
    unfold nlrQB
    ring_nf
    positivity
  nlinarith only [hp, hs, hz1]

private theorem gram_third_nonneg {z : ℝ} (hz : 1 / 4 ≤ z) (hz1 : z ≤ 1 / 2) :
    0 ≤ gramPoly.derivative.derivative.derivative.eval z := by
  obtain ⟨u, rfl⟩ : ∃ u, z = u + 1 / 4 := ⟨z - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [hz]
  have hu1 : u ≤ 1 / 4 := by linarith only [hz1]
  have hs : u ^ 2 ≤ u / 4 := by nlinarith only [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have htail : 0 ≤ gramPoly.derivative.derivative.derivative.eval (u + 1 / 4)
      - gramPoly.derivative.derivative.derivative.eval (1 / 4)
      - gramPoly.derivative.derivative.derivative.derivative.eval (1 / 4) * u
      - gramPoly.derivative.derivative.derivative.derivative.derivative.eval (1 / 4) / 2 * u ^ 2 := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring_nf
    positivity
  have h0 : 0 < gramPoly.derivative.derivative.derivative.eval (1 / 4) := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have h1 : (1536000000 : ℝ) ≤ gramPoly.derivative.derivative.derivative.derivative.eval (1 / 4) := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have h2 : (-4320000000 : ℝ) ≤
      gramPoly.derivative.derivative.derivative.derivative.derivative.eval (1 / 4) / 2 := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have hm1 := mul_le_mul_of_nonneg_right h1 hu
  have hm2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg u)
  nlinarith only [htail, h0, hm1, hm2, hs, hu]

private theorem gram_middle_pos {z : ℝ} (hz : 1 / 4 ≤ z) (hz1 : z ≤ 1 / 2) :
    0 < nlrGram z := by
  have hconc : ∀ s, 1 / 4 ≤ s → s ≤ 1 / 2 → gramPoly.derivative.derivative.eval s ≤ 0 := by
    intro s hs hs1
    have hm := UnitShape.polynomial_mono (p := gramPoly.derivative.derivative) hs1
      (fun r hsr hr1 => gram_third_nonneg (hs.trans hsr) hr1)
    have he : gramPoly.derivative.derivative.eval (1 / 2) ≤ 0 := by
      norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
    exact hm.trans he
  have hfloor := UnitShape.polynomial_floor (p := gramPoly) (m := 1) hz hz1 hconc
    (by norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC])
    (by norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC])
  rw [gram_eval] at hfloor
  linarith only [hfloor]

private theorem gram_right_pos {z : ℝ} (hz : 1 / 2 ≤ z) (hz1 : z ≤ 1) : 0 < nlrGram z := by
  obtain ⟨u, rfl⟩ : ∃ u, z = u + 1 / 2 := ⟨z - 1 / 2, by ring⟩
  have hu : 0 ≤ u := by linarith only [hz]
  have hu1 : u ≤ 1 / 2 := by linarith only [hz1]
  have htail : 0 ≤ gramPoly.eval (u + 1 / 2) - gramPoly.eval (1 / 2)
      - gramPoly.derivative.eval (1 / 2) * u - gramPoly.derivative.derivative.eval (1 / 2) / 2 * u ^ 2
      - gramPoly.derivative.derivative.derivative.eval (1 / 2) / 6 * u ^ 3 := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring_nf
    apply sub_nonneg.mp
    ring_nf
    positivity
  have h0 : (2000000 : ℝ) < gramPoly.eval (1 / 2) := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC]
  have h1 : (-8000000 : ℝ) ≤ gramPoly.derivative.eval (1 / 2) := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have h2 : (-2000000 : ℝ) ≤ gramPoly.derivative.derivative.eval (1 / 2) / 2 := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have h3 : (64000000 : ℝ) ≤ gramPoly.derivative.derivative.derivative.eval (1 / 2) / 6 := by
    norm_num [gramPoly, nlrGram, nlrQA, nlrQB, nlrQC, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have hm1 := mul_le_mul_of_nonneg_right h1 hu
  have hm2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg u)
  have hm3 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hu 3)
  have hP : 0 ≤ 2 - 8 * u - 2 * u ^ 2 + 64 * u ^ 3 := by
    have he : 2 - 8 * u - 2 * u ^ 2 + 64 * u ^ 3 =
        64 * (u - 1 / 4) ^ 2 * (u + 1 / 2) + 2 * u * (2 - u) := by ring
    rw [he]
    have : 0 ≤ 2 - u := by linarith only [hu1]
    positivity
  rw [gram_eval] at htail
  nlinarith only [htail, h0, hm1, hm2, hm3, hP]

/-- The boundary quadratic is positive by its diagonals and determinant. -/
theorem nlr_Q_ge {z β : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hb : 0 ≤ β) :
    4 ≤ nlrQA z + β * nlrQB z + β ^ 2 * nlrQC z ∧ 0 ≤ nlrQC z := by
  have hC := diagonal_right hz0
  refine ⟨?_, hC.le⟩
  by_cases hzq : z ≤ 1 / 4
  · have hA := diagonal_left hz0 hz1
    have hB := mul_nonneg hb (show 0 ≤ nlrQB z by linarith only [mixed_left hz0 hzq])
    have hlast := mul_nonneg (sq_nonneg β) hC.le
    linarith only [hA, hB, hlast]
  · have hG : 0 < nlrGram z := by
      by_cases hzh : z ≤ 1 / 2
      · exact gram_middle_pos (le_of_not_ge hzq) hzh
      · exact gram_right_pos (le_of_not_ge hzh) hz1
    have he : 4 * nlrQC z * (nlrQA z + β * nlrQB z + β ^ 2 * nlrQC z - 4) =
        (2 * nlrQC z * β + nlrQB z) ^ 2 + nlrGram z := by
      unfold nlrGram
      ring
    have hp : 0 < 4 * nlrQC z * (nlrQA z + β * nlrQB z + β ^ 2 * nlrQC z - 4) := by
      nlinarith only [he, hG, sq_nonneg (2 * nlrQC z * β + nlrQB z)]
    have hpos := pos_of_mul_pos_right hp (show 0 ≤ 4 * nlrQC z by positivity)
    linarith only [hpos]

end SmoothedOctagon
