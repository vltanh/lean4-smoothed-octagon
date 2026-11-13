module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Margins

/-!
# The two boundary estimates for the quartic margins

For `x≤1`, the quarter-scale boundary is positive directly.
For `x≥1`, evaluate the same supporting line at the norm boundary
`t=(3+x-x²)/(x²+6x+6)`. Elementary comparisons of powers give
positivity there. The feasible region lies above these supports.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

private def quadraticNormBoundary {R : Type*} [CommRing R] (x : R) : R :=
  -456 * x ^ 9 + 5672 * x ^ 8 - 19485 * x ^ 7 + 134298 * x ^ 6 + 403631 * x ^ 5
    + 61620 * x ^ 4 - 258996 * x ^ 3 - 40752 * x ^ 2 - 900 * x + 864

private def cubicNormBoundary {R : Type*} [CommRing R] (x : R) : R :=
  -640 * x ^ 10 - 8232 * x ^ 9 - 10728 * x ^ 8 + 66548 * x ^ 7 + 224929 * x ^ 6
    + 153453 * x ^ 5 - 150756 * x ^ 4 - 134888 * x ^ 3 + 27492 * x ^ 2 + 4884 * x + 4752

private theorem quadratic_quarter_pos {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < quadraticMargin (1 / 4) x := by
  let z := 2 * x - 1
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hx]
  have hz1 : z ≤ 1 := by dsimp [z]; linarith only [hx1]
  have h4 := power_tail_le hz hz1 2 2
  have h5 := power_tail_le hz hz1 2 3
  have h6 := power_tail_le hz hz1 2 4
  have h7 := power_tail_le hz hz1 2 5
  norm_num at h4 h5 h6 h7
  have he : 1024 * quadraticMargin (1 / 4) x = -9 * z ^ 7 - 4065 * z ^ 6
      - 43794 * z ^ 5 - 106842 * z ^ 4 + 73095 * z ^ 3 + 319839 * z ^ 2
      + 189108 * z + 11772 := by
    dsimp [z, quadraticMargin, unit2, unit0, incoming0]
    ring
  nlinarith only [he, h4, h5, h6, h7, pow_nonneg hz 3, sq_nonneg z, hz]

private theorem cubic_quarter_pos {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < cubicMargin (1 / 4) x := by
  let z := 2 * x - 1
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hx]
  have hz1 : z ≤ 1 := by dsimp [z]; linarith only [hx1]
  have h4 := power_tail_le hz hz1 3 1
  have h5 := power_tail_le hz hz1 3 2
  norm_num at h4 h5
  have he : 1024 * cubicMargin (1 / 4) x = 20 * z ^ 8 + 517 * z ^ 7
      + 1351 * z ^ 6 - 10463 * z ^ 5 - 27079 * z ^ 4 + 63675 * z ^ 3
      + 154629 * z ^ 2 + 78111 * z + 14823 := by
    dsimp [z, cubicMargin, unit3, unit2]
    ring
  nlinarith only [he, h4, h5, pow_nonneg hz 8, pow_nonneg hz 7,
    pow_nonneg hz 6, pow_nonneg hz 3, sq_nonneg z, hz]

private theorem quadratic_norm_pos {x : ℝ} (hx : 1 ≤ x) (hx3 : x ≤ 3) :
    0 < quadraticNormBoundary x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hA : 0 ≤ (5672 - 456 * x) * x ^ 8 := by
    have : 0 ≤ 5672 - 456 * x := by linarith only [hx3]
    positivity
  have hB : 0 ≤ (134298 - 19485 * x) * x ^ 6 := by
    have : 0 ≤ 134298 - 19485 * x := by linarith only [hx3]
    positivity
  have h35 : x ^ 3 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
  have h25 : x ^ 2 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
  have h15 : x ≤ x ^ 5 := by simpa using (pow_le_pow_right₀ hx (show 1 ≤ 5 by decide))
  unfold quadraticNormBoundary
  nlinarith only [hA, hB, h35, h25, h15, pow_nonneg hx0 5, pow_nonneg hx0 4]

private theorem cubic_norm_pos {x : ℝ} (hx : 1 ≤ x) (hx5 : x ≤ 5 / 2) :
    0 < cubicNormBoundary x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have h2 := pow_le_pow_left₀ hx0 hx5 2
  have h3 := pow_le_pow_left₀ hx0 hx5 3
  norm_num at h2 h3
  have hH : -24000 ≤ 66548 - 10728 * x - 8232 * x ^ 2 - 640 * x ^ 3 := by
    nlinarith only [hx5, h2, h3]
  have hH' := mul_le_mul_of_nonneg_right hH (pow_nonneg hx0 7)
  have h76 := power_tail_le hx0 hx5 6 1
  norm_num at h76
  have h65 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
  have h45 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
  have h35 : x ^ 3 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
  unfold cubicNormBoundary
  nlinarith only [hH', h76, h65, h45, h35, pow_nonneg hx0 5, sq_nonneg x, hx0]

/-- The quadratic margin is positive throughout the feasible unit face. -/
theorem quadraticMargin_pos {t x : ℝ} (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) : 0 < quadraticMargin t x := by
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hs := quadraticSlope_nonneg hz (show 2 * x - 1 ≤ 4 by linarith only [hx7])
  have hd : 0 ≤ 1 / 4 - t := sub_nonneg.mpr ht1
  have hsupp := quadratic_support ht1 hx
  by_cases hx1 : x ≤ 1
  · have hb := quadratic_quarter_pos hx hx1
    have hp := mul_nonneg hd hs
    linarith only [hb, hp, hsupp]
  · have hb := quadratic_norm_pos (show 1 ≤ x by linarith only [hx1])
      (show x ≤ 3 by linarith only [hx7])
    have hslack := mul_nonneg (sub_nonneg.mpr hT) hs
    have he : 32 * (x ^ 2 + 6 * x + 6) *
        (quadraticMargin (1 / 4) x + (1 / 4 - t) * quadraticSlope (2 * x - 1) / 256) =
        quadraticNormBoundary x +
          (3 + x - x ^ 2 - t * (x ^ 2 + 6 * x + 6)) * quadraticSlope (2 * x - 1) / 8 := by
      unfold quadraticMargin unit2 unit0 incoming0 quadraticSlope quadraticNormBoundary
      ring
    have hp : 0 < 32 * (x ^ 2 + 6 * x + 6) *
        (quadraticMargin (1 / 4) x + (1 / 4 - t) * quadraticSlope (2 * x - 1) / 256) := by
      linarith only [he, hb, hslack]
    have hx0 : 0 ≤ x := by linarith only [hx]
    exact (pos_of_mul_pos_right hp (by positivity)).trans_le hsupp

/-- The cubic margin has the same supporting boundaries. -/
theorem cubicMargin_pos {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) : 0 < cubicMargin t x := by
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hs := cubicSlope_nonneg hz (show 2 * x - 1 ≤ 11 / 3 by linarith only [hx7])
  have hd : 0 ≤ 1 / 4 - t := sub_nonneg.mpr ht1
  have hsupp := cubic_support ht ht1 hx
  by_cases hx1 : x ≤ 1
  · have hb := cubic_quarter_pos hx hx1
    have hp := mul_nonneg hd hs
    linarith only [hb, hp, hsupp]
  · have hb := cubic_norm_pos (show 1 ≤ x by linarith only [hx1])
      (show x ≤ 5 / 2 by linarith only [hx7])
    have hslack := mul_nonneg (sub_nonneg.mpr hT) hs
    have he : 32 * (x ^ 2 + 6 * x + 6) *
        (cubicMargin (1 / 4) x + (1 / 4 - t) * cubicSlope (2 * x - 1) / 256) =
        cubicNormBoundary x +
          (3 + x - x ^ 2 - t * (x ^ 2 + 6 * x + 6)) * cubicSlope (2 * x - 1) / 8 := by
      unfold cubicMargin unit3 unit2 cubicSlope cubicNormBoundary
      ring
    have hp : 0 < 32 * (x ^ 2 + 6 * x + 6) *
        (cubicMargin (1 / 4) x + (1 / 4 - t) * cubicSlope (2 * x - 1) / 256) := by
      linarith only [he, hb, hslack]
    have hx0 : 0 ≤ x := by linarith only [hx]
    exact (pos_of_mul_pos_right hp (by positivity)).trans_le hsupp

end SmoothedOctagon.LowScale
