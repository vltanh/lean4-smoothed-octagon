module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Polynomial

/-!
# The incoming coefficients from the two geometric slacks

Put `δ = 1/4-t` and `σ = 3+x-x²-t(x²+6x+6)`.
The first two coefficients are sums of positive terms and positive
multiples of these slacks. Their quadratic remainders are nonnegative.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

private def incomingBase0 {R : Type*} [CommRing R] (x : R) : R :=
  2 * x ^ 4 - 6 * x ^ 3 + 23 * x ^ 2 + 34 * x - 18

private def incomingBase1 {R : Type*} [CommRing R] (x : R) : R :=
  8 * x ^ 6 + 86 * x ^ 5 - 169 * x ^ 4 - 69 * x ^ 3 + 274 * x ^ 2 - 126 * x + 12

private def incomingSlope1 {R : Type*} [CommRing R] (x : R) : R :=
  -16 * x ^ 6 - 16 * x ^ 5 + 37 * x ^ 4 + 381 * x ^ 3 + 362 * x ^ 2 - 90 * x + 12

private def incomingRem1 {R : Type*} [CommRing R] (t x : R) : R :=
  -6 * t * x ^ 4 - 38 * t * x ^ 3 - 44 * t * x ^ 2 + 12 * t * x + 24 * t
    + 4 * x ^ 6 + 37 * x ^ 5 + 106 * x ^ 4 + 172 * x ^ 3 + 130 * x ^ 2 + 12 * x - 12

private theorem incomingBase0_pos {x : ℝ} (hx : 1 / 2 ≤ x) (hx3 : x ≤ 3) :
    0 < incomingBase0 x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have h3 := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx3)
  unfold incomingBase0
  nlinarith only [h3, hx, pow_nonneg hx0 4]

private theorem incomingBase1_pos {x : ℝ} (hx : 1 / 2 ≤ x) : 0 < incomingBase1 x := by
  by_cases hx1 : x ≤ 1
  · let z := 2 * x - 1
    have hz : 0 ≤ z := by dsimp [z]; linarith only [hx]
    have hz1 : 0 ≤ 1 - z := by dsimp [z]; linarith only [hx1]
    have he : 16 * incomingBase1 x = 18 + 105 * z + 8 * z * (1 - z) * (27 + 43 * z)
        + 76 * z ^ 4 + 55 * z ^ 5 + 2 * z ^ 6 := by
      dsimp [z, incomingBase1]
      ring
    have hp : 0 < 18 + 105 * z + 8 * z * (1 - z) * (27 + 43 * z)
        + 76 * z ^ 4 + 55 * z ^ 5 + 2 * z ^ 6 := by positivity
    linarith only [he, hp]
  · let z := x - 1
    have hz : 0 ≤ z := by dsimp [z]; linarith only [hx1]
    have he : incomingBase1 x = 16 + 17 * z + 33 * z ^ 2 + 275 * z ^ 3
        + 381 * z ^ 4 + 134 * z ^ 5 + 8 * z ^ 6 := by
      dsimp [z, incomingBase1]
      ring
    rw [he]
    positivity

private theorem incomingSlope1_nonneg {x : ℝ} (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3) :
    0 ≤ incomingSlope1 x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have h2 : x ^ 2 ≤ 6 := by nlinarith only [hx, hx7]
  have h3 : x ^ 3 ≤ 13 := by
    have hp := pow_le_pow_left₀ hx0 hx7 3
    norm_num at hp
    linarith only [hp]
  have h5 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hx0 3)
  have h6 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hx0 3)
  have h2lo : x / 2 ≤ x ^ 2 := by nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  unfold incomingSlope1
  nlinarith only [h5, h6, h2lo, hx0, pow_nonneg hx0 3, pow_nonneg hx0 4]

private theorem incomingRem1_nonneg {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) : 0 ≤ incomingRem1 t x := by
  let h := 1 - 4 * t
  let z := 2 * x - 1
  have hh : 0 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 := by dsimp [h]; linarith only [ht]
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hx]
  have hc : 0 ≤ 1898 - 111 * h := by linarith only [hh1]
  have he : 32 * incomingRem1 t x = (1898 - 111 * h)
      + (254 * h + 5127) * z + (220 * h + 4556) * z ^ 2
      + (50 * h + 1896) * z ^ 3 + (3 * h + 424) * z ^ 4 + 49 * z ^ 5 + 2 * z ^ 6 := by
    dsimp [h, z, incomingRem1]
    ring
  have hp : 0 ≤ (1898 - 111 * h)
      + (254 * h + 5127) * z + (220 * h + 4556) * z ^ 2
      + (50 * h + 1896) * z ^ 3 + (3 * h + 424) * z ^ 4 + 49 * z ^ 5 + 2 * z ^ 6 := by positivity
  linarith only [he, hp]

/-- The positive constant coefficient follows from the endpoint and scale slacks. -/
theorem incoming0_pos {t x : ℝ} (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) : 0 < incoming0 t x := by
  let δ := 1 / 4 - t
  let σ := 3 + x - x ^ 2 - t * (x ^ 2 + 6 * x + 6)
  have hδ : 0 ≤ δ := sub_nonneg.mpr ht1
  have hσ : 0 ≤ σ := sub_nonneg.mpr hT
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hL : 0 ≤ 2 * x ^ 2 + 2 * x - 1 := by nlinarith only [hx, sq_nonneg x]
  have hbase := incomingBase0_pos hx (show x ≤ 3 by linarith only [hx7])
  have he : incoming0 t x = incomingBase0 x / 32 + (2 * x ^ 2 + 2 * x - 1) * σ / 8
      + (6 * x ^ 4 + 2 * x ^ 3 + 9 * x ^ 2 + 26 * x + 6) * δ / 8
      + 2 * (x ^ 3 + 7 * x ^ 2 + 12 * x + 6) * δ ^ 2 := by
    dsimp [δ, σ, incoming0, incomingBase0]
    ring
  rw [he]
  positivity

/-- The linear coefficient is a positive remainder plus the same two geometric slacks. -/
theorem incoming1_pos {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) : 0 < incoming1 t x := by
  let δ := 1 / 4 - t
  let σ := 3 + x - x ^ 2 - t * (x ^ 2 + 6 * x + 6)
  have hδ : 0 ≤ δ := sub_nonneg.mpr ht1
  have hσ : 0 ≤ σ := sub_nonneg.mpr hT
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hbase := incomingBase1_pos hx
  have hslope := incomingSlope1_nonneg hx hx7
  have hrem := incomingRem1_nonneg ht ht1 hx
  have he : incoming1 t x = incomingBase1 x / 32 + incomingSlope1 x * δ / 8
      + 9 / 2 * x ^ 3 * σ + δ ^ 2 * incomingRem1 t x := by
    dsimp [δ, σ, incoming1, incomingBase1, incomingSlope1, incomingRem1]
    ring
  rw [he]
  positivity

end SmoothedOctagon.LowScale
