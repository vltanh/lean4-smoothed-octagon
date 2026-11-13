module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace SmoothedOctagon.UnitShape

/-- The quadratic and cubic terms have increasing sum if the quadratic
coefficient absorbs the possible negative cubic coefficient at the endpoint. -/
theorem cubic_increasing {a b c d R u v : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcd : 0 ≤ 2 * c + 3 * R * d) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ R) :
    a + b * u + c * u ^ 2 + d * u ^ 3 ≤ a + b * v + c * v ^ 2 + d * v ^ 3 := by
  have hv0 : 0 ≤ v := hu.trans huv
  have hR : 0 ≤ R := hv0.trans hv
  have huR : u ≤ R := huv.trans hv
  have hsum : 0 ≤ u + v := by positivity
  have hquad : 0 ≤ u ^ 2 + u * v + v ^ 2 := by positivity
  have hslope : 0 ≤ b + c * (u + v) + d * (u ^ 2 + u * v + v ^ 2) := by
    by_cases hd : 0 ≤ d
    · positivity
    have hd : d ≤ 0 := le_of_not_ge hd
    have hu2 := mul_le_mul_of_nonneg_left huR hu
    have hv2 := mul_le_mul_of_nonneg_left hv hv0
    have huv1 := mul_le_mul_of_nonneg_left hv hu
    have huv2 := mul_le_mul_of_nonneg_left huR hv0
    have hcap : 2 * (u ^ 2 + u * v + v ^ 2) ≤ 3 * R * (u + v) := by
      nlinarith only [hu2, hv2, huv1, huv2]
    have hcap' := mul_le_mul_of_nonpos_left hcap hd
    have hrest := mul_nonneg hcd hsum
    nlinarith only [hcap', hrest, hb]
  have hprod := mul_nonneg (sub_nonneg.mpr huv) hslope
  nlinarith only [hprod]

/-- A cubic is controlled by its value and slope at one, and by a quadratic
remainder. The small negative cross term is absorbed by completing a square. -/
theorem cubic_boundary_pos {C A B G z : ℝ} (hC : 0 < C) (hG : 0 < G) (hz : 0 ≤ z)
    (hK : 0 < C + 2 * A + 3 * B + 4 * G)
    (hH : 0 ≤ B + 4 * G - C / 9)
    (hS : 0 < 8 * (A + 2 * C - G) + C)
    (hP : 0 < A + 2 * C - G + 32 * (C + A + B + G)) :
    0 < C + A * z + B * z ^ 2 + G * z ^ 3 := by
  let S := A + 2 * C - G
  let P := C + A + B + G
  have hK' : 0 < 3 * P - S := by dsimp [P, S]; linarith only [hK]
  have hS' : 0 < 8 * S + C := hS
  have hP' : 0 < S + 32 * P := hP
  by_cases hSn : S < 0
  · have hgram : 0 < 4 * C * P - S ^ 2 := by
      have h1 := mul_pos hC hP'
      have h2 := mul_neg_of_neg_of_pos hSn hS'
      nlinarith only [h1, h2]
    by_cases hz0 : z = 0
    · subst z; simpa using hC
    have hsq := mul_pos hgram (sq_pos_of_pos (lt_of_le_of_ne hz (Ne.symm hz0)))
    have hrest : 0 ≤ 4 * C * G * z * (1 - z) ^ 2 := by positivity
    have e : 4 * C * (C + A * z + B * z ^ 2 + G * z ^ 3) =
        (2 * C * (1 - z) + S * z) ^ 2 +
        (4 * C * P - S ^ 2) * z ^ 2 + 4 * C * G * z * (1 - z) ^ 2 := by
      dsimp [P, S]; ring
    have hp : 0 < 4 * C * (C + A * z + B * z ^ 2 + G * z ^ 3) := by
      nlinarith only [e, hsq, hrest, sq_nonneg (2 * C * (1 - z) + S * z)]
    exact pos_of_mul_pos_right hp (by positivity)
  have hSn : 0 ≤ S := le_of_not_gt hSn
  have hPv : 0 < P := by linarith only [hK', hSn]
  by_cases hz1 : z ≤ 1
  · have h1 : 0 ≤ (C + G * z) * (1 - z) ^ 2 := by positivity
    have h2 : 0 ≤ S * z * (1 - z) := by positivity
    have e : C + A * z + B * z ^ 2 + G * z ^ 3 =
        (C + G * z) * (1 - z) ^ 2 + S * z * (1 - z) + P * z ^ 2 := by
      dsimp [S, P]; ring
    by_cases hz0 : z = 0
    · subst z; simpa using hC
    have h3 := mul_pos hPv (sq_pos_of_pos (lt_of_le_of_ne hz (Ne.symm hz0)))
    linarith only [e, h1, h2, h3]
  have hz1 : 1 < z := lt_of_not_ge hz1
  by_cases hz2 : z ≤ 3 / 2
  · have h1 : 0 ≤ C * (z - 1) ^ 2 := by positivity
    have hcap : 0 ≤ 3 - 2 * z := by linarith only [hz2]
    have h2 : 0 ≤ z * ((3 - 2 * z) * P) := by positivity
    have h3 : 0 < z * ((z - 1) * (3 * P - S)) := by positivity
    have h4 : 0 ≤ z * (G * (z - 1) ^ 2) := by positivity
    have e : C + A * z + B * z ^ 2 + G * z ^ 3 = C * (z - 1) ^ 2 +
        z * ((3 - 2 * z) * P + (z - 1) * (3 * P - S) + G * (z - 1) ^ 2) := by
      dsimp [S, P]; ring
    linarith only [e, h1, h2, h3, h4]
  have hz2 : 3 / 2 < z := lt_of_not_ge hz2
  have h1 : 0 ≤ C * (z - 3) ^ 2 / 9 := by positivity
  have h2 : 0 < z * ((3 * P - S) / 2) := by positivity
  have h3 : 0 ≤ z * ((z - 3 / 2) * (B + 4 * G - C / 9)) := by positivity
  have h4 : 0 ≤ z * (G * (z - 2) ^ 2) := by positivity
  have e : C + A * z + B * z ^ 2 + G * z ^ 3 = C * (z - 3) ^ 2 / 9 +
      z * ((3 * P - S) / 2 + (z - 3 / 2) * (B + 4 * G - C / 9) + G * (z - 2) ^ 2) := by
    dsimp [S, P]; ring
  linarith only [e, h1, h2, h3, h4]

end SmoothedOctagon.UnitShape
