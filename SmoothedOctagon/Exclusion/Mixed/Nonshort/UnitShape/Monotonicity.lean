module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Coordinates
public import Mathlib.Tactic.GCongr

/-!
# Moving the order gap to its lower boundary

The value at one and the cross term increase with the order gap `r`.
The switching bound absorbs a possible negative cubic coefficient in
the value. For the cross term, the order bound gives `(1+x)r ≤ 1`.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

theorem constant_mono {x u v : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (huv : u ≤ v) :
    constant x u ≤ constant x v := by
  unfold constant
  gcongr

theorem value_mono {x u v : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ x * (1 + x)) : value x u ≤ value x v := by
  have h2 : 0 ≤ value2 x := by unfold value2; positivity
  have h23 : 0 ≤ 2 * value2 x + 3 * (x * (1 + x)) * value3 x := by
    have e : 2 * value2 x + 3 * (x * (1 + x)) * value3 x =
        9 * x ^ 6 + 84 * x ^ 5 + 246 * x ^ 4 + 261 * x ^ 3
        + 46 * x ^ 2 + 24 * (1 - x) := by unfold value2 value3; ring
    rw [e]
    have : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    positivity
  have h1 : 0 ≤ value1 x := by unfold value1; positivity
  have h23' : 0 ≤ 2 * ((1 + x) ^ 2 * value2 x)
      + 3 * (x * (1 + x)) * ((1 + x) ^ 2 * value3 x) := by
    nlinarith only [mul_nonneg (sq_nonneg (1 + x)) h23]
  have hi := cubic_increasing (a := (1 + x) * value0 x) h1
    (mul_nonneg (sq_nonneg (1 + x)) h2) h23' hu huv hv
  exact mul_le_mul_of_nonneg_left hi (by positivity)

private theorem cross_coeff_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    72 ≤ cross1 x ∧ 72 ≤ cross2 x ∧ -12 ≤ cross3 x := by
  have h93 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 9)
  have h83 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 8)
  have h73 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 7)
  have h63 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 6)
  have h53 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 5)
  have h43 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 4)
  constructor
  · have hp : 0 ≤ 124 * x ^ 5 + 539 * x ^ 4 + 1158 * x ^ 2 + 600 * x := by positivity
    unfold cross1
    linarith only [h93, h83, h73, h63, hp, pow_nonneg hx 3]
  constructor
  · have hp : 0 ≤ 85 * x ^ 6 + 498 * x ^ 5 + 894 * x ^ 4 + 1104 * x ^ 2 + 528 * x := by positivity
    unfold cross2
    linarith only [h93, h83, h73, hp, pow_nonneg hx 3]
  · have hp : 0 ≤ 81 * x ^ 2 + 42 * x := by positivity
    unfold cross3
    linarith only [h53, h43, hp, pow_nonneg hx 3]

theorem cross_mono {x u v : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 - x) : cross x u ≤ cross x v := by
  obtain ⟨h1, h2, h3⟩ := cross_coeff_bounds hx hx1
  have hv0 : 0 ≤ v := hu.trans huv
  have hW : 0 ≤ 1 + x := by positivity
  have huW : 0 ≤ (1 + x) * u := by positivity
  have hvW : 0 ≤ (1 + x) * v := by positivity
  have hvW1 : (1 + x) * v ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hv hW
    nlinarith only [this, sq_nonneg x]
  have huW1 : (1 + x) * u ≤ 1 :=
    (mul_le_mul_of_nonneg_left huv hW).trans hvW1
  have hsq1 : ((1 + x) * u) ^ 2 ≤ 1 := by nlinarith only [huW, huW1]
  have hsq2 : ((1 + x) * v) ^ 2 ≤ 1 := by nlinarith only [hvW, hvW1]
  have hmix : ((1 + x) * u) * ((1 + x) * v) ≤ 1 :=
    (mul_le_mul huW1 hvW1 hvW (by norm_num)).trans_eq (by norm_num)
  have htail : (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) ≤ 3 := by
    nlinarith only [hsq1, hsq2, hmix]
  have htail' := mul_le_mul_of_nonneg_left htail hx
  have h1' := mul_le_mul_of_nonneg_left h1 hW
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ u + v by positivity)
  have h3' := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) by positivity)
  have hpositive : 0 ≤ (1 + x) * cross1 x + (u + v) * cross2 x
      + x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) * cross3 x := by
    nlinarith only [h1', h2', h3', htail', hx, hu, hv0]
  have heq : cross x v - cross x u = (v - u) *
      ((1 + x) * cross1 x + (u + v) * cross2 x
        + x * (1 + x) ^ 2 * (u ^ 2 + u * v + v ^ 2) * cross3 x) := by
    unfold cross
    ring
  have hp := mul_nonneg (sub_nonneg.mpr huv) hpositive
  linarith only [heq, hp]

end SmoothedOctagon.UnitShape
