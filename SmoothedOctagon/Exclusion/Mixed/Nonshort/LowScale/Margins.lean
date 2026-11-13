module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Polynomial

/-!
# Supporting lines for the two quartic margins

Both margins lie above their tangent line at `t=1/4`.
In the coordinates `h=1-4t` and `z=2x-1`, their quadratic
remainders have nonnegative coefficients. The slopes point
into the feasible region.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

def quadraticMargin {R : Type*} [CommRing R] (t x : R) : R :=
  unit2 t x + 54 * unit0 t x

def cubicMargin {R : Type*} [CommRing R] (t x : R) : R :=
  unit3 t x + 4 * unit2 t x

def quadraticSlope {R : Type*} [CommRing R] (z : R) : R :=
  -21 * z ^ 7 + 1259 * z ^ 6 + 16439 * z ^ 5 + 172227 * z ^ 4
    + 767969 * z ^ 3 + 1307705 * z ^ 2 + 930525 * z + 231417

def cubicSlope {R : Type*} [CommRing R] (z : R) : R :=
  -20 * z ^ 8 - 675 * z ^ 7 - 5533 * z ^ 6 - 4059 * z ^ 5 + 134647 * z ^ 4
    + 577447 * z ^ 3 + 835953 * z ^ 2 + 471735 * z + 65961

private def quadraticRemainder {R : Type*} [CommRing R] (h z : R) : R :=
  (34299 * h ^ 2 + 240219 * h + 423861)
    + (95007 * h ^ 2 + 661863 * h + 1310249) * z
    + (91794 * h ^ 2 + 660739 * h + 1479827) * z ^ 2
    + (36954 * h ^ 2 + 292011 * h + 763411) * z ^ 3
    + (6195 * h ^ 2 + 61737 * h + 193211) * z ^ 4
    + (327 * h ^ 2 + 7045 * h + 27983) * z ^ 5
    + (537 * h + 2461) * z ^ 6 + (9 * h + 21) * z ^ 7

private def cubicRemainder {R : Type*} [CommRing R] (h z : R) : R :=
  (-7326 * h ^ 2 + 25167 * h + 28575)
    + (-11208 * h ^ 2 + 51141 * h + 334701) * z
    + (-4056 * h ^ 2 + 85739 * h + 695831) * z ^ 2
    + (-36 * h ^ 2 + 76069 * h + 592925) * z ^ 3
    + (150 * h ^ 2 + 33621 * h + 237573) * z ^ 4
    + (12 * h ^ 2 + 7823 * h + 47455) * z ^ 5
    + (913 * h + 4389) * z ^ 6 + (39 * h + 119) * z ^ 7

/-- Charge a higher power against an earlier one using the interval's upper endpoint. -/
theorem power_tail_le {z B : ℝ} (hz : 0 ≤ z) (hB : z ≤ B) (m n : ℕ) :
    z ^ (m + n) ≤ z ^ m * B ^ n := by
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hB n) (pow_nonneg hz m)

theorem quadraticSlope_nonneg {z : ℝ} (hz : 0 ≤ z) (hz4 : z ≤ 4) :
    0 ≤ quadraticSlope z := by
  have hc : 0 ≤ 1259 - 21 * z := by linarith only [hz4]
  have he : quadraticSlope z = (1259 - 21 * z) * z ^ 6 + 16439 * z ^ 5
      + 172227 * z ^ 4 + 767969 * z ^ 3 + 1307705 * z ^ 2 + 930525 * z + 231417 := by
    unfold quadraticSlope
    ring
  rw [he]
  positivity

theorem cubicSlope_nonneg {z : ℝ} (hz : 0 ≤ z) (hz4 : z ≤ 11 / 3) :
    0 ≤ cubicSlope z := by
  have h5 := power_tail_le hz hz4 4 1
  have h6 := power_tail_le hz hz4 4 2
  have h7 := power_tail_le hz hz4 4 3
  have h8 := power_tail_le hz hz4 4 4
  norm_num at h5 h6 h7 h8
  unfold cubicSlope
  nlinarith only [h5, h6, h7, h8, pow_nonneg hz 4, pow_nonneg hz 3, sq_nonneg z, hz]

private theorem quadraticRemainder_nonneg {h z : ℝ} (hh : 0 ≤ h) (hz : 0 ≤ z) :
    0 ≤ quadraticRemainder h z := by
  unfold quadraticRemainder
  positivity

private theorem cubicRemainder_nonneg {h z : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hz : 0 ≤ z) :
    0 ≤ cubicRemainder h z := by
  have hsq : h ^ 2 ≤ h := by nlinarith only [mul_nonneg hh (sub_nonneg.mpr hh1)]
  have h0 : 0 ≤ -7326 * h ^ 2 + 25167 * h + 28575 := by nlinarith only [hsq, hh]
  have h1 : 0 ≤ -11208 * h ^ 2 + 51141 * h + 334701 := by nlinarith only [hsq, hh]
  have h2 : 0 ≤ -4056 * h ^ 2 + 85739 * h + 695831 := by nlinarith only [hsq, hh]
  have h3 : 0 ≤ -36 * h ^ 2 + 76069 * h + 592925 := by nlinarith only [hsq, hh]
  unfold cubicRemainder
  positivity

/-- The tangent at the quarter-scale boundary supports the quadratic margin. -/
theorem quadratic_support {t x : ℝ} (ht1 : t ≤ 1 / 4) (hx : 1 / 2 ≤ x) :
    quadraticMargin (1 / 4) x + (1 / 4 - t) * quadraticSlope (2 * x - 1) / 256 ≤
      quadraticMargin t x := by
  have hh : 0 ≤ 1 - 4 * t := by linarith only [ht1]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hr := quadraticRemainder_nonneg hh hz
  have he : quadraticMargin t x = quadraticMargin (1 / 4) x
      + (1 / 4 - t) * quadraticSlope (2 * x - 1) / 256
      + (1 / 4 - t) ^ 2 * quadraticRemainder (1 - 4 * t) (2 * x - 1) / 64 := by
    unfold quadraticMargin unit2 unit0 incoming0 quadraticSlope quadraticRemainder
    ring
  rw [he]
  have hp := mul_nonneg (sq_nonneg (1 / 4 - t)) hr
  linarith only [hp]

/-- The same supporting-line argument applies to the cubic margin. -/
theorem cubic_support {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) (hx : 1 / 2 ≤ x) :
    cubicMargin (1 / 4) x + (1 / 4 - t) * cubicSlope (2 * x - 1) / 256 ≤ cubicMargin t x := by
  have hh : 0 ≤ 1 - 4 * t := by linarith only [ht1]
  have hh1 : 1 - 4 * t ≤ 1 := by linarith only [ht]
  have hz : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have hr := cubicRemainder_nonneg hh hh1 hz
  have he : cubicMargin t x = cubicMargin (1 / 4) x
      + (1 / 4 - t) * cubicSlope (2 * x - 1) / 256
      + (1 / 4 - t) ^ 2 * cubicRemainder (1 - 4 * t) (2 * x - 1) / 64 := by
    unfold cubicMargin unit3 unit2 cubicSlope cubicRemainder
    ring
  rw [he]
  have hp := mul_nonneg (sq_nonneg (1 / 4 - t)) hr
  linarith only [hp]

end SmoothedOctagon.LowScale
