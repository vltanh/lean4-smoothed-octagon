module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Incoming
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Boundary

/-!
# Positivity on the unit low-scale face

The incoming coefficients follow from the geometric slacks, and the
two margins from their supporting boundaries. The cubic coefficient
is positive by a square completion and absorption of the higher powers
of `t`; the leading coefficient is a product of positive factors.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

private def cubicLinear {R : Type*} [CommRing R] (x : R) : R :=
  10 * x ^ 8 + 88 * x ^ 7 + 178 * x ^ 6 - 54 * x ^ 5 - 332 * x ^ 4
    + 188 * x ^ 3 + 432 * x ^ 2 - 24 * x

private def cubicRemainder {R : Type*} [CommRing R] (t x : R) : R :=
  (44 * x ^ 7 + 450 * x ^ 6 + 1376 * x ^ 5 + 1669 * x ^ 4 + 512 * x ^ 3
    - 121 * x ^ 2 + 186 * x + 30)
    + t * (-12 * x ^ 7 - 80 * x ^ 6 - 76 * x ^ 5 + 298 * x ^ 4
      + 762 * x ^ 3 + 522 * x ^ 2 - 36)
    + t ^ 2 * (-12 * x ^ 4 - 84 * x ^ 3 - 144 * x ^ 2 - 72 * x)

private theorem cubicLinear_nonneg {x : ℝ} (hx : 1 / 2 ≤ x) : 0 ≤ cubicLinear x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have ho : 0 ≤ 2 * x - 1 := by linarith only [hx]
  have he : cubicLinear x = 10 * x ^ 8 + 88 * x ^ 7 + 6 * x ^ 2 * (5 * x ^ 2 - 6) ^ 2
      + 28 * x ^ 4 * (x - 1) ^ 2 + 2 * x ^ 5 + 188 * x ^ 3 + 168 * x ^ 2
      + 24 * x * (2 * x - 1) := by unfold cubicLinear; ring
  rw [he]
  positivity

private theorem cubicRemainder_pos {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) : 0 < cubicRemainder t x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith only [ht, ht1]
  have hA : 0 ≤ 12 * x ^ 7 + 80 * x ^ 6 + 76 * x ^ 5 + 36 := by positivity
  have hB : 0 ≤ 16 * x ^ 4 + 96 * x ^ 3 + 144 * x ^ 2 + 80 * x := by positivity
  have hA' := mul_le_mul_of_nonneg_right ht1 hA
  have hB' := mul_le_mul_of_nonneg_right ht2 hB
  have hplus : 0 ≤ t * (298 * x ^ 4 + 762 * x ^ 3 + 522 * x ^ 2) := by positivity
  have hpad : 0 ≤ t ^ 2 * (4 * x ^ 4 + 12 * x ^ 3 + 8 * x) := by positivity
  have hx3 : x ^ 2 / 2 ≤ x ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  unfold cubicRemainder
  nlinarith only [hA', hB', hplus, hpad, hx3, pow_nonneg hx0 7, pow_nonneg hx0 6,
    pow_nonneg hx0 5, pow_nonneg hx0 4, sq_nonneg x, hx0]

/-- A square completion makes the unit-face cubic coefficient positive. -/
theorem unit3_pos {t x : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) (hx : 1 / 2 ≤ x) :
    0 < unit3 t x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have h2 : 1 / 4 ≤ x ^ 2 := by nlinarith only [hx]
  have h3 : 1 / 8 ≤ x ^ 3 := by
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 2 by norm_num) hx 3
    norm_num at hp
    exact hp
  have hbase : 0 < x ^ 2 * (11 * x ^ 4 + 104 * x ^ 3 + 231 * x ^ 2 + 78 * x - 90) := by
    have hc : 0 < 11 * x ^ 4 + 104 * x ^ 3 + 231 * x ^ 2 + 78 * x - 90 := by
      nlinarith only [h2, h3, hx, pow_nonneg hx0 4]
    exact mul_pos (sq_pos_of_pos hxpos) hc
  have hlin := mul_nonneg ht (cubicLinear_nonneg hx)
  have hrem := mul_nonneg (sq_nonneg t) (cubicRemainder_pos ht ht1 hx).le
  have he : unit3 t x = 2 * (x ^ 2 * (11 * x ^ 4 + 104 * x ^ 3 + 231 * x ^ 2 + 78 * x - 90)
      + t * cubicLinear x + t ^ 2 * cubicRemainder t x) := by
    unfold unit3 cubicLinear cubicRemainder
    ring
  linarith only [he, hbase, hlin, hrem]

/-- The leading coefficient has positive geometric factors. -/
theorem unit4_pos {t x : ℝ} (ht : 0 ≤ t) (hx : 1 / 2 ≤ x) : 0 < unit4 t x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hg : 0 < 6 * t + 5 * x - 1 := by linarith only [ht, hx]
  unfold unit4
  positivity

/-- The full cleared quartic is positive on the feasible unit face. -/
theorem unit_quartic_pos {t x y : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hx : 1 / 2 ≤ x) (hx7 : x ≤ 7 / 3)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) (hy : 0 ≤ y) :
    0 < unit0 t x + unit1 t x * y + unit2 t x * y ^ 2 + unit3 t x * y ^ 3 + unit4 t x * y ^ 4 := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht0 : 0 < 1 - t := by linarith only [ht1]
  have h0 : 0 < unit0 t x := by
    have hp := incoming0_pos ht1 hx hx7 hT
    unfold unit0
    positivity
  have h1 : 0 ≤ unit1 t x := by
    have hp := incoming1_pos ht ht1 hx hx7 hT
    unfold unit1
    positivity
  exact nsr_quartic_cubic_tail h0 h1 (unit3_pos ht ht1 hx).le (unit4_pos ht hx).le
    (quadraticMargin_pos ht1 hx hx7 hT).le (cubicMargin_pos ht ht1 hx hx7 hT).le hy

end SmoothedOctagon.LowScale
