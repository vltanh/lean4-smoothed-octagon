module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Monotonicity on the reverse scale strip

Use the reciprocal-mean secant ceiling and start at `t = 3/8`.
Each coefficient of the cleared ratio cubic increases with `t`.
On `0 ≤ x ≤ 1/4`, elementary power bounds absorb the high powers
of `x`; the remaining coefficients are nonnegative.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Coefficient of `(q - 1)^0` on the scale face. -/
def nsrSC0 {R : Type*} [CommRing R] (t x : R) : R :=
  -348 * t ^ 4 * x ^ 5 + 1392 * t ^ 4 * x ^ 3 + 1044 * t ^ 4 * x ^ 2 - 48 * t ^ 3 * x ^ 6 + 108 * t ^ 3 * x
    ^ 5 - 1272 * t ^ 3 * x ^ 4 - 3804 * t ^ 3 * x ^ 3 - 2376 * t ^ 3 * x ^ 2 + 96 * t ^ 2 * x ^ 6 + 528 * t
    ^ 2 * x ^ 5 + 1944 * t ^ 2 * x ^ 4 + 3132 * t ^ 2 * x ^ 3 + 1620 * t ^ 2 * x ^ 2 - 48 * t * x ^ 6 - 288
    * t * x ^ 5 - 672 * t * x ^ 4 - 720 * t * x ^ 3 - 288 * t * x ^ 2

private def stripD0 (t x : ℝ) : ℝ :=
  -1392 * t ^ 3 * x ^ 3 + 5568 * t ^ 3 * x + 4176 * t ^ 3 - 144 * t ^ 2 * x ^ 4 + 324 * t ^ 2 * x ^ 3 - 3816
    * t ^ 2 * x ^ 2 - 11412 * t ^ 2 * x - 7128 * t ^ 2 + 192 * t * x ^ 4 + 1056 * t * x ^ 3 + 3888 * t * x ^
    2 + 6264 * t * x + 3240 * t - 48 * x ^ 4 - 288 * x ^ 3 - 672 * x ^ 2 - 720 * x - 288

/-- Coefficient of `(q - 1)^1` on the scale face. -/
def nsrSC1 {R : Type*} [CommRing R] (t x : R) : R :=
  -348 * t ^ 4 * x ^ 6 - 3306 * t ^ 4 * x ^ 5 - 6960 * t ^ 4 * x ^ 4 - 6612 * t ^ 4 * x ^ 3 - 4698 * t ^ 4 *
    x ^ 2 - 2088 * t ^ 4 * x - 48 * t ^ 3 * x ^ 7 - 60 * t ^ 3 * x ^ 6 + 1770 * t ^ 3 * x ^ 5 + 2400 * t ^ 3
    * x ^ 4 + 294 * t ^ 3 * x ^ 3 + 2340 * t ^ 3 * x ^ 2 + 2664 * t ^ 3 * x + 96 * t ^ 2 * x ^ 7 + 1152 * t
    ^ 2 * x ^ 6 + 4368 * t ^ 2 * x ^ 5 + 9360 * t ^ 2 * x ^ 4 + 10230 * t ^ 2 * x ^ 3 + 3366 * t ^ 2 * x ^ 2
    - 864 * t ^ 2 * x - 48 * t * x ^ 7 - 744 * t * x ^ 6 - 2832 * t * x ^ 5 - 4800 * t * x ^ 4 - 3960 * t *
    x ^ 3 - 960 * t * x ^ 2 + 432 * t * x + 48 * x ^ 3 - 48 * x ^ 2 - 144 * x

private def stripD1 (t x : ℝ) : ℝ :=
  -1392 * t ^ 3 * x ^ 5 - 13224 * t ^ 3 * x ^ 4 - 27840 * t ^ 3 * x ^ 3 - 26448 * t ^ 3 * x ^ 2 - 18792 * t
    ^ 3 * x - 8352 * t ^ 3 - 144 * t ^ 2 * x ^ 6 - 180 * t ^ 2 * x ^ 5 + 5310 * t ^ 2 * x ^ 4 + 7200 * t ^ 2
    * x ^ 3 + 882 * t ^ 2 * x ^ 2 + 7020 * t ^ 2 * x + 7992 * t ^ 2 + 192 * t * x ^ 6 + 2304 * t * x ^ 5 +
    8736 * t * x ^ 4 + 18720 * t * x ^ 3 + 20460 * t * x ^ 2 + 6732 * t * x - 1728 * t - 48 * x ^ 6 - 744 *
    x ^ 5 - 2832 * x ^ 4 - 4800 * x ^ 3 - 3960 * x ^ 2 - 960 * x + 432

/-- Coefficient of `(q - 1)^2` on the scale face. -/
def nsrSC2 {R : Type*} [CommRing R] (t x : R) : R :=
  -522 * t ^ 4 * x ^ 6 - 4176 * t ^ 4 * x ^ 5 - 8874 * t ^ 4 * x ^ 4 - 7656 * t ^ 4 * x ^ 3 - 2436 * t ^ 4 *
    x ^ 2 + 1044 * t ^ 4 * x + 1044 * t ^ 4 - 72 * t ^ 3 * x ^ 7 + 168 * t ^ 3 * x ^ 6 + 3984 * t ^ 3 * x ^
    5 + 10092 * t ^ 3 * x ^ 4 + 12240 * t ^ 3 * x ^ 3 + 10068 * t ^ 3 * x ^ 2 + 3888 * t ^ 3 * x - 288 * t ^
    3 + 120 * t ^ 2 * x ^ 7 + 1248 * t ^ 2 * x ^ 6 + 4116 * t ^ 2 * x ^ 5 + 7158 * t ^ 2 * x ^ 4 + 5784 * t
    ^ 2 * x ^ 3 + 102 * t ^ 2 * x ^ 2 - 1296 * t ^ 2 * x + 288 * t ^ 2 - 24 * t * x ^ 8 - 336 * t * x ^ 7 -
    2112 * t * x ^ 6 - 5928 * t * x ^ 5 - 8376 * t * x ^ 4 - 5904 * t * x ^ 3 - 1152 * t * x ^ 2 + 504 * t *
    x - 144 * t + 24 * x ^ 4 + 144 * x ^ 3 - 24 * x ^ 2 - 216 * x

private def stripD2 (t x : ℝ) : ℝ :=
  -2088 * t ^ 3 * x ^ 6 - 16704 * t ^ 3 * x ^ 5 - 35496 * t ^ 3 * x ^ 4 - 30624 * t ^ 3 * x ^ 3 - 9744 * t ^
    3 * x ^ 2 + 4176 * t ^ 3 * x + 4176 * t ^ 3 - 216 * t ^ 2 * x ^ 7 + 504 * t ^ 2 * x ^ 6 + 11952 * t ^ 2
    * x ^ 5 + 30276 * t ^ 2 * x ^ 4 + 36720 * t ^ 2 * x ^ 3 + 30204 * t ^ 2 * x ^ 2 + 11664 * t ^ 2 * x -
    864 * t ^ 2 + 240 * t * x ^ 7 + 2496 * t * x ^ 6 + 8232 * t * x ^ 5 + 14316 * t * x ^ 4 + 11568 * t * x
    ^ 3 + 204 * t * x ^ 2 - 2592 * t * x + 576 * t - 24 * x ^ 8 - 336 * x ^ 7 - 2112 * x ^ 6 - 5928 * x ^ 5
    - 8376 * x ^ 4 - 5904 * x ^ 3 - 1152 * x ^ 2 + 504 * x - 144

/-- Coefficient of `(q - 1)^3` on the scale face. -/
def nsrSC3 {R : Type*} [CommRing R] (t x : R) : R :=
  -174 * t ^ 4 * x ^ 6 - 1247 * t ^ 4 * x ^ 5 - 2175 * t ^ 4 * x ^ 4 - 435 * t ^ 4 * x ^ 3 + 2233 * t ^ 4 *
    x ^ 2 + 2436 * t ^ 4 * x + 870 * t ^ 4 - 24 * t ^ 3 * x ^ 7 + 167 * t ^ 3 * x ^ 6 + 2229 * t ^ 3 * x ^ 5
    + 6285 * t ^ 3 * x ^ 4 + 8309 * t ^ 3 * x ^ 3 + 5928 * t ^ 3 * x ^ 2 + 1722 * t ^ 3 * x - 144 * t ^ 3 +
    60 * t ^ 2 * x ^ 7 + 564 * t ^ 2 * x ^ 6 + 1680 * t ^ 2 * x ^ 5 + 2370 * t ^ 2 * x ^ 4 + 1302 * t ^ 2 *
    x ^ 3 - 444 * t ^ 2 * x ^ 2 - 432 * t ^ 2 * x + 144 * t ^ 2 - 4 * t * x ^ 8 - 84 * t * x ^ 7 - 660 * t *
    x ^ 6 - 1996 * t * x ^ 5 - 2880 * t * x ^ 4 - 1996 * t * x ^ 3 - 316 * t * x ^ 2 + 240 * t * x - 24 * t
    + 20 * x ^ 4 + 116 * x ^ 3 + 96 * x ^ 2 - 24 * x

private def stripD3 (t x : ℝ) : ℝ :=
  -696 * t ^ 3 * x ^ 6 - 4988 * t ^ 3 * x ^ 5 - 8700 * t ^ 3 * x ^ 4 - 1740 * t ^ 3 * x ^ 3 + 8932 * t ^ 3 *
    x ^ 2 + 9744 * t ^ 3 * x + 3480 * t ^ 3 - 72 * t ^ 2 * x ^ 7 + 501 * t ^ 2 * x ^ 6 + 6687 * t ^ 2 * x ^
    5 + 18855 * t ^ 2 * x ^ 4 + 24927 * t ^ 2 * x ^ 3 + 17784 * t ^ 2 * x ^ 2 + 5166 * t ^ 2 * x - 432 * t ^
    2 + 120 * t * x ^ 7 + 1128 * t * x ^ 6 + 3360 * t * x ^ 5 + 4740 * t * x ^ 4 + 2604 * t * x ^ 3 - 888 *
    t * x ^ 2 - 864 * t * x + 288 * t - 4 * x ^ 8 - 84 * x ^ 7 - 660 * x ^ 6 - 1996 * x ^ 5 - 2880 * x ^ 4 -
    1996 * x ^ 3 - 316 * x ^ 2 + 240 * x - 24

private theorem strip_powers {t : ℝ} (ht : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5) :
    9 / 64 ≤ t ^ 2 ∧ t ^ 2 ≤ 4 / 25 ∧ 27 / 512 ≤ t ^ 3 ∧ t ^ 3 ≤ 8 / 125 := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have h2lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 8) ht 2
  have h2hi := pow_le_pow_left₀ ht0 ht1 2
  have h3lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 8) ht 3
  have h3hi := pow_le_pow_left₀ ht0 ht1 3
  norm_num at h2lo h2hi h3lo h3hi
  exact ⟨h2lo, h2hi, h3lo, h3hi⟩

private theorem stripD0_nonneg {t x : ℝ} (ht : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) : 0 ≤ stripD0 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (4 : ℝ) ≤ 4176 * t ^ 3 - 7128 * t ^ 2 + 3240 * t - 288 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ 5568 * t ^ 3 - 11412 * t ^ 2 + 6264 * t - 720 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ -3816 * t ^ 2 + 3888 * t - 672 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -1392 * t ^ 3 + 324 * t ^ 2 + 1056 * t - 288 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (0 : ℝ) ≤ -144 * t ^ 2 + 192 * t - 48 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hp : (0 : ℝ) ≤ 4 := by norm_num
  unfold stripD0
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hp

private theorem stripSC0_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC0 t x) (x ^ 2 * stripD0 t x) t := by
  let p : Polynomial ℝ := nsrSC0 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC0]
  · norm_num [p, nsrSC0, stripD0, Polynomial.derivative_mul, Polynomial.derivative_pow]; ring

/-- The coefficient of `(q - 1)^0` increases along the scale strip. -/
theorem nsrSC0_mono {x a b : ℝ} (hx : 0 ≤ x)
    (ha : 3 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC0 a x ≤ nsrSC0 b x := by
  have hm : MonotoneOn (fun t => nsrSC0 t x) (Set.Icc (3 / 8) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t _ => (stripSC0_deriv t x).continuousAt.continuousWithinAt)
      (fun t _ => (stripSC0_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD0_nonneg ht.1.le ht.2.le hx
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripD1_nonneg {t x : ℝ} (ht : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) : 0 ≤ stripD1 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (320 : ℝ) ≤ -8352 * t ^ 3 + 7992 * t ^ 2 - 1728 * t + 432 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ -18792 * t ^ 3 + 7020 * t ^ 2 + 6732 * t - 960 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ -26448 * t ^ 3 + 882 * t ^ 2 + 20460 * t - 3960 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -27840 * t ^ 3 + 7200 * t ^ 2 + 18720 * t - 4800 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (0 : ℝ) ≤ -13224 * t ^ 3 + 5310 * t ^ 2 + 8736 * t - 2832 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (0 : ℝ) ≤ -1392 * t ^ 3 - 180 * t ^ 2 + 2304 * t - 744 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (0 : ℝ) ≤ -144 * t ^ 2 + 192 * t - 48 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hp : (0 : ℝ) ≤ 320 := by norm_num
  unfold stripD1
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hp

private theorem stripSC1_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC1 t x) (x * stripD1 t x) t := by
  let p : Polynomial ℝ := nsrSC1 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC1]; ring
  · norm_num [p, nsrSC1, stripD1, Polynomial.derivative_mul, Polynomial.derivative_pow]; ring

/-- The coefficient of `(q - 1)^1` increases along the scale strip. -/
theorem nsrSC1_mono {x a b : ℝ} (hx : 0 ≤ x)
    (ha : 3 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC1 a x ≤ nsrSC1 b x := by
  have hm : MonotoneOn (fun t => nsrSC1 t x) (Set.Icc (3 / 8) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t _ => (stripSC1_deriv t x).continuousAt.continuousWithinAt)
      (fun t _ => (stripSC1_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD1_nonneg ht.1.le ht.2.le hx
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripD2_nonneg {t x : ℝ} (ht : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : 0 ≤ stripD2 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (120 : ℝ) ≤ 4176 * t ^ 3 - 864 * t ^ 2 + 576 * t - 144 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ 4176 * t ^ 3 + 11664 * t ^ 2 - 2592 * t + 504 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ -9744 * t ^ 3 + 30204 * t ^ 2 + 204 * t - 1152 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -30624 * t ^ 3 + 36720 * t ^ 2 + 11568 * t - 5904 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (-2400 : ℝ) ≤ -35496 * t ^ 3 + 30276 * t ^ 2 + 14316 * t - 8376 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (-2400 : ℝ) ≤ -16704 * t ^ 3 + 11952 * t ^ 2 + 8232 * t - 5928 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (-2400 : ℝ) ≤ -2088 * t ^ 3 + 504 * t ^ 2 + 2496 * t - 2112 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hc7 : (-2400 : ℝ) ≤ -216 * t ^ 2 + 240 * t - 336 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm7 := mul_nonneg (sub_nonneg.mpr hc7) (pow_nonneg hx 7)
  have hc8 : (-2400 : ℝ) ≤ -24 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm8 := mul_nonneg (sub_nonneg.mpr hc8) (pow_nonneg hx 8)
  have hx4 := pow_le_pow_left₀ hx hx1 4
  have hx5 := pow_le_pow_left₀ hx hx1 5
  have hx6 := pow_le_pow_left₀ hx hx1 6
  have hx7 := pow_le_pow_left₀ hx hx1 7
  have hx8 := pow_le_pow_left₀ hx hx1 8
  have hp : 0 ≤ 120 - 2400 * (x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8) := by
    nlinarith only [hx4, hx5, hx6, hx7, hx8]
  unfold stripD2
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hm7 + hm8 + hp

private theorem stripSC2_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC2 t x) (1 * stripD2 t x) t := by
  let p : Polynomial ℝ := nsrSC2 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC2]; ring
  · norm_num [p, nsrSC2, stripD2, Polynomial.derivative_mul, Polynomial.derivative_pow]; ring

/-- The coefficient of `(q - 1)^2` increases along the scale strip. -/
theorem nsrSC2_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4)
    (ha : 3 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC2 a x ≤ nsrSC2 b x := by
  have hm : MonotoneOn (fun t => nsrSC2 t x) (Set.Icc (3 / 8) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t _ => (stripSC2_deriv t x).continuousAt.continuousWithinAt)
      (fun t _ => (stripSC2_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD2_nonneg ht.1.le ht.2.le hx hx1
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripD3_nonneg {t x : ℝ} (ht : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : 0 ≤ stripD3 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (160 : ℝ) ≤ 3480 * t ^ 3 - 432 * t ^ 2 + 288 * t - 24 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ 9744 * t ^ 3 + 5166 * t ^ 2 - 864 * t + 240 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ 8932 * t ^ 3 + 17784 * t ^ 2 - 888 * t - 316 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -1740 * t ^ 3 + 24927 * t ^ 2 + 2604 * t - 1996 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (0 : ℝ) ≤ -8700 * t ^ 3 + 18855 * t ^ 2 + 4740 * t - 2880 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (-400 : ℝ) ≤ -4988 * t ^ 3 + 6687 * t ^ 2 + 3360 * t - 1996 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (-400 : ℝ) ≤ -696 * t ^ 3 + 501 * t ^ 2 + 1128 * t - 660 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hc7 : (-400 : ℝ) ≤ -72 * t ^ 2 + 120 * t - 84 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm7 := mul_nonneg (sub_nonneg.mpr hc7) (pow_nonneg hx 7)
  have hc8 : (-400 : ℝ) ≤ -4 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm8 := mul_nonneg (sub_nonneg.mpr hc8) (pow_nonneg hx 8)
  have hx5 := pow_le_pow_left₀ hx hx1 5
  have hx6 := pow_le_pow_left₀ hx hx1 6
  have hx7 := pow_le_pow_left₀ hx hx1 7
  have hx8 := pow_le_pow_left₀ hx hx1 8
  have hp : 0 ≤ 160 - 400 * (x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8) := by
    nlinarith only [hx5, hx6, hx7, hx8]
  unfold stripD3
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hm7 + hm8 + hp

private theorem stripSC3_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC3 t x) (1 * stripD3 t x) t := by
  let p : Polynomial ℝ := nsrSC3 Polynomial.X (Polynomial.C x)
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC3]; ring
  · norm_num [p, nsrSC3, stripD3, Polynomial.derivative_mul, Polynomial.derivative_pow]; ring

/-- The coefficient of `(q - 1)^3` increases along the scale strip. -/
theorem nsrSC3_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4)
    (ha : 3 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC3 a x ≤ nsrSC3 b x := by
  have hm : MonotoneOn (fun t => nsrSC3 t x) (Set.Icc (3 / 8) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t _ => (stripSC3_deriv t x).continuousAt.continuousWithinAt)
      (fun t _ => (stripSC3_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD3_nonneg ht.1.le ht.2.le hx hx1
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

end SmoothedOctagon
