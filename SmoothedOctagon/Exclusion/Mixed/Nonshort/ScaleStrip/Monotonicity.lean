module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Monotonicity on the reverse scale strip

The scale `k = 29t²/4` grows fast enough that every coefficient of the
cleared residual increases with `t`. On `1/3 ≤ t ≤ 2/5`, the quadratic
and cubic powers of `t` lie between constant multiples of `t`.
These bounds make the low powers of `x` positive. A geometric sum
bounds the remaining high powers for `0 ≤ x ≤ 1/3`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Coefficient of `(q - 1)^0` on the scale face. -/
noncomputable def nsrSC0 (t x : ℝ) : ℝ :=
  (-12 * x ^ 7 - 76 * x ^ 6 - 224 * x ^ 5 - 352 * x ^ 4 - 288 * x ^ 3 - 96 * x ^ 2) * t
  + (24 * x ^ 7 + 144 * x ^ 6 + 561 * x ^ 5 + 1215 * x ^ 4 + 1314 * x ^ 3 + 540 * x ^ 2) * t ^ 2
  + (-12 * x ^ 7 - 10 * x ^ 6 - 250 * x ^ 5 - 1124 * x ^ 4 - 1664 * x ^ 3 - 792 * x ^ 2) * t ^ 3
  + (-58 * x ^ 6 - 87 * x ^ 5 + 261 * x ^ 4 + 638 * x ^ 3 + 348 * x ^ 2) * t ^ 4

/-- Coefficient of `(q - 1)^1` on the scale face. -/
noncomputable def nsrSC1 (t x : ℝ) : ℝ :=
  (8 * x ^ 4 + 4 * x ^ 3 - 40 * x ^ 2 - 48 * x)
  + (-16 * x ^ 8 - 186 * x ^ 7 - 814 * x ^ 6 - 1836 * x ^ 5 - 2292 * x ^ 4 - 1468 * x ^ 3 - 248 * x ^ 2 +
    144 * x) * t
  + (28 * x ^ 8 + 288 * x ^ 7 + 1253 * x ^ 6 + 6461 * x ^ 5 / 2 + 9861 * x ^ 4 / 2 + 3947 * x ^ 3 + 978 * x
    ^ 2 - 288 * x) * t ^ 2
  + (-12 * x ^ 8 - 15 * x ^ 7 + 344 * x ^ 6 + 998 * x ^ 5 + 877 * x ^ 4 + 562 * x ^ 3 + 1224 * x ^ 2 + 888 *
    x) * t ^ 3
  + (-87 * x ^ 7 - 783 * x ^ 6 - 4785 * x ^ 5 / 2 - 7047 * x ^ 4 / 2 - 3045 * x ^ 3 - 1914 * x ^ 2 - 696 *
    x) * t ^ 4

/-- Coefficient of `(q - 1)^2` on the scale face. -/
noncomputable def nsrSC2 (t x : ℝ) : ℝ :=
  (6 * x ^ 5 + 34 * x ^ 4 + 38 * x ^ 3 - 44 * x ^ 2 - 72 * x)
  + (-6 * x ^ 9 - 90 * x ^ 8 - 564 * x ^ 7 - 1862 * x ^ 6 - 3514 * x ^ 5 - 3816 * x ^ 4 - 2144 * x ^ 3 - 304
    * x ^ 2 + 144 * x - 48) * t
  + (36 * x ^ 8 + 312 * x ^ 7 + 2427 * x ^ 6 / 2 + 2694 * x ^ 5 + 6747 * x ^ 4 / 2 + 1905 * x ^ 3 - 174 * x
    ^ 2 - 384 * x + 96) * t ^ 2
  + (-18 * x ^ 8 + 42 * x ^ 7 + 913 * x ^ 6 + 3262 * x ^ 5 + 5627 * x ^ 4 + 5870 * x ^ 3 + 3996 * x ^ 2 +
    1248 * x - 96) * t ^ 3
  + (-261 * x ^ 7 / 2 - 2059 * x ^ 6 / 2 - 3045 * x ^ 5 - 8613 * x ^ 4 / 2 - 5887 * x ^ 3 / 2 - 609 * x ^ 2
    + 522 * x + 348) * t ^ 4

/-- Coefficient of `(q - 1)^3` on the scale face. -/
noncomputable def nsrSC3 (t x : ℝ) : ℝ :=
  (5 * x ^ 5 + 29 * x ^ 4 + 54 * x ^ 3 + 28 * x ^ 2 - 8 * x)
  + (-x ^ 9 - 23 * x ^ 8 - 171 * x ^ 7 - 611 * x ^ 6 - 1194 * x ^ 5 - 1305 * x ^ 4 - 711 * x ^ 3 - 66 * x ^
    2 + 76 * x - 8) * t
  + (17 * x ^ 8 + 141 * x ^ 7 + 1019 * x ^ 6 / 2 + 1975 * x ^ 5 / 2 + 1002 * x ^ 4 + 346 * x ^ 3 - 216 * x ^
    2 - 120 * x + 48) * t ^ 2
  + (-6 * x ^ 8 + 167 * x ^ 7 / 4 + 2143 * x ^ 6 / 4 + 7843 * x ^ 5 / 4 + 14477 * x ^ 4 / 4 + 7615 * x ^ 3 /
    2 + 2259 * x ^ 2 + 550 * x - 48) * t ^ 3
  + (-87 * x ^ 7 / 2 - 1247 * x ^ 6 / 4 - 3219 * x ^ 5 / 4 - 3045 * x ^ 4 / 4 + 1131 * x ^ 3 / 4 + 2349 * x
    ^ 2 / 2 + 957 * x + 290) * t ^ 4

private noncomputable def stripD0 (t x : ℝ) : ℝ :=
  (1392 * t ^ 3 - 2376 * t ^ 2 + 1080 * t - 96)
  + (2552 * t ^ 3 - 4992 * t ^ 2 + 2628 * t - 288) * x
  + (1044 * t ^ 3 - 3372 * t ^ 2 + 2430 * t - 352) * x ^ 2
  + (-348 * t ^ 3 - 750 * t ^ 2 + 1122 * t - 224) * x ^ 3
  + (-232 * t ^ 3 - 30 * t ^ 2 + 288 * t - 76) * x ^ 4
  + (-36 * t ^ 2 + 48 * t - 12) * x ^ 5

private noncomputable def stripD1 (t x : ℝ) : ℝ :=
  (-2784 * t ^ 3 + 2664 * t ^ 2 - 576 * t + 144)
  + (-7656 * t ^ 3 + 3672 * t ^ 2 + 1956 * t - 248) * x
  + (-12180 * t ^ 3 + 1686 * t ^ 2 + 7894 * t - 1468) * x ^ 2
  + (-14094 * t ^ 3 + 2631 * t ^ 2 + 9861 * t - 2292) * x ^ 3
  + (-9570 * t ^ 3 + 2994 * t ^ 2 + 6461 * t - 1836) * x ^ 4
  + (-3132 * t ^ 3 + 1032 * t ^ 2 + 2506 * t - 814) * x ^ 5
  + (-348 * t ^ 3 - 45 * t ^ 2 + 576 * t - 186) * x ^ 6
  + (-36 * t ^ 2 + 56 * t - 16) * x ^ 7

private noncomputable def stripD2 (t x : ℝ) : ℝ :=
  (1392 * t ^ 3 - 288 * t ^ 2 + 192 * t - 48)
  + (2088 * t ^ 3 + 3744 * t ^ 2 - 768 * t + 144) * x
  + (-2436 * t ^ 3 + 11988 * t ^ 2 - 348 * t - 304) * x ^ 2
  + (-11774 * t ^ 3 + 17610 * t ^ 2 + 3810 * t - 2144) * x ^ 3
  + (-17226 * t ^ 3 + 16881 * t ^ 2 + 6747 * t - 3816) * x ^ 4
  + (-12180 * t ^ 3 + 9786 * t ^ 2 + 5388 * t - 3514) * x ^ 5
  + (-4118 * t ^ 3 + 2739 * t ^ 2 + 2427 * t - 1862) * x ^ 6
  + (-522 * t ^ 3 + 126 * t ^ 2 + 624 * t - 564) * x ^ 7
  + (-54 * t ^ 2 + 72 * t - 90) * x ^ 8
  + (-6) * x ^ 9

private noncomputable def stripD3 (t x : ℝ) : ℝ :=
  (1160 * t ^ 3 - 144 * t ^ 2 + 96 * t - 8)
  + (3828 * t ^ 3 + 1650 * t ^ 2 - 240 * t + 76) * x
  + (4698 * t ^ 3 + 6777 * t ^ 2 - 432 * t - 66) * x ^ 2
  + (1131 * t ^ 3 + 22845 * t ^ 2 / 2 + 692 * t - 711) * x ^ 3
  + (-3045 * t ^ 3 + 43431 * t ^ 2 / 4 + 2004 * t - 1305) * x ^ 4
  + (-3219 * t ^ 3 + 23529 * t ^ 2 / 4 + 1975 * t - 1194) * x ^ 5
  + (-1247 * t ^ 3 + 6429 * t ^ 2 / 4 + 1019 * t - 611) * x ^ 6
  + (-174 * t ^ 3 + 501 * t ^ 2 / 4 + 282 * t - 171) * x ^ 7
  + (-18 * t ^ 2 + 34 * t - 23) * x ^ 8
  + (-1) * x ^ 9

private theorem strip_powers {t : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) :
    t / 3 ≤ t ^ 2 ∧ t ^ 2 ≤ 2 / 5 * t ∧ t / 9 ≤ t ^ 3 ∧ t ^ 3 ≤ 4 / 25 * t := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hlo := mul_nonneg ht0 (show 0 ≤ t - 1 / 3 by linarith only [ht])
  have hhi := mul_nonneg ht0 (show 0 ≤ 2 / 5 - t by linarith only [ht1])
  have hlo3 := mul_nonneg (sq_nonneg t) (show 0 ≤ t - 1 / 3 by linarith only [ht])
  have hhi3 := mul_nonneg (sq_nonneg t) (show 0 ≤ 2 / 5 - t by linarith only [ht1])
  constructor
  · nlinarith only [hlo]
  constructor
  · nlinarith only [hhi]
  constructor
  · nlinarith only [hlo, hlo3]
  · nlinarith only [hhi, hhi3]

/-- A finite geometric sum is bounded by the infinite sum at one third. -/
private theorem strip_geom {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) :
    1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 ≤ 3 / 2 := by
  have hp : 0 ≤ (1 / 3 - x) * (1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5) := by
    apply mul_nonneg (by linarith only [hx1])
    positivity
  nlinarith only [hp, pow_nonneg hx 6]

private theorem stripD0_nonneg {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (_hx1 : x ≤ 1 / 3) : 0 ≤ stripD0 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (0 : ℝ) ≤ 1392 * t ^ 3 - 2376 * t ^ 2 + 1080 * t - 96 := by
    have hq : 0 ≤ -58 * t ^ 2 + 41 * t - 4 := by linarith only [h2hi, ht]
    have hp : 0 ≤ 24 * (1 - t) * (-58 * t ^ 2 + 41 * t - 4) := by
      apply mul_nonneg (by linarith only [ht1]) hq
    nlinarith only [hp]
  have hc1 : (0 : ℝ) ≤ 2552 * t ^ 3 - 4992 * t ^ 2 + 2628 * t - 288 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ 1044 * t ^ 3 - 3372 * t ^ 2 + 2430 * t - 352 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -348 * t ^ 3 - 750 * t ^ 2 + 1122 * t - 224 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (0 : ℝ) ≤ -232 * t ^ 3 - 30 * t ^ 2 + 288 * t - 76 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (0 : ℝ) ≤ -36 * t ^ 2 + 48 * t - 12 := by
    have hp : 0 ≤ 12 * (1 - t) * (3 * t - 1) := by
      exact mul_nonneg (by linarith only [ht1]) (by linarith only [ht])
    nlinarith only [hp]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  unfold stripD0
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5

private theorem stripD1_nonneg {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) : 0 ≤ stripD1 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (80 : ℝ) ≤ -2784 * t ^ 3 + 2664 * t ^ 2 - 576 * t + 144 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ -7656 * t ^ 3 + 3672 * t ^ 2 + 1956 * t - 248 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ -12180 * t ^ 3 + 1686 * t ^ 2 + 7894 * t - 1468 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -14094 * t ^ 3 + 2631 * t ^ 2 + 9861 * t - 2292 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (100 : ℝ) ≤ -9570 * t ^ 3 + 2994 * t ^ 2 + 6461 * t - 1836 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (-40 : ℝ) ≤ -3132 * t ^ 3 + 1032 * t ^ 2 + 2506 * t - 814 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (-20 : ℝ) ≤ -348 * t ^ 3 - 45 * t ^ 2 + 576 * t - 186 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hc7 : (-4 : ℝ) ≤ -36 * t ^ 2 + 56 * t - 16 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm7 := mul_nonneg (sub_nonneg.mpr hc7) (pow_nonneg hx 7)
  unfold stripD1
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1, sq_nonneg (x - 1 / 3)]
  have hx3 : x ^ 3 ≤ 1 := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ ≤ 1 * 1 := mul_le_mul hx2 (by linarith only [hx1]) hx (by norm_num)
      _ = 1 := by norm_num
  have hp : 0 ≤ x ^ 4 * (100 - 40 * x - 20 * x ^ 2 - 4 * x ^ 3) :=
    mul_nonneg (pow_nonneg hx 4) (by linarith only [hx1, hx2, hx3])
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hm7 + hp

private theorem stripD2_nonneg {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) : 0 ≤ stripD2 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (28 : ℝ) ≤ 1392 * t ^ 3 - 288 * t ^ 2 + 192 * t - 48 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ 2088 * t ^ 3 + 3744 * t ^ 2 - 768 * t + 144 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ -2436 * t ^ 3 + 11988 * t ^ 2 - 348 * t - 304 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ -11774 * t ^ 3 + 17610 * t ^ 2 + 3810 * t - 2144 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (-1500 : ℝ) ≤ -17226 * t ^ 3 + 16881 * t ^ 2 + 6747 * t - 3816 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (-1500 : ℝ) ≤ -12180 * t ^ 3 + 9786 * t ^ 2 + 5388 * t - 3514 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (-1500 : ℝ) ≤ -4118 * t ^ 3 + 2739 * t ^ 2 + 2427 * t - 1862 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hc7 : (-1500 : ℝ) ≤ -522 * t ^ 3 + 126 * t ^ 2 + 624 * t - 564 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm7 := mul_nonneg (sub_nonneg.mpr hc7) (pow_nonneg hx 7)
  have hc8 : (-1500 : ℝ) ≤ -54 * t ^ 2 + 72 * t - 90 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm8 := mul_nonneg (sub_nonneg.mpr hc8) (pow_nonneg hx 8)
  have hc9 : (-1500 : ℝ) ≤ -6 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm9 := mul_nonneg (sub_nonneg.mpr hc9) (pow_nonneg hx 9)
  unfold stripD2
  have hxpow : x ^ 4 ≤ (1 / 3 : ℝ) ^ 4 := pow_le_pow_left₀ hx hx1 4
  have hg := strip_geom hx hx1
  have hp0 : x ^ 4 * (1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5) ≤ (1 / 3 : ℝ) ^ 4 * (3 / 2) :=
    mul_le_mul hxpow hg (by positivity) (by positivity)
  have hp : 0 ≤ 28 - 1500 * x ^ 4 * (1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5) := by
    norm_num at hp0
    linarith only [hp0]
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hm7 + hm8 + hm9 + hp

private theorem stripD3_nonneg {t x : ℝ} (ht : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) : 0 ≤ stripD3 t x := by
  obtain ⟨h2lo, h2hi, h3lo, h3hi⟩ := strip_powers ht ht1
  have hc0 : (40 : ℝ) ≤ 1160 * t ^ 3 - 144 * t ^ 2 + 96 * t - 8 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hc1 : (0 : ℝ) ≤ 3828 * t ^ 3 + 1650 * t ^ 2 - 240 * t + 76 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm1 := mul_nonneg (sub_nonneg.mpr hc1) (pow_nonneg hx 1)
  have hc2 : (0 : ℝ) ≤ 4698 * t ^ 3 + 6777 * t ^ 2 - 432 * t - 66 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm2 := mul_nonneg (sub_nonneg.mpr hc2) (pow_nonneg hx 2)
  have hc3 : (0 : ℝ) ≤ 1131 * t ^ 3 + 22845 * t ^ 2 / 2 + 692 * t - 711 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm3 := mul_nonneg (sub_nonneg.mpr hc3) (pow_nonneg hx 3)
  have hc4 : (0 : ℝ) ≤ -3045 * t ^ 3 + 43431 * t ^ 2 / 4 + 2004 * t - 1305 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm4 := mul_nonneg (sub_nonneg.mpr hc4) (pow_nonneg hx 4)
  have hc5 : (-200 : ℝ) ≤ -3219 * t ^ 3 + 23529 * t ^ 2 / 4 + 1975 * t - 1194 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm5 := mul_nonneg (sub_nonneg.mpr hc5) (pow_nonneg hx 5)
  have hc6 : (-200 : ℝ) ≤ -1247 * t ^ 3 + 6429 * t ^ 2 / 4 + 1019 * t - 611 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm6 := mul_nonneg (sub_nonneg.mpr hc6) (pow_nonneg hx 6)
  have hc7 : (-200 : ℝ) ≤ -174 * t ^ 3 + 501 * t ^ 2 / 4 + 282 * t - 171 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm7 := mul_nonneg (sub_nonneg.mpr hc7) (pow_nonneg hx 7)
  have hc8 : (-200 : ℝ) ≤ -18 * t ^ 2 + 34 * t - 23 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm8 := mul_nonneg (sub_nonneg.mpr hc8) (pow_nonneg hx 8)
  have hc9 : (-200 : ℝ) ≤ -1 := by
    linarith only [ht, ht1, h2lo, h2hi, h3lo, h3hi]
  have hm9 := mul_nonneg (sub_nonneg.mpr hc9) (pow_nonneg hx 9)
  unfold stripD3
  have hxpow : x ^ 5 ≤ (1 / 3 : ℝ) ^ 5 := pow_le_pow_left₀ hx hx1 5
  have hg : 1 + x + x ^ 2 + x ^ 3 + x ^ 4 ≤ 3 / 2 := by
    linarith only [strip_geom hx hx1, pow_nonneg hx 5]
  have hp0 : x ^ 5 * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) ≤ (1 / 3 : ℝ) ^ 5 * (3 / 2) :=
    mul_le_mul hxpow hg (by positivity) (by positivity)
  have hp : 0 ≤ 40 - 200 * x ^ 5 * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) := by
    norm_num at hp0
    linarith only [hp0]
  linear_combination hc0 + hm1 + hm2 + hm3 + hm4 + hm5 + hm6 + hm7 + hm8 + hm9 + hp

private theorem stripSC0_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC0 t x) (x ^ 2 * stripD0 t x) t := by
  let p : Polynomial ℝ :=
    Polynomial.C (-12 * x ^ 7 - 76 * x ^ 6 - 224 * x ^ 5 - 352 * x ^ 4 - 288 * x ^ 3 - 96 * x ^ 2) *
      Polynomial.X
    + Polynomial.C (24 * x ^ 7 + 144 * x ^ 6 + 561 * x ^ 5 + 1215 * x ^ 4 + 1314 * x ^ 3 + 540 * x ^ 2) *
      Polynomial.X ^ 2
    + Polynomial.C (-12 * x ^ 7 - 10 * x ^ 6 - 250 * x ^ 5 - 1124 * x ^ 4 - 1664 * x ^ 3 - 792 * x ^ 2) *
      Polynomial.X ^ 3
    + Polynomial.C (-58 * x ^ 6 - 87 * x ^ 5 + 261 * x ^ 4 + 638 * x ^ 3 + 348 * x ^ 2) * Polynomial.X ^ 4
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC0]
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    norm_num [stripD0]
    ring

/-- The coefficient of `(q - 1)^0` increases along the scale strip. -/
theorem nsrSC0_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3)
    (ha : 1 / 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC0 a x ≤ nsrSC0 b x := by
  have hm : MonotoneOn (fun t => nsrSC0 t x) (Set.Icc (1 / 3) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (stripSC0_deriv t x).continuousAt.continuousWithinAt)
      (fun t ht => (stripSC0_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD0_nonneg ht.1.le ht.2.le hx hx1
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripSC1_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC1 t x) (x * stripD1 t x) t := by
  let p : Polynomial ℝ :=
    Polynomial.C (8 * x ^ 4 + 4 * x ^ 3 - 40 * x ^ 2 - 48 * x)
    + Polynomial.C (-16 * x ^ 8 - 186 * x ^ 7 - 814 * x ^ 6 - 1836 * x ^ 5 - 2292 * x ^ 4 - 1468 * x ^ 3 -
      248 * x ^ 2 + 144 * x) * Polynomial.X
    + Polynomial.C (28 * x ^ 8 + 288 * x ^ 7 + 1253 * x ^ 6 + 6461 * x ^ 5 / 2 + 9861 * x ^ 4 / 2 + 3947 * x
      ^ 3 + 978 * x ^ 2 - 288 * x) * Polynomial.X ^ 2
    + Polynomial.C (-12 * x ^ 8 - 15 * x ^ 7 + 344 * x ^ 6 + 998 * x ^ 5 + 877 * x ^ 4 + 562 * x ^ 3 + 1224
      * x ^ 2 + 888 * x) * Polynomial.X ^ 3
    + Polynomial.C (-87 * x ^ 7 - 783 * x ^ 6 - 4785 * x ^ 5 / 2 - 7047 * x ^ 4 / 2 - 3045 * x ^ 3 - 1914 *
      x ^ 2 - 696 * x) * Polynomial.X ^ 4
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC1]
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    norm_num [stripD1]
    ring

/-- The coefficient of `(q - 1)^1` increases along the scale strip. -/
theorem nsrSC1_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3)
    (ha : 1 / 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC1 a x ≤ nsrSC1 b x := by
  have hm : MonotoneOn (fun t => nsrSC1 t x) (Set.Icc (1 / 3) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (stripSC1_deriv t x).continuousAt.continuousWithinAt)
      (fun t ht => (stripSC1_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD1_nonneg ht.1.le ht.2.le hx hx1
    positivity
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripSC2_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC2 t x) (stripD2 t x) t := by
  let p : Polynomial ℝ :=
    Polynomial.C (6 * x ^ 5 + 34 * x ^ 4 + 38 * x ^ 3 - 44 * x ^ 2 - 72 * x)
    + Polynomial.C (-6 * x ^ 9 - 90 * x ^ 8 - 564 * x ^ 7 - 1862 * x ^ 6 - 3514 * x ^ 5 - 3816 * x ^ 4 -
      2144 * x ^ 3 - 304 * x ^ 2 + 144 * x - 48) * Polynomial.X
    + Polynomial.C (36 * x ^ 8 + 312 * x ^ 7 + 2427 * x ^ 6 / 2 + 2694 * x ^ 5 + 6747 * x ^ 4 / 2 + 1905 * x
      ^ 3 - 174 * x ^ 2 - 384 * x + 96) * Polynomial.X ^ 2
    + Polynomial.C (-18 * x ^ 8 + 42 * x ^ 7 + 913 * x ^ 6 + 3262 * x ^ 5 + 5627 * x ^ 4 + 5870 * x ^ 3 +
      3996 * x ^ 2 + 1248 * x - 96) * Polynomial.X ^ 3
    + Polynomial.C (-261 * x ^ 7 / 2 - 2059 * x ^ 6 / 2 - 3045 * x ^ 5 - 8613 * x ^ 4 / 2 - 5887 * x ^ 3 / 2
      - 609 * x ^ 2 + 522 * x + 348) * Polynomial.X ^ 4
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC2]
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    norm_num [stripD2]
    ring

/-- The coefficient of `(q - 1)^2` increases along the scale strip. -/
theorem nsrSC2_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3)
    (ha : 1 / 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC2 a x ≤ nsrSC2 b x := by
  have hm : MonotoneOn (fun t => nsrSC2 t x) (Set.Icc (1 / 3) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (stripSC2_deriv t x).continuousAt.continuousWithinAt)
      (fun t ht => (stripSC2_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD2_nonneg ht.1.le ht.2.le hx hx1
    exact hd
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

private theorem stripSC3_deriv (t x : ℝ) :
    HasDerivAt (fun t => nsrSC3 t x) (stripD3 t x) t := by
  let p : Polynomial ℝ :=
    Polynomial.C (5 * x ^ 5 + 29 * x ^ 4 + 54 * x ^ 3 + 28 * x ^ 2 - 8 * x)
    + Polynomial.C (-x ^ 9 - 23 * x ^ 8 - 171 * x ^ 7 - 611 * x ^ 6 - 1194 * x ^ 5 - 1305 * x ^ 4 - 711 * x
      ^ 3 - 66 * x ^ 2 + 76 * x - 8) * Polynomial.X
    + Polynomial.C (17 * x ^ 8 + 141 * x ^ 7 + 1019 * x ^ 6 / 2 + 1975 * x ^ 5 / 2 + 1002 * x ^ 4 + 346 * x
      ^ 3 - 216 * x ^ 2 - 120 * x + 48) * Polynomial.X ^ 2
    + Polynomial.C (-6 * x ^ 8 + 167 * x ^ 7 / 4 + 2143 * x ^ 6 / 4 + 7843 * x ^ 5 / 4 + 14477 * x ^ 4 / 4 +
      7615 * x ^ 3 / 2 + 2259 * x ^ 2 + 550 * x - 48) * Polynomial.X ^ 3
    + Polynomial.C (-87 * x ^ 7 / 2 - 1247 * x ^ 6 / 4 - 3219 * x ^ 5 / 4 - 3045 * x ^ 4 / 4 + 1131 * x ^ 3
      / 4 + 2349 * x ^ 2 / 2 + 957 * x + 290) * Polynomial.X ^ 4
  convert p.hasDerivAt t using 1
  · funext z; simp [p, nsrSC3]
  · simp only [p, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
      Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    norm_num [stripD3]
    ring

/-- The coefficient of `(q - 1)^3` increases along the scale strip. -/
theorem nsrSC3_mono {x a b : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3)
    (ha : 1 / 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) : nsrSC3 a x ≤ nsrSC3 b x := by
  have hm : MonotoneOn (fun t => nsrSC3 t x) (Set.Icc (1 / 3) (2 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (stripSC3_deriv t x).continuousAt.continuousWithinAt)
      (fun t ht => (stripSC3_deriv t x).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hd := stripD3_nonneg ht.1.le ht.2.le hx hx1
    exact hd
  exact hm ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

end SmoothedOctagon
