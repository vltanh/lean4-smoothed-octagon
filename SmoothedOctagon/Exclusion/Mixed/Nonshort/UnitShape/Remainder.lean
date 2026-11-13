module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# The quadratic remainder on the unit face

The remaining combination in the cubic decomposition is concave in
the order gap. Its lower edge is the order edge or `t = 3/8`; its
upper edge is the switching edge or `t = 0`. Elementary one-variable
bounds prove positivity on all four edges.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

private def rem0 {R : Type*} [CommRing R] (x : R) : R :=
  36 * x ^ 8 + 279 * x ^ 7 + 993 * x ^ 6 + 1761 * x ^ 5 + 1357 * x ^ 4
    + 40 * x ^ 3 - 428 * x ^ 2 + 132 * x + 320

private def rem1 {R : Type*} [CommRing R] (x : R) : R :=
  108 * x ^ 9 + 825 * x ^ 8 + 2487 * x ^ 7 + 4461 * x ^ 6 + 6021 * x ^ 5
    + 6518 * x ^ 4 + 4972 * x ^ 3 + 1688 * x ^ 2 - 300 * x - 120

private def rem2 {R : Type*} [CommRing R] (x : R) : R :=
  108 * x ^ 9 + 837 * x ^ 8 + 2079 * x ^ 7 + 2175 * x ^ 6 + 579 * x ^ 5
    - 1436 * x ^ 4 - 2848 * x ^ 3 - 2456 * x ^ 2 - 804 * x - 24

private def rem3 {R : Type*} [CommRing R] (x : R) : R :=
  36 * x ^ 8 + 255 * x ^ 7 + 378 * x ^ 6 - 351 * x ^ 5 - 1286 * x ^ 4
    - 964 * x ^ 3 + 12 * x ^ 2 + 296 * x + 96

private theorem remainder_eq (x r : ℝ) :
    remainder x r = 3 * x * (1 + x) ^ 2 * rem0 x + 3 * (1 + x) * rem1 x * r
      + 3 * rem2 x * r ^ 2 + 3 * rem3 x * r ^ 3 := by
  unfold remainder value cross leading constant value0 value1 value2 value3
    cross0 cross1 cross2 cross3 lead0 lead1 lead2 lead3 rem0 rem1 rem2 rem3
  ring

private theorem remainder_curvature {x r : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hr : 0 ≤ r) (hrx : r ≤ x * (1 + x)) : rem2 x + 3 * r * rem3 x ≤ 0 := by
  have h54 := pow_le_pow_of_le_one hx hx1 (by norm_num : (4 : ℕ) ≤ 5)
  have h64 := pow_le_pow_of_le_one hx hx1 (by norm_num : (4 : ℕ) ≤ 6)
  have h74 := pow_le_pow_of_le_one hx hx1 (by norm_num : (4 : ℕ) ≤ 7)
  have h84 := pow_le_pow_of_le_one hx hx1 (by norm_num : (4 : ℕ) ≤ 8)
  have h94 := pow_le_pow_of_le_one hx hx1 (by norm_num : (4 : ℕ) ≤ 9)
  have h43 := pow_le_pow_of_le_one hx hx1 (by norm_num : (3 : ℕ) ≤ 4)
  have h32 := pow_le_pow_of_le_one hx hx1 (by norm_num : (2 : ℕ) ≤ 3)
  have h2 : rem2 x ≤ -24 - 804 * x - 962 * x ^ 2 := by
    unfold rem2
    linarith only [h54, h64, h74, h84, h94, h43, h32]
  have h3 : rem3 x ≤ 96 + 296 * x + 12 * x ^ 2 - 964 * x ^ 3 - 617 * x ^ 4 := by
    unfold rem3
    linarith only [h64, h74, h84, pow_nonneg hx 5]
  by_cases h3n : rem3 x ≤ 0
  · have hp := mul_nonpos_of_nonneg_of_nonpos hr h3n
    nlinarith only [h2, hp, hx, sq_nonneg x]
  have h3p : 0 ≤ rem3 x := le_of_lt (lt_of_not_ge h3n)
  have hcap := mul_le_mul_of_nonneg_right hrx h3p
  have hcap' := mul_le_mul_of_nonneg_left h3 (show 0 ≤ x * (1 + x) by positivity)
  have hb : -24 - 516 * x + 214 * x ^ 2 + 924 * x ^ 3 - 2856 * x ^ 4
      - 4743 * x ^ 5 - 1851 * x ^ 6 ≤ 0 := by
    by_cases hhalf : x ≤ 1 / 2
    · have h2' : x ^ 2 ≤ x / 2 := by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hhalf)]
      have h3' : x ^ 3 ≤ x / 4 := by
        have := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hhalf)
        nlinarith only [this, h2']
      linarith only [h2', h3', hx, pow_nonneg hx 4, pow_nonneg hx 5, pow_nonneg hx 6]
    · have hhalf : 1 / 2 ≤ x := le_of_lt (lt_of_not_ge hhalf)
      have h2' := pow_le_pow_of_le_one hx hx1 (by norm_num : (1 : ℕ) ≤ 2)
      have h4' : x ^ 3 / 2 ≤ x ^ 4 := by
        nlinarith only [mul_nonneg (pow_nonneg hx 3) (sub_nonneg.mpr hhalf)]
      norm_num only [pow_one] at h2'
      linarith only [h2', h4', hx, pow_nonneg hx 3, pow_nonneg hx 5, pow_nonneg hx 6]
  nlinarith only [h2, hcap, hcap', hb]

private def capRem {R : Type*} [CommRing R] (x : R) : R :=
  -1152 * x ^ 9 - 20412 * x ^ 8 - 146925 * x ^ 7 - 442998 * x ^ 6 - 636123 * x ^ 5
    - 366054 * x ^ 4 + 50412 * x ^ 3 + 113932 * x ^ 2 + 18136 * x - 1920

private theorem cap_rem_pos {x : ℝ} (hx : 1 / 10 ≤ x) (hx1 : x ≤ 1 / 4) : 0 < capRem x := by
  let p : Polynomial ℝ := capRem Polynomial.X
  have hm := polynomial_mono (p := p) hx (by
    intro z hz hz1
    have hz0 : 0 ≤ z := by linarith only [hz]
    have hzq : z ≤ 1 / 4 := hz1.trans hx1
    have charge (n : ℕ) : z ^ (n + 1) ≤ z * (1 / 4 : ℝ) ^ n := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hzq n) hz0
      simpa [pow_add, mul_comm] using this
    have h3 := charge 2
    have h4 := charge 3
    have h5 := charge 4
    have h6 := charge 5
    have h7 := charge 6
    have h8 := charge 7
    norm_num [p, capRem, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [h3, h4, h5, h6, h7, h8, hz0, sq_nonneg z])
  have hp : 0 < p.eval (1 / 10) := by norm_num [p, capRem]
  have he : p.eval x = capRem x := by simp [p, capRem]
  linarith only [hm, hp, he]

private theorem remainder_lower {x : ℝ} (hx : 1 / 10 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ remainder x (max 0 (1 / 4 - x)) := by
  have hx0 : 0 < x := by linarith only [hx]
  by_cases hq : 1 / 4 ≤ x
  · rw [max_eq_left (by linarith only [hq]), remainder_eq]
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), add_zero]
    have he : rem0 x = 36 * x ^ 8 + 279 * x ^ 7 + 993 * x ^ 6 + 1761 * x ^ 5
        + 1357 * x ^ 4 + 40 * x ^ 3 + 320 * (1 - x) + 24 * x + 428 * x * (1 - x) := by
      unfold rem0; ring
    rw [he]
    have : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    positivity
  · have hxq : x ≤ 1 / 4 := le_of_lt (lt_of_not_ge hq)
    rw [max_eq_right (by linarith only [hxq])]
    have hp := cap_rem_pos hx hxq
    have he : 64 * remainder x (1 / 4 - x) = 3 * capRem x := by
      rw [remainder_eq]
      unfold rem0 rem1 rem2 rem3 capRem
      ring
    linarith only [he, hp]

private theorem remainder_upper {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ remainder x (min (x * (1 + x)) (1 - x)) := by
  by_cases hswitch : x * (1 + x) ≤ 1 - x
  · rw [min_eq_left hswitch]
    have he : remainder x (x * (1 + x)) = 3 * x * (1 + x) ^ 2 *
        (36 * x ^ 11 + 399 * x ^ 10 + 1578 * x ^ 9 + 2967 * x ^ 8 + 3304 * x ^ 7
          + 3783 * x ^ 6 + 5394 * x ^ 5 + 5335 * x ^ 4 + 2948 * x ^ 3
          + 552 * x ^ 2 - 192 * x + 200) := by
      rw [remainder_eq]
      unfold rem0 rem1 rem2 rem3
      ring
    have hp : 0 ≤ 36 * x ^ 11 + 399 * x ^ 10 + 1578 * x ^ 9 + 2967 * x ^ 8
        + 3304 * x ^ 7 + 3783 * x ^ 6 + 5394 * x ^ 5 + 5335 * x ^ 4
        + 2948 * x ^ 3 + 552 * x ^ 2 := by positivity
    rw [he]
    apply mul_nonneg (by positivity)
    linarith only [hp, hx1]
  · have hswitch : 1 - x ≤ x * (1 + x) := le_of_lt (lt_of_not_ge hswitch)
    have hxlo : 2 / 5 ≤ x := by
      by_contra h
      have h : x < 2 / 5 := lt_of_not_ge h
      nlinarith only [hswitch, mul_nonneg hx.le (show 0 ≤ 2 / 5 - x by linarith only [h])]
    rw [min_eq_right hswitch]
    have he : remainder x (1 - x) =
        24 * (72 * x ^ 6 + 408 * x ^ 5 + 912 * x ^ 4 + 810 * x ^ 3
          + 140 * x ^ 2 - 91 * x - 6) := by
      rw [remainder_eq]
      unfold rem0 rem1 rem2 rem3
      ring
    have h2 : 2 / 5 * x ≤ x ^ 2 := by nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hxlo)]
    have h3 : 2 / 5 * x ^ 2 ≤ x ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxlo)]
    have hp : 0 ≤ 72 * x ^ 6 + 408 * x ^ 5 + 912 * x ^ 4 := by positivity
    rw [he]
    nlinarith only [hp, h2, h3, hxlo]

theorem remainder_nonneg {x r : ℝ} (hx : 1 / 10 ≤ x) (hr : 0 ≤ r)
    (hr0 : 1 / 4 - x ≤ r) (hrx : r ≤ x * (1 + x)) (hr1 : r ≤ 1 - x) :
    0 ≤ remainder x r := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : x ≤ 1 := by linarith only [hr, hr1]
  let a := max 0 (1 / 4 - x)
  let b := min (x * (1 + x)) (1 - x)
  let p : Polynomial ℝ := Polynomial.C (3 * x * (1 + x) ^ 2 * rem0 x)
    + Polynomial.C (3 * (1 + x) * rem1 x) * Polynomial.X
    + Polynomial.C (3 * rem2 x) * Polynomial.X ^ 2
    + Polynomial.C (3 * rem3 x) * Polynomial.X ^ 3
  have he (z : ℝ) : p.eval z = remainder x z := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    rw [remainder_eq]
  have har : a ≤ r := max_le hr hr0
  have hrb : r ≤ b := le_min hrx hr1
  have hc : ∀ z, a ≤ z → z ≤ b → p.derivative.derivative.eval z ≤ 0 := by
    intro z hz hz1
    have hz0 : 0 ≤ z := (le_max_left _ _).trans hz
    have hzW : z ≤ x * (1 + x) := hz1.trans (min_le_left _ _)
    have hp := remainder_curvature hx0.le hx1 hz0 hzW
    norm_num [p, Polynomial.derivative_mul, Polynomial.derivative_pow]
    linarith only [hp]
  have hmin := polynomial_floor (p := p) (m := 0) har hrb hc
    (by rw [he]; exact remainder_lower hx hx1)
    (by rw [he]; exact remainder_upper hx0 hx1)
  rwa [he] at hmin

end SmoothedOctagon.UnitShape
