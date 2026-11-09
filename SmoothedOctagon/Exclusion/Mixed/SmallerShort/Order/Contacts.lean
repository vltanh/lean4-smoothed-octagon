module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Smaller-short window: certificates of the order contacts

The logarithm bounds and the polynomial identities behind the contact inequalities of
`SmallerShort/Order.lean` (the Padé gap, the strong lower order and the rational
quadratic order). Every identity is a
two-variable rational identity checked by `field_simp`/`ring`; every sign is a positive Bernstein
form, a termwise bound or a one-sign-change row.

## Main API

* `ord_log_lt_pade3` (strict Padé).
* `ord_bern4_pos`: positivity of a quartic Bernstein form.
* Strong contact: the quartic `ordSP`, `ord_strong_eq` (the factored contact function),
  `ord_strong_bern` (its
  Bernstein form on `[q_min, 1]`, without `x ≤ 9`).
* Quadratic contact: the rows `ordQ0`, …, `ordQ7` of the table and their signs `ord_row0`, …,
  `ord_row7`, `ord_quad_Q_nonneg`, `ord_quad_eq` (the cleared contact function is `d Q(d, x)`).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- Strict Padé: `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` for `z > 1`. -/
theorem ord_log_lt_pade3 {z : ℝ} (hz : 1 < z) :
    Real.log z < (z - 1) * (z ^ 2 + 10 * z + 1) / (6 * z * (z + 1)) := by
  have h := ss_lt_of_deriv
    (f := fun t => (t - 1) * (t ^ 2 + 10 * t + 1) / (6 * t * (t + 1)) - Real.log t)
    (f' := fun t => (t - 1) ^ 4 / (6 * t ^ 2 * (t + 1) ^ 2)) hz (fun t ht => ?_)
    (fun t ht => by
      have : 0 < t - 1 := by linarith [ht.1]
      have : 0 < t := by linarith [ht.1]
      positivity)
  · simp only [sub_self, zero_mul, zero_div, Real.log_one] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have h1 : HasDerivAt (fun t : ℝ => (t - 1) * (t ^ 2 + 10 * t + 1))
      (3 * t ^ 2 + 18 * t - 9) t := by
    have := ((hasDerivAt_id' t).sub_const 1).mul
      ((((hasDerivAt_id' t).mul (hasDerivAt_id' t)).add
        ((hasDerivAt_id' t).const_mul 10)).add_const 1)
    convert this using 1
    · funext s; simp only [Pi.mul_apply, Pi.add_apply]; ring
    · simp only [Pi.mul_apply, Pi.add_apply]; ring
  have h2 : HasDerivAt (fun t : ℝ => 6 * t * (t + 1)) (12 * t + 6) t := by
    have := ((hasDerivAt_id' t).const_mul 6).mul ((hasDerivAt_id' t).add_const 1)
    convert this using 1
    · ring
  have := (h1.div h2 (by positivity)).sub (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- A quartic Bernstein form with positive end coefficients and nonnegative inner ones is positive
on `T, S ≥ 0`, `T + S > 0`. -/
theorem ord_bern4_pos {T S b0 b1 b2 b3 b4 : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hTS : 0 < T + S)
    (h0 : 0 < b0) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (h3 : 0 ≤ b3) (h4 : 0 < b4) :
    0 < b0 * S ^ 4 + b1 * T * S ^ 3 + b2 * T ^ 2 * S ^ 2 + b3 * T ^ 3 * S + b4 * T ^ 4 := by
  have e1 : 0 ≤ b1 * T * S ^ 3 := by positivity
  have e2 : 0 ≤ b2 * T ^ 2 * S ^ 2 := by positivity
  have e3 : 0 ≤ b3 * T ^ 3 * S := by positivity
  rcases hS.lt_or_eq with hS' | hS'
  · have : 0 < b0 * S ^ 4 := by positivity
    have : 0 ≤ b4 * T ^ 4 := by positivity
    linarith
  · subst hS'
    have hT' : 0 < T := by linarith
    have : 0 < b4 * T ^ 4 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      zero_add] at *
    linarith

/-- The strong contact quartic `P(q, x) = -aq⁴ + bq³ - cq² + dq - e`. -/
noncomputable def ordSP (x q : ℝ) : ℝ :=
  -(860 * x ^ 4 + 1096 * x ^ 3 + 92 * x ^ 2) * q ^ 4 +
    (1432 * x ^ 5 + 2829 * x ^ 4 + 3321 * x ^ 3 + 583 * x ^ 2 + 27 * x) * q ^ 3 -
    (3210 * x ^ 5 + 12960 * x ^ 4 + 5523 * x ^ 3 + 787 * x ^ 2 + 47 * x + 1) * q ^ 2 +
    (8184 * x ^ 5 + 9883 * x ^ 4 + 8635 * x ^ 3 + 1821 * x ^ 2 + 145 * x + 4) * q -
    (2024 * x ^ 5 + 6498 * x ^ 4 + 3181 * x ^ 3 + 545 * x ^ 2 + 39 * x + 1)

/-- The strong contact function `F` factors as `x²(7x + 1)²F = (1 - q)(x + 1)P(q, x)`. -/
theorem ord_strong_eq {x q : ℝ} (hx : 1 < x) :
    x ^ 2 * (7 * x + 1) ^ 2 * ((7 * x + 1) * ((1 + (1 / x + ssKs x * (1 - q))) *
        (6 + (1 / x + ssKs x * (1 - q)) - 5 * (1 / x + ssKs x * (1 - q)) * q - q ^ 2 - q)) *
        ((2 * q - (1 / x + ssKs x * (1 - q))) * x - q ^ 2) -
      4 * (x + 1) * q * (x - q) *
        (6 * ((1 / x + ssKs x * (1 - q)) + q + 2) * (1 - (1 / x + ssKs x * (1 - q)) * q) -
          (1 + (1 / x + ssKs x * (1 - q))) *
            (6 + (1 / x + ssKs x * (1 - q)) - 5 * (1 / x + ssKs x * (1 - q)) * q - q ^ 2 - q))) =
      (1 - q) * (x + 1) * ordSP x q := by
  have hx0 : 0 < x := by linarith
  unfold ssKs ordSP
  field_simp
  ring

/-- The Bernstein form of the strong contact quartic `P(q, x)` on
`[q_min, 1]`, in `T = x(11x + 5)q - (4x² + 11x + 1)` and `1 - q`. -/
theorem ord_strong_bern (x q : ℝ) : (7 * x + 1) ^ 3 * (x - 1) ^ 2 * ordSP x q =
      18 * (x + 1) ^ 2 * (7 * x + 1) * (11 * x + 1) * (15 * x + 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) *
          x ^ 2 * (1 - q) ^ 4 +
        (x + 1) * (15 * x + 1) *
            (82008 * x ^ 5 + 141569 * x ^ 4 + 62540 * x ^ 3 + 10134 * x ^ 2 + 692 * x + 17) * x *
          (x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1)) * (1 - q) ^ 3 +
        (x + 1) * (262098 * x ^ 5 + 211683 * x ^ 4 + 41340 * x ^ 3 + 2966 * x ^ 2 + 58 * x - 1) *
          (x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1)) ^ 2 * (1 - q) ^ 2 +
        2 * (10742 * x ^ 4 + 10397 * x ^ 3 + 1685 * x ^ 2 + 87 * x + 1) *
          (x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1)) ^ 3 * (1 - q) +
        2 * (313 * x ^ 2 + 38 * x + 1) * (x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1)) ^ 4 := by
  unfold ordSP
  ring

/-- Row 0 of the quadratic contact table: the coefficient `Q_0(d)` of `X^0` in `Q(d, 2 + X)`. -/
noncomputable def ordQ0 (d : ℝ) : ℝ :=
  36720 + 1629288 * d + 17492895 * d ^ 2 + 74741292 * d ^ 3 + 105796719 * d ^ 4 -
    166842396 * d ^ 5 - 727738209 * d ^ 6 - 852289776 * d ^ 7 - 354696408 * d ^ 8

/-- Row 1 of the quadratic contact table: the coefficient `Q_1(d)` of `X^1` in `Q(d, 2 + X)`. -/
noncomputable def ordQ1 (d : ℝ) : ℝ :=
  238626 + 8238690 * d + 83306538 * d ^ 2 + 360237447 * d ^ 3 + 635229657 * d ^ 4 -
    86528583 * d ^ 5 - 1858423950 * d ^ 6 - 2400943680 * d ^ 7 - 1020299220 * d ^ 8

/-- Row 2 of the quadratic contact table: the coefficient `Q_2(d)` of `X^2` in `Q(d, 2 + X)`. -/
noncomputable def ordQ2 (d : ℝ) : ℝ :=
  593592 + 17166666 * d + 163840779 * d ^ 2 + 705290757 * d ^ 3 + 1373526066 * d ^ 4 +
    605939586 * d ^ 5 - 1840319490 * d ^ 6 - 2832837468 * d ^ 7 - 1244301468 * d ^ 8

/-- Row 3 of the quadratic contact table: the coefficient `Q_3(d)` of `X^3` in `Q(d, 2 + X)`. -/
noncomputable def ordQ3 (d : ℝ) : ℝ :=
  756714 + 19160832 * d + 173117946 * d ^ 2 + 734815226 * d ^ 3 + 1501754180 * d ^ 4 +
    1093860788 * d ^ 5 - 819809180 * d ^ 6 - 1801734292 * d ^ 7 - 832609260 * d ^ 8

/-- Row 4 of the quadratic contact table: the coefficient `Q_4(d)` of `X^4` in `Q(d, 2 + X)`. -/
noncomputable def ordQ4 (d : ℝ) : ℝ :=
  543312 + 12411244 * d + 106539549 * d ^ 2 + 443438138 * d ^ 3 + 926686305 * d ^ 4 +
    822274086 * d ^ 5 - 92531309 * d ^ 6 - 659469924 * d ^ 7 - 329457820 * d ^ 8

/-- Row 5 of the quadratic contact table: the coefficient `Q_5(d)` of `X^5` in `Q(d, 2 + X)`. -/
noncomputable def ordQ5 (d : ℝ) : ℝ :=
  222422 + 4681266 * d + 38321998 * d ^ 2 + 155892919 * d ^ 3 + 328222643 * d ^ 4 +
    321672435 * d ^ 5 + 55204082 * d ^ 6 - 136079836 * d ^ 7 - 76886224 * d ^ 8

/-- Row 6 of the quadratic contact table: the coefficient `Q_6(d)` of `X^6` in `Q(d, 2 + X)`. -/
noncomputable def ordQ6 (d : ℝ) : ℝ :=
  48520 + 955170 * d + 7482521 * d ^ 2 + 29687685 * d ^ 3 + 62391462 * d ^ 4 + 64565076 * d ^ 5 +
    20939672 * d ^ 6 - 14040576 * d ^ 7 - 9764480 * d ^ 8

/-- Row 7 of the quadratic contact table: the coefficient `Q_7(d)` of `X^7` in `Q(d, 2 + X)`. -/
noncomputable def ordQ7 (d : ℝ) : ℝ :=
  4382 + 81580 * d + 613358 * d ^ 2 + 2369976 * d ^ 3 + 4939992 * d ^ 4 + 5266560 * d ^ 5 +
    2182912 * d ^ 6 - 495616 * d ^ 7 - 518144 * d ^ 8

/-- `Q_0(d) ≥ 0` on `[0, 9/20]`: the coefficients change sign once, after `d^4`, so
`b^4 Q_0(d) ≥ d^4 Q_0(b)` termwise, and
`Q_0(9/20) = 8187154568095419/3200000000`. -/
theorem ord_row0 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (9 / 20 : ℝ)) : 0 ≤ ordQ0 d := by
  unfold ordQ0
  have hQb : 0 ≤ d ^ 4 * (8187154568095419 / 3200000000 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4))]

/-- `Q_1(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^4`, so
`b^4 Q_1(d) ≥ d^4 Q_1(b)` termwise, and
`Q_1(1/2) = 3547605195/64`. -/
theorem ord_row1 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ1 d := by
  unfold ordQ1
  have hQb : 0 ≤ d ^ 4 * (3547605195 / 64 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4))]

/-- `Q_2(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^5`, so
`b^5 Q_2(d) ≥ d^5 Q_2(b)` termwise, and
`Q_2(1/2) = 11989271565/64`. -/
theorem ord_row2 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ2 d := by
  unfold ordQ2
  have hQb : 0 ≤ d ^ 5 * (11989271565 / 64 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3))]

/-- `Q_3(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^5`, so
`b^5 Q_3(d) ≥ d^5 Q_3(b)` termwise, and
`Q_3(1/2) = 15575894919/64`. -/
theorem ord_row3 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ3 d := by
  unfold ordQ3
  have hQb : 0 ≤ d ^ 5 * (15575894919 / 64 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3))]

/-- `Q_4(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^5`, so
`b^5 Q_4(d) ≥ d^5 Q_4(b)` termwise, and
`Q_4(1/2) = 5265366165/32`. -/
theorem ord_row4 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ4 d := by
  unfold ordQ4
  have hQb : 0 ≤ d ^ 5 * (5265366165 / 32 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3))]

/-- `Q_5(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^6`, so
`b^6 Q_5(d) ≥ d^6 Q_5(b)` termwise, and
`Q_5(1/2) = 1974254445/32`. -/
theorem ord_row5 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ5 d := by
  unfold ordQ5
  have hQb : 0 ≤ d ^ 6 * (1974254445 / 32 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 6)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2))]

/-- `Q_6(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^6`, so
`b^6 Q_6(d) ≥ d^6 Q_6(b)` termwise, and
`Q_6(1/2) = 48816675/4`. -/
theorem ord_row6 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ6 d := by
  unfold ordQ6
  have hQb : 0 ≤ d ^ 6 * (48816675 / 4 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 6)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2))]

/-- `Q_7(d) ≥ 0` on `[0, 1/2]`: the coefficients change sign once, after `d^6`, so
`b^6 Q_7(d) ≥ d^6 Q_7(b)` termwise, and
`Q_7(1/2) = 996300/1`. -/
theorem ord_row7 {d : ℝ} (hd : 0 ≤ d) (hdb : d ≤ (1 / 2 : ℝ)) : 0 ≤ ordQ7 d := by
  unfold ordQ7
  have hQb : 0 ≤ d ^ 6 * (996300 : ℝ) := by positivity
  linarith [mul_nonneg (pow_nonneg hd 0) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 6)),
    mul_nonneg (pow_nonneg hd 1) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 5)),
    mul_nonneg (pow_nonneg hd 2) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 4)),
    mul_nonneg (pow_nonneg hd 3) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 3)),
    mul_nonneg (pow_nonneg hd 4) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2)),
    mul_nonneg (pow_nonneg hd 5) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 1)),
    mul_nonneg (pow_nonneg hd 6) (sub_nonneg.2 (pow_le_pow_left₀ hd hdb 2))]

/-- `Q(d, x) ≥ 0` on `2 ≤ x`, `0 ≤ d ≤ 9/20` (every row is nonnegative, `X = x - 2 ≥ 0`). -/
theorem ord_quad_Q_nonneg {x d : ℝ} (hx : 2 ≤ x) (hd : 0 ≤ d) (hd2 : d ≤ 9 / 20) :
    0 ≤ ordQ0 d + (x - 2) * ordQ1 d + (x - 2) ^ 2 * ordQ2 d + (x - 2) ^ 3 * ordQ3 d +
      (x - 2) ^ 4 * ordQ4 d + (x - 2) ^ 5 * ordQ5 d + (x - 2) ^ 6 * ordQ6 d +
      (x - 2) ^ 7 * ordQ7 d := by
  have hX : 0 ≤ x - 2 := by linarith
  have hd1 : d ≤ (1 / 2 : ℝ) := by linarith
  have r0 := ord_row0 hd hd2
  have r1 := mul_nonneg hX (ord_row1 hd hd1)
  have r2 := mul_nonneg (pow_nonneg hX 2) (ord_row2 hd hd1)
  have r3 := mul_nonneg (pow_nonneg hX 3) (ord_row3 hd hd1)
  have r4 := mul_nonneg (pow_nonneg hX 4) (ord_row4 hd hd1)
  have r5 := mul_nonneg (pow_nonneg hX 5) (ord_row5 hd hd1)
  have r6 := mul_nonneg (pow_nonneg hX 6) (ord_row6 hd hd1)
  have r7 := mul_nonneg (pow_nonneg hX 7) (ord_row7 hd hd1)
  linarith

/-- The cleared quadratic contact function is `d Q(d, x)`, with `Q(d, 2 + X) = Σ Xᵏ Q_k(d)` (the
8 × 9 table of the rows `ordQ0`, …, `ordQ7`). -/
theorem ord_quad_eq {x d c q p N W : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hc : c = (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1)) (hq : q = 1 / (1 + d))
    (hp : p = (1 + c * d + d ^ 2 / (1 + 4 * d)) / (x * (1 + d)))
    (hN : N = (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q))
    (hW : W = 6 * (p + q + 2) * (1 - p * q)) :
    x ^ 3 * (1 + d) ^ 5 * (1 + 4 * d) ^ 4 * (7 * x + 1) ^ 3 *
      (N * ((2 * q - p) * x - q ^ 2) -
        (x - q) * (W - N) * ((c + d * (2 + 4 * d) / (1 + 4 * d) ^ 2) / x - p)) =
    d * (ordQ0 d + (x - 2) * ordQ1 d + (x - 2) ^ 2 * ordQ2 d + (x - 2) ^ 3 * ordQ3 d +
      (x - 2) ^ 4 * ordQ4 d + (x - 2) ^ 5 * ordQ5 d + (x - 2) ^ 6 * ordQ6 d +
      (x - 2) ^ 7 * ordQ7 d) := by
  subst hN hW hp hq hc
  unfold ordQ0 ordQ1 ordQ2 ordQ3 ordQ4 ordQ5 ordQ6 ordQ7
  have h1 : 1 + d ≠ 0 := by positivity
  have h2 : 1 + 4 * d ≠ 0 := by positivity
  have h3 : 7 * x + 1 ≠ 0 := by positivity
  field_simp
  ring

end SmoothedOctagon
