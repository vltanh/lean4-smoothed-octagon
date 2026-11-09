module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Reciprocal bounds and quadratic bridge contacts

The strict Simpson bound for the reciprocal integral gives the endpoint-gap
majorant used by the affine and quadratic lower barriers. The remaining
quadratic contact table and its row signs are recorded here.
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

/-- **The Padé gap**: for
`0 < p < q ≤ 1`, `η = avg(p, q) - g(q) > η₀ = (q - p)(6 + p - 5pq - q² - q)/(6(1 + p)(1 + q)²(p + q +
2))` (strict `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` at `z = (1 + q)/(1 + p)`). -/
theorem ss_pade_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) <
      m2Sec p 1 q - ss_gB 1 q := by
  have hq1 : q ≤ 1 := hq
  have hq0 : 0 < q := by linarith
  have hz : 1 < (q + 1) / (p + 1) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hlog := ord_log_lt_pade3 hz
  rw [m2Sec_of_ne hpq.ne]
  have hqp : 0 < q - p := by linarith
  have k : 1 / (q - p) * Real.log ((q + 1) / (p + 1)) <
      1 / (q - p) * (((q + 1) / (p + 1) - 1) *
        (((q + 1) / (p + 1)) ^ 2 + 10 * ((q + 1) / (p + 1)) + 1) /
          (6 * ((q + 1) / (p + 1)) * ((q + 1) / (p + 1) + 1))) :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  have e : 1 / (q - p) * (((q + 1) / (p + 1) - 1) *
      (((q + 1) / (p + 1)) ^ 2 + 10 * ((q + 1) / (p + 1)) + 1) /
        (6 * ((q + 1) / (p + 1)) * ((q + 1) / (p + 1) + 1))) =
      (p ^ 2 + 10 * p * q + 12 * p + q ^ 2 + 12 * q + 12) /
        (6 * (p + 1) * (q + 1) * (p + q + 2)) := by
    have : p + 1 ≠ 0 := by positivity
    have : q + 1 ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at k
  have e2 : 1 + 1 ^ 2 / ((p + 1) * (q + 1)) -
      (p ^ 2 + 10 * p * q + 12 * p + q ^ 2 + 12 * q + 12) /
        (6 * (p + 1) * (q + 1) * (p + q + 2)) - ss_gB 1 q =
      (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) := by
    unfold ss_gB
    have : p + 1 ≠ 0 := by positivity
    have : q + 1 ≠ 0 := by positivity
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [← e2]
  linarith

/-- **The gap ratio from below**: for `0 < p < q ≤ 1`, with
`N = (1 + p)(6 + p - 5pq - q² - q)`, `W = 6(p + q + 2)(1 - pq)`, `η = avg - g(q)`, `ξ = g(p) - avg`:
`η/ξ > N/(W - N)`, in cleared form `N ξ < (W - N) η`. -/
theorem ss_gap_ratio_low {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - m2Sec p 1 q) <
      (6 * (p + q + 2) * (1 - p * q) - (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)) *
        (m2Sec p 1 q - ss_gB 1 q) := by
  have hq0 : 0 < q := by linarith
  have hgap := ss_pade_gap hp hpq hq
  have hpq1 : p * q < 1 := by have := mul_le_of_le_one_right hp.le hq; linarith
  have hW : 0 < 6 * (p + q + 2) * (1 - p * q) := by
    have : 0 < 1 - p * q := by linarith
    positivity
  have e : (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - ss_gB 1 q) =
      6 * (p + q + 2) * (1 - p * q) *
        ((q - p) * (6 + p - 5 * p * q - q ^ 2 - q) /
          (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2))) := by
    unfold ss_gB
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
    ring
  have := mul_lt_mul_of_pos_left hgap hW
  linarith

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
