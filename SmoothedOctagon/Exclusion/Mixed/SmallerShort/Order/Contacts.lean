module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Smaller-short window: certificates of the order contacts

The logarithm bounds and the polynomial identities behind the contact inequalities of
`SmallerShort/Order.lean` (the Padé gap, the strong lower order, the small-shape upper
order and the rational quadratic order). Every identity is a
two-variable rational identity checked by `field_simp`/`ring`; every sign is a positive Bernstein
form, a termwise bound or a one-sign-change row.

## Main API

* `ord_log_lt_pade3` (strict Padé).
* `ord_bern4_pos`: positivity of a quartic Bernstein form.
* Strong contact: the quartic `ordSP`, `ord_strong_eq` (the factored contact function),
  `ord_strong_bern` (its
  Bernstein form on `[q_min, 1]`, without `x ≤ 9`).
* Small-shape contact: `ord_ut_gaps`, `ord_sec_le_ut`, `ord_K_eq`,
  `ord_K_pos`.
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

/-- The two-term `artanh` majorant of the secant against its endpoints:
`g(p) - ũ` and `ũ - g(q)` in closed form. -/

theorem ord_ut_gaps {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ss_gB 1 p - (1 + 1 / ((1 + p) * (1 + q)) -
        (2 * ((q - p) / (2 + p + q)) + 2 / 3 * ((q - p) / (2 + p + q)) ^ 3) / (q - p)) =
      (q - p) * (12 + 14 * q + 5 * q ^ 2 + 10 * p - 4 * p * q - 8 * p * q ^ 2 - 3 * p * q ^ 3 -
        p ^ 2 - 14 * p ^ 2 * q - 4 * p ^ 2 * q ^ 2 - 2 * p ^ 3 - 5 * p ^ 3 * q) /
        (3 * (1 + p) ^ 2 * (1 + q) * (p + q + 2) ^ 3) ∧
    (1 + 1 / ((1 + p) * (1 + q)) -
        (2 * ((q - p) / (2 + p + q)) + 2 / 3 * ((q - p) / (2 + p + q)) ^ 3) / (q - p)) -
        ss_gB 1 q =
      (q - p) * (12 + 10 * q - q ^ 2 - 2 * q ^ 3 + 14 * p - 4 * p * q - 14 * p * q ^ 2 -
        5 * p * q ^ 3 + 5 * p ^ 2 - 8 * p ^ 2 * q - 4 * p ^ 2 * q ^ 2 - 3 * p ^ 3 * q) /
        (3 * (1 + p) * (1 + q) ^ 2 * (p + q + 2) ^ 3) := by
  have hq : 0 < q := by linarith
  have h1 : (1 + p) ≠ 0 := by positivity
  have h2 : (1 + q) ≠ 0 := by positivity
  have h3 : (2 + p + q) ≠ 0 := by positivity
  have h4 : (p + q + 2) ≠ 0 := by positivity
  have h5 : q - p ≠ 0 := by linarith
  unfold ss_gB
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The two-term `artanh` majorant: `avg(p, q) ≤ ũ` for `0 < p < q`
(`ss_log_ge_cubic` at `(1 + q)/(1 + p)`). -/
theorem ord_sec_le_ut {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    m2Sec p 1 q ≤ 1 + 1 / ((1 + p) * (1 + q)) -
      (2 * ((q - p) / (2 + p + q)) + 2 / 3 * ((q - p) / (2 + p + q)) ^ 3) / (q - p) := by
  have hq : 0 < q := hp.trans hpq
  have hqp : 0 < q - p := by linarith
  have hY : 1 ≤ (q + 1) / (p + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hlog := ss_log_ge_cubic hY
  have hw : ((q + 1) / (p + 1) - 1) / ((q + 1) / (p + 1) + 1) = (q - p) / (2 + p + q) := by
    have : p + 1 ≠ 0 := by positivity
    have : 2 + p + q ≠ 0 := by positivity
    field_simp
    ring
  rw [hw] at hlog
  rw [m2Sec_of_ne hpq.ne]
  have k := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 1 / (q - p))
  have e1 : (1:ℝ) ^ 2 / ((p + 1) * (q + 1)) = 1 / ((1 + p) * (1 + q)) := by ring
  have e2 : (2 * ((q - p) / (2 + p + q)) + 2 / 3 * ((q - p) / (2 + p + q)) ^ 3) / (q - p) =
      1 / (q - p) * (2 * ((q - p) / (2 + p + q)) + 2 / 3 * ((q - p) / (2 + p + q)) ^ 3) := by ring
  rw [e1, e2]
  linarith

/-- The polynomial `K(z, h)` of `ord_K_eq` is positive on the small-shape contact
domain. -/

theorem ord_K_pos {z h : ℝ} (hz : 0 < z) (hz7 : z ≤ 7 / 6) (hh : 0 ≤ h) (hh20 : h ≤ 1 / 20)
    (hhz : h * (z + 3) < z) :
    0 < -2 * z ^ 2 * (19 * z ^ 3 + 24 * z ^ 2 - 48 * z - 64) +
      6 * h * z ^ 2 * (7 * z ^ 3 - 31 * z ^ 2 - 92 * z - 48) +
      h ^ 2 * (10 * z ^ 5 + 303 * z ^ 4 + 450 * z ^ 3 + 248 * z ^ 2 - 96 * z - 384) +
      h ^ 3 * (-18 * z ^ 5 + 72 * z ^ 4 + 435 * z ^ 3 + 1178 * z ^ 2 + 2040 * z + 864) +
      h ^ 4 * (4 * z ^ 5 - 135 * z ^ 4 + 180 * z ^ 3 + 257 * z ^ 2 + 108 * z + 456) +
      h ^ 5 * (30 * z ^ 4 - 297 * z ^ 3 - 4 * z ^ 2 + 111 * z + 120) +
      6 * h ^ 6 * (11 * z ^ 3 - 20 * z ^ 2 + 19 * z + 6) + 32 * h ^ 7 * (z ^ 2 + 3) := by
  have hz0 := hz.le
  have hz2 : 0 < z ^ 2 := by positivity
  have hzz2 : z ^ 2 ≤ (7 / 6) ^ 2 := pow_le_pow_left₀ hz0 hz7 2
  have hzz3 : z ^ 3 ≤ (7 / 6) ^ 3 := pow_le_pow_left₀ hz0 hz7 3
  have hz3 := pow_nonneg hz0 3
  have hz4 := pow_nonneg hz0 4
  have hz5 := pow_nonneg hz0 5
  -- `h ≤ z/3`, `(h(z + 3))² ≤ z²` and `9h² ≤ z²`
  have hh3 : 3 * h ≤ z := by have := mul_nonneg hh hz0; linarith
  have hhsq : (h * (z + 3)) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (by positivity) hhz.le 2
  have hh2 : (3 * h) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (by positivity) hh3 2
  -- the nonnegative higher terms
  have t3 :
      0 ≤ h ^ 3 * (-18 * z ^ 5 + 72 * z ^ 4 + 435 * z ^ 3 + 1178 * z ^ 2 + 2040 * z + 864) := by
    have := mul_le_mul_of_nonneg_left hzz2 hz3
    have : 0 ≤ -18 * z ^ 5 + 72 * z ^ 4 + 435 * z ^ 3 + 1178 * z ^ 2 + 2040 * z + 864 := by
      linarith
    positivity
  have t4 :
      0 ≤ h ^ 4 * (4 * z ^ 5 - 135 * z ^ 4 + 180 * z ^ 3 + 257 * z ^ 2 + 108 * z + 456) := by
    have := mul_le_mul_of_nonneg_left hz7 hz3
    have : 0 ≤ 4 * z ^ 5 - 135 * z ^ 4 + 180 * z ^ 3 + 257 * z ^ 2 + 108 * z + 456 := by
      linarith
    positivity
  have t6 : 0 ≤ 6 * h ^ 6 * (11 * z ^ 3 - 20 * z ^ 2 + 19 * z + 6) := by
    have := mul_nonneg hz0 (sq_nonneg (z - 10 / 11))
    have : 0 ≤ 11 * z ^ 3 - 20 * z ^ 2 + 19 * z + 6 := by linarith
    positivity
  have t7 : 0 ≤ 32 * h ^ 7 * (z ^ 2 + 3) := by positivity
  -- `h⁵`: the coefficient is at least `-478`, and `478 h⁵ ≤ z²/100`
  have t5 : -(z ^ 2 / 100) ≤ h ^ 5 * (30 * z ^ 4 - 297 * z ^ 3 - 4 * z ^ 2 + 111 * z + 120) := by
    have hc : -478 ≤ 30 * z ^ 4 - 297 * z ^ 3 - 4 * z ^ 2 + 111 * z + 120 := by linarith
    have h5 : 0 ≤ h ^ 5 := by positivity
    have k1 := mul_le_mul_of_nonneg_left hc h5
    have hh35 : h ^ 3 ≤ (1 / 20) ^ 3 := pow_le_pow_left₀ hh hh20 3
    have k2 := mul_le_mul_of_nonneg_right hh35 (sq_nonneg h)
    linarith
  -- `h`: drop `42 h z⁵`, use `h ≤ 1/20`
  have t1 : -(3 / 10) * (z ^ 2 * (31 * z ^ 2 + 92 * z + 48)) ≤
      6 * h * z ^ 2 * (7 * z ^ 3 - 31 * z ^ 2 - 92 * z - 48) := by
    have hA : 0 ≤ z ^ 2 * (31 * z ^ 2 + 92 * z + 48) := by positivity
    have k1 := mul_le_mul_of_nonneg_right hh20 hA
    have k2 : 0 ≤ h * z ^ 5 := by positivity
    linarith
  -- `h²`: `(96z + 384)h² ≤ (128/3)(z + 3)²h² ≤ (128/3)z²`
  have t2 : -(128 / 3) * z ^ 2 ≤
      h ^ 2 * (10 * z ^ 5 + 303 * z ^ 4 + 450 * z ^ 3 + 248 * z ^ 2 - 96 * z - 384) := by
    have hpos : 0 ≤ h ^ 2 * (10 * z ^ 5 + 303 * z ^ 4 + 450 * z ^ 3 + 248 * z ^ 2) := by
      positivity
    have hle : 96 * z + 384 ≤ 128 / 3 * (z + 3) ^ 2 := by have := sq_nonneg z; linarith
    have k := mul_le_mul_of_nonneg_right hle (sq_nonneg h)
    linarith
  -- the cubic `J̃` is positive on `[0, 7/6]`
  have hJ : 0 < -38 * z ^ 3 - 573 / 10 * z ^ 2 + 342 / 5 * z + 21277 / 300 := by
    have k1 := mul_nonneg hz0 (by linarith : (0:ℝ) ≤ 7 / 6 - z)
    have k2 := mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ 7 / 6 - z)
    linarith
  have hJ2 : 0 < z ^ 2 * (-38 * z ^ 3 - 573 / 10 * z ^ 2 + 342 / 5 * z + 21277 / 300) :=
    mul_pos hz2 hJ
  linarith

/-- `K = x³[2q(x - q)(1 + q)b(p, q) - x M (1 + p)c(p, q)]` at the contact `p = (3 - 2q)/x`. -/
theorem ord_K_eq {z h : ℝ} (hz : 0 < z) :
    (1 + z) ^ 3 * (2 * (1 - h) * (1 + z - (1 - h)) * (1 + (1 - h)) *
        (12 + 14 * (1 - h) + 5 * (1 - h) ^ 2 + 10 * ((3 - 2 * (1 - h)) / (1 + z)) -
          4 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) -
          8 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) ^ 2 -
          3 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) ^ 3 - ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 -
          14 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 * (1 - h) -
          4 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 * (1 - h) ^ 2 -
          2 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 3 -
          5 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 3 * (1 - h)) -
      (1 + z) * (2 * (1 - h) * (1 + z + 1) - (1 - h) ^ 2 - 3) *
        (1 + (3 - 2 * (1 - h)) / (1 + z)) *
        (12 + 10 * (1 - h) - (1 - h) ^ 2 - 2 * (1 - h) ^ 3 + 14 * ((3 - 2 * (1 - h)) / (1 + z)) -
          4 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) -
          14 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) ^ 2 -
          5 * ((3 - 2 * (1 - h)) / (1 + z)) * (1 - h) ^ 3 +
          5 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 -
          8 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 * (1 - h) -
          4 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 2 * (1 - h) ^ 2 -
          3 * ((3 - 2 * (1 - h)) / (1 + z)) ^ 3 * (1 - h))) =
    -2 * z ^ 2 * (19 * z ^ 3 + 24 * z ^ 2 - 48 * z - 64) +
      6 * h * z ^ 2 * (7 * z ^ 3 - 31 * z ^ 2 - 92 * z - 48) +
      h ^ 2 * (10 * z ^ 5 + 303 * z ^ 4 + 450 * z ^ 3 + 248 * z ^ 2 - 96 * z - 384) +
      h ^ 3 * (-18 * z ^ 5 + 72 * z ^ 4 + 435 * z ^ 3 + 1178 * z ^ 2 + 2040 * z + 864) +
      h ^ 4 * (4 * z ^ 5 - 135 * z ^ 4 + 180 * z ^ 3 + 257 * z ^ 2 + 108 * z + 456) +
      h ^ 5 * (30 * z ^ 4 - 297 * z ^ 3 - 4 * z ^ 2 + 111 * z + 120) +
      6 * h ^ 6 * (11 * z ^ 3 - 20 * z ^ 2 + 19 * z + 6) + 32 * h ^ 7 * (z ^ 2 + 3) := by
  have : 1 + z ≠ 0 := by positivity
  field_simp
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
