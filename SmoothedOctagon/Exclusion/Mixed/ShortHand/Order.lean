module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hso.Barrier
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hso.Poly

/-!
# Hand proof of the smaller-short case: the equal-secant orders

The order relations between the shape coordinates `x = C/a`, `α = A/a`, `β = B/a` of a short bridge
with equal turn secants `Sec(1, x, β) = Sec(α, β, x)` (`MIXED_SMALLER_SHORT_STRONG_ORDER`,
`MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER`, `MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER`,
`MIXED_SMALLER_SHORT_RATIONAL_QUADRATIC_ORDER`; inventories HS-S01 M1-M9, HS-S3 R2-R5, HS-S4 R1-R8).
Route (inventory HS-S4 R1, HS-S01 M5): no equal-secant continuation; the barrier argument runs on
the normalized comparison function `Φ(z) = avg(ℓ + k(1 - z), z) - avg(ℓ, 1/z)` of `ss_order_norm`
with the first-contact lemma `hs_first_contact`; at a zero of `Φ` the sign of `Φ'` is the contact
inequality below. The barrier machinery (any differentiable barrier, so also the non-affine barrier
of `hs_quad_order`) is `Hso/Barrier.lean`; the polynomial certificates are `Hso/Poly.lean`.

## Main API

* Gap ratios: `hs_pade_gap` (`MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL` (3)), `hs_gap_ratio_low`
  (`STRONG_ORDER` (2)-(3)), `hs_chebyshev_gap` (`GLOBAL_UPPER_ORDER` (6)).
* Contact inequalities: `hs_strong_contact` (`STRONG_ORDER` (4)-(12)), `hs_upper_contact_54`,
  `hs_upper_contact_98` (`GLOBAL_UPPER_ORDER` (8)-(15)), `hs_small_contact` (inventory HS-S4 R6′),
  `hs_quad_contact` (`RATIONAL_QUADRATIC_ORDER` (3)-(10)).
* Orders: `hs_strong_order` (`α ≥ β/x + k_s(x)(β - x)`), `hs_upper_order_54`, `hs_upper_order_98`,
  `hs_small_upper_order` (`α ≤ 1 + 3δ`), `hs_quad_order` (`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`).
* Helpers: `hso_cheb_ratio` (`Zη < N'ξ`, `GLOBAL_UPPER_ORDER` (7)), `hso_affine_deriv`,
  `hso_affine_lt` (affine barriers), `hso_contact_pos` (signs of `M`, `ξ`, `η`, `N` at a contact).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Gap ratios of the averaged threshold `avg(p, q) = Sec(p, 1, q)` -/

/-- **The Padé gap** (`MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL` (3); inventory HS-S3 R2): for
`0 < p < q ≤ 1`, `η = avg(p, q) - g(q) > η₀ = (q - p)(6 + p - 5pq - q² - q)/(6(1 + p)(1 + q)²(p + q +
2))` (strict `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` at `z = (1 + q)/(1 + p)`). Status: stable. -/
theorem hs_pade_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) <
      m2Sec p 1 q - ss_gB 1 q := by
  have hq1 : q ≤ 1 := hq
  have hq0 : 0 < q := by linarith
  have hz : 1 < (q + 1) / (p + 1) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hlog := hso_log_lt_pade3 hz
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

/-- **The gap ratio from below** (`STRONG_ORDER` (2)-(3)): for `0 < p < q ≤ 1`, with
`N = (1 + p)(6 + p - 5pq - q² - q)`, `W = 6(p + q + 2)(1 - pq)`, `η = avg - g(q)`, `ξ = g(p) - avg`:
`η/ξ > N/(W - N)`, in cleared form `N ξ < (W - N) η`. Status: stable. -/
theorem hs_gap_ratio_low {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - m2Sec p 1 q) <
      (6 * (p + q + 2) * (1 - p * q) - (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)) *
        (m2Sec p 1 q - ss_gB 1 q) := by
  have hq0 : 0 < q := by linarith
  have hgap := hs_pade_gap hp hpq hq
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

/-- **The Chebyshev gap** (`GLOBAL_UPPER_ORDER` (6); inventory HS-S01 M6, as the log inequality
`log y > (y - 1)[3y(y + 1) - 2θ(y - 1)²]/(6y²)`, `y = (1 + q)/(1 + p)`, `θ = 1/(1 + p)`): for
`0 < p < q ≤ 1`, `avg(p, q) - 3/4 < (z_p² + z_p z_q + z_q²)/12`, `z_s = (1 - s)/(1 + s)`.
Status: stable. -/
theorem hs_chebyshev_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    m2Sec p 1 q - 3 / 4 <
      (((1 - p) / (1 + p)) ^ 2 + (1 - p) / (1 + p) * ((1 - q) / (1 + q)) +
        ((1 - q) / (1 + q)) ^ 2) / 12 := by
  have hq0 : 0 < q := by linarith
  have hy : 1 < (q + 1) / (p + 1) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hyθ : (q + 1) / (p + 1) ≤ 2 * (1 / (p + 1)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlog := hso_log_gt_cheb hy hyθ
  rw [m2Sec_of_ne hpq.ne]
  have hqp : 0 < q - p := by linarith
  have k := mul_lt_mul_of_pos_left hlog (by positivity : (0:ℝ) < 1 / (q - p))
  have e : 1 + 1 ^ 2 / ((p + 1) * (q + 1)) - 1 / (q - p) *
      (((q + 1) / (p + 1) - 1) * (3 * ((q + 1) / (p + 1)) * ((q + 1) / (p + 1) + 1) -
        2 * (1 / (p + 1)) * ((q + 1) / (p + 1) - 1) ^ 2) / (6 * ((q + 1) / (p + 1)) ^ 2)) - 3 / 4 =
      (((1 - p) / (1 + p)) ^ 2 + (1 - p) / (1 + p) * ((1 - q) / (1 + q)) +
        ((1 - q) / (1 + q)) ^ 2) / 12 := by
    have : p + 1 ≠ 0 := by positivity
    have : q + 1 ≠ 0 := by positivity
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    have : q - p ≠ 0 := hqp.ne'
    field_simp
    ring
  rw [← e]
  linarith

/-- The Chebyshev gap as a gap ratio (`GLOBAL_UPPER_ORDER` (7)): `Zη < N'ξ` with
`N' = 3 + p - q - 3pq`, `Z = 3 - p + q - 3pq` (`N'ξ - Zη = 6(1 - pq)(c₀ - (u - 3/4))`). -/
theorem hso_cheb_ratio {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (3 - p + q - 3 * p * q) * (m2Sec p 1 q - ss_gB 1 q) <
      (3 + p - q - 3 * p * q) * (ss_gB 1 p - m2Sec p 1 q) := by
  have hc := hs_chebyshev_gap hp hpq hq
  have hq0 : 0 < q := by linarith
  have hpq1 : 0 < 1 - p * q := by have := mul_le_of_le_one_right hp.le hq; linarith
  have e : (3 + p - q - 3 * p * q) * (ss_gB 1 p - m2Sec p 1 q) -
      (3 - p + q - 3 * p * q) * (m2Sec p 1 q - ss_gB 1 q) =
      6 * (1 - p * q) * ((((1 - p) / (1 + p)) ^ 2 + (1 - p) / (1 + p) * ((1 - q) / (1 + q)) +
        ((1 - q) / (1 + q)) ^ 2) / 12 - (m2Sec p 1 q - 3 / 4)) := by
    unfold ss_gB
    have : 1 + q ≠ 0 := by positivity
    have : 1 + p ≠ 0 := by positivity
    field_simp
    ring
  have := mul_pos (by positivity : (0:ℝ) < 6 * (1 - p * q)) (sub_pos.2 hc)
  linarith

/-! ### Contact inequalities -/

/-- **The strong lower-barrier contact** (`STRONG_ORDER` (4)-(12)): for `1 < x ≤ 9`,
`q_min = (4x² + 11x + 1)/(x(11x + 5)) ≤ q ≤ 1`, `p = 1/x + k_s(x)(1 - q)`:
`(7x + 1)N((2q - p)x - q²) - 4(x + 1)q(x - q)(W - N) ≥ 0` (`= (1 - q)(x + 1)P(q, x)/(x²(7x + 1)²)`,
`P` concave in `q` with positive endpoint values). Status: stable.
Route: `P ≥ 0` on `[q_min, 1]` from its quartic Bernstein form (`hso_strong_bern`, five coefficients
positive for every `x > 1`) instead of the concavity steps (iii)-(iv); `x ≤ 9` is not used. -/
theorem hs_strong_contact {x q : ℝ} (hx : 1 < x) (hx9 : x ≤ 9)
    (hq : (4 * x ^ 2 + 11 * x + 1) / (x * (11 * x + 5)) ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (7 * x + 1) * ((1 + (1 / x + hsKs x * (1 - q))) *
        (6 + (1 / x + hsKs x * (1 - q)) - 5 * (1 / x + hsKs x * (1 - q)) * q - q ^ 2 - q)) *
        ((2 * q - (1 / x + hsKs x * (1 - q))) * x - q ^ 2) -
      4 * (x + 1) * q * (x - q) *
        (6 * ((1 / x + hsKs x * (1 - q)) + q + 2) * (1 - (1 / x + hsKs x * (1 - q)) * q) -
          (1 + (1 / x + hsKs x * (1 - q))) *
            (6 + (1 / x + hsKs x * (1 - q)) - 5 * (1 / x + hsKs x * (1 - q)) * q - q ^ 2 - q)) := by
  have _hx9 := hx9
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hT : 0 ≤ x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1) := by
    rw [div_le_iff₀ (by positivity)] at hq; linarith
  have hS1 : 0 ≤ 1 - q := by linarith
  have hTS1 : 0 < x * (11 * x + 5) * q - (4 * x ^ 2 + 11 * x + 1) + (1 - q) := by
    rcases hS1.lt_or_eq with h | h
    · linarith
    · have : q = 1 := by linarith
      subst this
      linarith [mul_pos (show (0:ℝ) < 7 * x + 1 by linarith) hx1]
  have hb2 : 0 ≤ (x + 1) *
      (262098 * x ^ 5 + 211683 * x ^ 4 + 41340 * x ^ 3 + 2966 * x ^ 2 + 58 * x - 1) := by
    have : 0 ≤ 262098 * x ^ 5 + 211683 * x ^ 4 + 41340 * x ^ 3 + 2966 * x ^ 2 + 58 * x - 1 := by
      linarith [pow_pos hx0 5, pow_pos hx0 4, pow_pos hx0 3, pow_pos hx0 2]
    positivity
  have hpos := hso_bern4_pos hT hS1 hTS1
    (b0 := 18 * (x + 1) ^ 2 * (7 * x + 1) * (11 * x + 1) * (15 * x + 1) ^ 2 *
      (4 * x ^ 2 + 11 * x + 1) * x ^ 2)
    (b1 := (x + 1) * (15 * x + 1) *
      (82008 * x ^ 5 + 141569 * x ^ 4 + 62540 * x ^ 3 + 10134 * x ^ 2 + 692 * x + 17) * x)
    (b3 := 2 * (10742 * x ^ 4 + 10397 * x ^ 3 + 1685 * x ^ 2 + 87 * x + 1))
    (b4 := 2 * (313 * x ^ 2 + 38 * x + 1))
    (by positivity) (by positivity) hb2 (by positivity) (by positivity)
  rw [← hso_strong_bern x q] at hpos
  have hP := pos_of_mul_pos_right hpos (by positivity)
  have hR := mul_nonneg (mul_nonneg hS1 (by linarith : (0:ℝ) ≤ x + 1)) hP.le
  rw [← hso_strong_eq hx] at hR
  exact nonneg_of_mul_nonneg_right hR (by positivity)

/-- **The upper-barrier contact, `k = 5/4`** (`GLOBAL_UPPER_ORDER` (8)-(13)): for `x > 1`,
`(5x + 4)/(9x) ≤ q ≤ 1`, `p = 1/x + (5/4)(1 - q)`, `N' = 3 + p - q - 3pq`, `Z = 3 - p + q - 3pq`:
`(5/4)qZ(x - q) - N'((2q - p)x - q²) > 0` (Bernstein form (11), all coefficients positive).
Status: stable. -/
theorem hs_upper_contact_54 {x q : ℝ} (hx : 1 < x) (hq : (5 * x + 4) / (9 * x) ≤ q)
    (hq1 : q ≤ 1) :
    0 < 5 / 4 * q * (3 - (1 / x + 5 / 4 * (1 - q)) + q - 3 * (1 / x + 5 / 4 * (1 - q)) * q) *
        (x - q) -
      (3 + (1 / x + 5 / 4 * (1 - q)) - q - 3 * (1 / x + 5 / 4 * (1 - q)) * q) *
        ((2 * q - (1 / x + 5 / 4 * (1 - q))) * x - q ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hT : 0 ≤ 9 * x * q - (5 * x + 4) := by
    rw [div_le_iff₀ (by positivity)] at hq; linarith
  have hS : 0 ≤ 9 * x * (1 - q) := mul_nonneg (by positivity) (by linarith)
  have hTS : 0 < 9 * x * q - (5 * x + 4) + 9 * x * (1 - q) := by linarith
  have hpos := hso_bern4_pos (T := 9 * x * q - (5 * x + 4)) (S := 9 * x * (1 - q))
    (b0 := 8 * (5 * x + 4) * (7 * x + 2) * (9 * x + 4))
    (b1 := 4 * (9 * (x + 4) * (142 * x ^ 2 + 61 * x + 4)))
    (b2 := 6 * (54 * x * (53 * x ^ 2 + 102 * x + 24))) (b3 := 4 * (729 * x ^ 2 * (8 * x + 5)))
    (b4 := 8748 * x ^ 3) hT hS hTS (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)
  rw [← hso_up54_bern] at hpos
  have hx1 : 0 < 8748 * 16 * x ^ 3 * (x - 1) ^ 2 := by
    have : 0 < x - 1 := by linarith
    positivity
  have h16 := pos_of_mul_pos_right hpos hx1.le
  rw [← hso_up54_eq hx0] at h16
  exact pos_of_mul_pos_right h16 (by positivity)

/-- **The upper-barrier contact, `k = 9/8`** (`GLOBAL_UPPER_ORDER` (14)-(15)): as
`hs_upper_contact_54` with `k = 9/8`, `1 < x ≤ 5`, `(9x + 8)/(17x) ≤ q ≤ 1`. Status: stable. -/
theorem hs_upper_contact_98 {x q : ℝ} (hx : 1 < x) (hx5 : x ≤ 5)
    (hq : (9 * x + 8) / (17 * x) ≤ q) (hq1 : q ≤ 1) :
    0 < 9 / 8 * q * (3 - (1 / x + 9 / 8 * (1 - q)) + q - 3 * (1 / x + 9 / 8 * (1 - q)) * q) *
        (x - q) -
      (3 + (1 / x + 9 / 8 * (1 - q)) - q - 3 * (1 / x + 9 / 8 * (1 - q)) * q) *
        ((2 * q - (1 / x + 9 / 8 * (1 - q))) * x - q ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hT : 0 ≤ 17 * x * q - (9 * x + 8) := by
    rw [div_le_iff₀ (by positivity)] at hq; linarith
  have hS : 0 ≤ 17 * x * (1 - q) := mul_nonneg (by positivity) (by linarith)
  have hTS : 0 < 17 * x * q - (9 * x + 8) + 17 * x * (1 - q) := by linarith
  have hC1 : 0 ≤ 4 * (51 * (-3237 * x ^ 3 + 17062 * x ^ 2 + 7840 * x + 384)) := by
    have := mul_le_mul_of_nonneg_left hx5 (sq_nonneg x)
    linarith [sq_nonneg x]
  have hpos := hso_bern4_pos (T := 17 * x * q - (9 * x + 8)) (S := 17 * x * (1 - q))
    (b0 := 144 * (9 * x + 8) * (13 * x + 4) * (17 * x + 8))
    (b2 := 6 * (578 * x * (67 * x ^ 2 + 1500 * x + 416)))
    (b3 := 4 * (14739 * x ^ 2 * (37 * x + 38))) (b4 := 1002252 * x ^ 3) hT hS hTS (by positivity)
    hC1 (by positivity) (by positivity) (by positivity)
  rw [← hso_up98_bern] at hpos
  have hx1 : 0 < 2004504 * 64 * x ^ 3 * (x - 1) ^ 2 := by
    have : 0 < x - 1 := by linarith
    positivity
  have h64 := pos_of_mul_pos_right hpos hx1.le
  rw [← hso_up98_eq hx0] at h64
  exact pos_of_mul_pos_right h64 (by positivity)

/-- **The small-shape upper-barrier contact** (inventory HS-S4 R6′, replacing the Simpson bound of
`SMALL_SHAPE_UPPER_ORDER` (3)-(14)): for `x = 1 + z`, `0 < z ≤ 7/6`, `q = 1 - h`, `0 ≤ h ≤ 1/20`,
`h(z + 3) < z` (`⟺ p < q`), `p = (3 - 2q)/x`, `w = (q - p)/(2 + p + q)`, the two-term `artanh`
majorant `ũ = 1 + 1/((1 + p)(1 + q)) - (2w + 2w³/3)/(q - p)` satisfies
`2q(x - q)(g(p) - ũ) - x(2q(x + 1) - q² - 3)(ũ - g(q)) > 0` (the polynomial `K(z, h)` of R6′).
Status: stable. -/
theorem hs_small_contact {z h : ℝ} (hz : 0 < z) (hz7 : z ≤ 7 / 6) (hh : 0 ≤ h) (hh20 : h ≤ 1 / 20)
    (hhz : h * (z + 3) < z) :
    let x := 1 + z
    let q := 1 - h
    let p := (3 - 2 * q) / x
    let w := (q - p) / (2 + p + q)
    let ut := 1 + 1 / ((1 + p) * (1 + q)) - (2 * w + 2 / 3 * w ^ 3) / (q - p)
    0 < 2 * q * (x - q) * (ss_gB 1 p - ut) - x * (2 * q * (x + 1) - q ^ 2 - 3) * (ut - ss_gB 1 q) := by
  intro x q p w ut
  have hx0 : 0 < x := by positivity
  have hq0 : 0 < q := by simp only [q]; linarith
  have hp0 : 0 < p := by
    simp only [p, q]
    exact div_pos (by linarith) hx0
  have hpq : p < q := by
    simp only [p, q, x]
    rw [div_lt_iff₀ hx0]
    linarith
  obtain ⟨e1, e2⟩ := hso_ut_gaps hp0 hpq
  have hKpos := hso_K_pos hz hz7 hh hh20 hhz
  rw [← hso_K_eq (h := h) hz] at hKpos
  have hd : 0 < 3 * (1 + p) ^ 2 * (1 + q) ^ 2 * (p + q + 2) ^ 3 := by positivity
  have e : 2 * q * (x - q) * (ss_gB 1 p - ut) -
      x * (2 * q * (x + 1) - q ^ 2 - 3) * (ut - ss_gB 1 q) =
      (q - p) * (2 * q * (x - q) * (1 + q) *
        (12 + 14 * q + 5 * q ^ 2 + 10 * p - 4 * p * q - 8 * p * q ^ 2 - 3 * p * q ^ 3 -
          p ^ 2 - 14 * p ^ 2 * q - 4 * p ^ 2 * q ^ 2 - 2 * p ^ 3 - 5 * p ^ 3 * q) -
        x * (2 * q * (x + 1) - q ^ 2 - 3) * (1 + p) *
        (12 + 10 * q - q ^ 2 - 2 * q ^ 3 + 14 * p - 4 * p * q - 14 * p * q ^ 2 -
          5 * p * q ^ 3 + 5 * p ^ 2 - 8 * p ^ 2 * q - 4 * p ^ 2 * q ^ 2 - 3 * p ^ 3 * q)) /
        (3 * (1 + p) ^ 2 * (1 + q) ^ 2 * (p + q + 2) ^ 3) := by
    rw [e1, e2]
    have : 1 + p ≠ 0 := by positivity
    have : 1 + q ≠ 0 := by positivity
    have : p + q + 2 ≠ 0 := by positivity
    field_simp
  rw [e]
  apply div_pos _ hd
  apply mul_pos (by linarith)
  exact pos_of_mul_pos_right hKpos (by positivity)

/-- **The quadratic lower-barrier contact** (`RATIONAL_QUADRATIC_ORDER` (3)-(10)): for
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 9/20`, `c = (4x² + 11x + 1)/(7x + 1)`, the barrier
`B(δ) = 1 + cδ + δ²/(1 + 4δ)`, `B'(δ) = c + δ(2 + 4δ)/(1 + 4δ)²`, the contact `q = 1/(1 + δ)`,
`p = B(δ)/(x(1 + δ))`: `N((2q - p)x - q²) - (x - q)(W - N)(B'(δ)/x - p) ≥ 0`
(`= δQ(δ, x)/(x³(1 + δ)⁵(1 + 4δ)⁴(7x + 1)³)`, the 8 × 9 table). Status: stable.
Proof as in the note (rows (8)-(10), `hso_quad_Q_nonneg`); only `X = x - 2 ≥ 0` is used. -/
theorem hs_quad_contact {x δ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 9 / 20) :
    let c := (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1)
    let q := 1 / (1 + δ)
    let p := (1 + c * δ + δ ^ 2 / (1 + 4 * δ)) / (x * (1 + δ))
    let N := (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)
    let W := 6 * (p + q + 2) * (1 - p * q)
    0 ≤ N * ((2 * q - p) * x - q ^ 2) -
      (x - q) * (W - N) * ((c + δ * (2 + 4 * δ) / (1 + 4 * δ) ^ 2) / x - p) := by
  intro c q p N W
  have _hx2 := hx2
  have hx0 : 0 < x := by linarith
  have key := hso_quad_eq (c := c) (q := q) (p := p) (N := N) (W := W) hx0 hδ rfl rfl rfl rfl rfl
  have h := mul_nonneg hδ (hso_quad_Q_nonneg hx hδ hδ2)
  rw [← key] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

/-! ### The orders -/

/-- The derivative of an affine barrier `z ↦ ℓ + k(1 - z)`. -/
theorem hso_affine_deriv (ℓ k z : ℝ) : HasDerivAt (fun z => ℓ + k * (1 - z)) (-k) z := by
  have := (((hasDerivAt_id' z).const_sub 1).const_mul k).const_add ℓ
  rwa [mul_neg_one] at this

/-- An affine barrier with slope `-k > -1` below the diagonal at `q₁` stays below it on
`[q₁, 1]`. -/
theorem hso_affine_lt {ℓ k q₁ : ℝ} (hk : -1 < k) (h : ℓ + k * (1 - q₁) < q₁) :
    ∀ z ∈ Icc q₁ 1, ℓ + k * (1 - z) < z := by
  intro z hz
  have := mul_nonneg (by linarith : (0:ℝ) ≤ k + 1) (sub_nonneg.2 hz.1)
  linarith

/-- The contact data of an affine lower barrier `p = 1/x + k(1 - z)` below the diagonal. -/
theorem hso_contact_pos {x p z : ℝ} (hx : 1 < x) (hp : 0 < p) (hpz : p < z) (hz : z ≤ 1) :
    0 < (2 * z - p) * x - z ^ 2 ∧ 0 ≤ ss_gB 1 p - m2Sec p 1 z ∧ 0 < m2Sec p 1 z - ss_gB 1 z ∧
      0 ≤ (1 + p) * (6 + p - 5 * p * z - z ^ 2 - z) := by
  have hz0 : 0 < z := hp.trans hpz
  refine ⟨?_, sub_nonneg.2 (ss_sec_le_left hp hpz.le hz), sub_pos.2 (ss_sec_gt_right hp hpz hz),
    ?_⟩
  · have h1 : 0 < z * (x - z) := mul_pos hz0 (by linarith)
    have h2 : 0 < (z - p) * x := mul_pos (by linarith) (by linarith)
    linarith
  · have h1 : p * z ≤ p := mul_le_of_le_one_right hp.le hz
    have h2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0.le hz
    have : 0 < 6 + p - 5 * p * z - z ^ 2 - z := by linarith
    positivity

/-- **The strong lower order** (`STRONG_ORDER` (1); inventory HS-S01 M5, HS-S4 R4): for
`1 < x ≤ 9`, `1 ≤ α < x ≤ β` with `Sec(1, x, β) = Sec(α, β, x)`,
`α ≥ β/x + k_s(x)(β - x)`, `k_s = 4(x + 1)/(7x + 1)` (barrier `p = ℓ + k_s(1 - z)`, contact
`hs_pade_gap`, `hs_gap_ratio_low`, `hs_strong_contact`, `hs_first_contact`). Status: stable. -/
theorem hs_strong_order {x al be : ℝ} (hx : 1 < x) (hx9 : x ≤ 9) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : be / x + hsKs x * (be - x) ≤ al := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hk : 0 ≤ hsKs x := by unfold hsKs; positivity
  have hP := hso_order_lower (P := fun z => 1 / x + hsKs x * (1 - z)) (P' := fun _ => -hsKs x)
    (p₁ := al / be) (q₁ := x / be) hx (div_pos hal0 hbe0) (div_lt_div_of_pos_right hax hbe0)
    ((div_le_one hbe0).2 hxb) (hso_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => hso_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) ?_
  · have e : be / x + hsKs x * (be - x) = be * (1 / x + hsKs x * (1 - x / be)) := by
      field_simp
    rw [e]
    calc be * (1 / x + hsKs x * (1 - x / be)) ≤ be * (al / be) :=
          mul_le_mul_of_nonneg_left hP hbe0.le
      _ = al := by field_simp
  intro z hz hPz hzeq
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + hsKs x * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  obtain ⟨hM, hξ, hη, hN⟩ := hso_contact_pos hx hp0 hPz hz1
  have hq : (4 * x ^ 2 + 11 * x + 1) / (x * (11 * x + 5)) ≤ z := by
    have e : 1 / x + hsKs x * (1 - z) =
        (7 * x + 1 + 4 * (x + 1) * x * (1 - z)) / (x * (7 * x + 1)) := by
      unfold hsKs; field_simp
    rw [e, div_lt_iff₀ (by positivity)] at hPz
    rw [div_le_iff₀ (by positivity)]
    linarith only [hPz]
  have hcont := hs_strong_contact hx hx9 hq hz1
  have hgap := hs_gap_ratio_low hp0 hPz hz1
  set pz := 1 / x + hsKs x * (1 - z) with hpz
  set N := (1 + pz) * (6 + pz - 5 * pz * z - z ^ 2 - z) with hNdef
  set W := 6 * (pz + z + 2) * (1 - pz * z) with hWdef
  set M := (2 * z - pz) * x - z ^ 2 with hMdef
  have hcon : hsKs x * z * (x - z) * (W - N) ≤ N * M := by
    have h7 : 0 < 7 * x + 1 := by linarith
    have ek : hsKs x * (7 * x + 1) = 4 * (x + 1) := by unfold hsKs; field_simp
    have key : (7 * x + 1) * (N * M - hsKs x * z * (x - z) * (W - N)) =
        (7 * x + 1) * N * M - 4 * (x + 1) * z * (x - z) * (W - N) := by rw [← ek]; ring
    rw [← key] at hcont
    have := nonneg_of_mul_nonneg_right hcont h7
    linarith only [this]
  have := hso_lower_alg hgap hcon hM hξ hη hN
  exact lt_of_eq_of_lt (by ring) this

/-- **The global upper order, `5/4`** (`GLOBAL_UPPER_ORDER` (2); inventory HS-S01 M9): for `1 < x`,
`1 ≤ α < x ≤ β` with equal secants, `α ≤ β/x + (5/4)(β - x)` (`hs_chebyshev_gap`,
`hs_upper_contact_54`, first contact from above). Status: stable. -/
theorem hs_upper_order_54 {x al be : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : al ≤ be / x + 5 / 4 * (be - x) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hp₁ : al / be < x / be := div_lt_div_of_pos_right hax hbe0
  have hq₁ : x / be ≤ 1 := (div_le_one hbe0).2 hxb
  have e : be / x + 5 / 4 * (be - x) = be * (1 / x + 5 / 4 * (1 - x / be)) := by field_simp
  rw [e]
  suffices h : al / be ≤ 1 / x + 5 / 4 * (1 - x / be) by
    calc al = be * (al / be) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hbe0.le
  rcases le_or_gt (x / be) (1 / x + 5 / 4 * (1 - x / be)) with hle | hlt
  · linarith
  refine hso_order_upper (P := fun z => 1 / x + 5 / 4 * (1 - z)) (P' := fun _ => -(5 / 4))
    (q₁ := x / be) hx hp₁ hq₁ (hso_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => hso_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) (hso_affine_lt (by norm_num) hlt) ?_
  intro z hz hzeq
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + 5 / 4 * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hPz : 1 / x + 5 / 4 * (1 - z) < z :=
    hso_affine_lt (by norm_num) hlt z (Ioc_subset_Icc_self hz)
  obtain ⟨hM, hξ, hη, -⟩ := hso_contact_pos hx hp0 hPz hz1
  have hq : (5 * x + 4) / (9 * x) ≤ z := by
    have e : 1 / x + 5 / 4 * (1 - z) = (1 + 5 / 4 * x * (1 - z)) / x := by field_simp
    rw [e, div_lt_iff₀ hx0] at hPz
    rw [div_le_iff₀ (by positivity)]
    linarith only [hPz]
  have hcont := hs_upper_contact_54 hx hq hz1
  have hgap := hso_cheb_ratio hp0 hPz hz1
  have hZ : 0 < 3 - (1 / x + 5 / 4 * (1 - z)) + z - 3 * (1 / x + 5 / 4 * (1 - z)) * z := by
    have : (1 / x + 5 / 4 * (1 - z)) * z < 1 := by
      have := mul_le_of_le_one_right hp0.le hz1; linarith only [this, hPz, hz1]
    linarith only [this, hPz]
  have := hso_upper_alg (B := 5 / 4 * z * (x - z)) hgap (by linarith only [hcont]) hM hξ hZ
  exact lt_of_lt_of_eq this (by ring)

/-- **The global upper order, `9/8`** (`GLOBAL_UPPER_ORDER` (3); inventory HS-S2 R5, HS-S3 R4): for
`1 < x ≤ 5`, `1 ≤ α < x ≤ β` with equal secants, `α ≤ β/x + (9/8)(β - x)`. Status: stable. -/
theorem hs_upper_order_98 {x al be : ℝ} (hx : 1 < x) (hx5 : x ≤ 5) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : al ≤ be / x + 9 / 8 * (be - x) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hp₁ : al / be < x / be := div_lt_div_of_pos_right hax hbe0
  have hq₁ : x / be ≤ 1 := (div_le_one hbe0).2 hxb
  have e : be / x + 9 / 8 * (be - x) = be * (1 / x + 9 / 8 * (1 - x / be)) := by field_simp
  rw [e]
  suffices h : al / be ≤ 1 / x + 9 / 8 * (1 - x / be) by
    calc al = be * (al / be) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hbe0.le
  rcases le_or_gt (x / be) (1 / x + 9 / 8 * (1 - x / be)) with hle | hlt
  · linarith
  refine hso_order_upper (P := fun z => 1 / x + 9 / 8 * (1 - z)) (P' := fun _ => -(9 / 8))
    (q₁ := x / be) hx hp₁ hq₁ (hso_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => hso_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) (hso_affine_lt (by norm_num) hlt) ?_
  intro z hz hzeq
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + 9 / 8 * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hPz : 1 / x + 9 / 8 * (1 - z) < z :=
    hso_affine_lt (by norm_num) hlt z (Ioc_subset_Icc_self hz)
  obtain ⟨hM, hξ, hη, -⟩ := hso_contact_pos hx hp0 hPz hz1
  have hq : (9 * x + 8) / (17 * x) ≤ z := by
    have e : 1 / x + 9 / 8 * (1 - z) = (1 + 9 / 8 * x * (1 - z)) / x := by field_simp
    rw [e, div_lt_iff₀ hx0] at hPz
    rw [div_le_iff₀ (by positivity)]
    linarith only [hPz]
  have hcont := hs_upper_contact_98 hx hx5 hq hz1
  have hgap := hso_cheb_ratio hp0 hPz hz1
  have hZ : 0 < 3 - (1 / x + 9 / 8 * (1 - z)) + z - 3 * (1 / x + 9 / 8 * (1 - z)) * z := by
    have : (1 / x + 9 / 8 * (1 - z)) * z < 1 := by
      have := mul_le_of_le_one_right hp0.le hz1; linarith only [this, hPz, hz1]
    linarith only [this, hPz]
  have := hso_upper_alg (B := 9 / 8 * z * (x - z)) hgap (by linarith only [hcont]) hM hξ hZ
  exact lt_of_lt_of_eq this (by ring)

/-- **The extended small-shape upper order** (`SMALL_SHAPE_UPPER_ORDER` (1); inventory HS-S4 R7):
for `1 < x ≤ 13/6`, `1 ≤ α < x ≤ β ≤ (20/19)x` (`0 ≤ δ ≤ 1/19`) with equal secants,
`α ≤ 1 + 3δ`, `δ = β/x - 1` (barrier `k = 2/x`, `hs_small_contact`). Status: stable. -/
theorem hs_small_upper_order {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hδ : be ≤ 20 / 19 * x) (heq : m2Sec 1 x be = m2Sec al be x) :
    al ≤ 1 + 3 * (be / x - 1) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hp₁ : al / be < x / be := div_lt_div_of_pos_right hax hbe0
  have hq₁ : x / be ≤ 1 := (div_le_one hbe0).2 hxb
  have hq₁19 : 19 / 20 ≤ x / be := by rw [le_div_iff₀ hbe0]; linarith
  have e : 1 + 3 * (be / x - 1) = be * ((3 - 2 * (x / be)) / x) := by field_simp; ring
  rw [e]
  suffices h : al / be ≤ (3 - 2 * (x / be)) / x by
    calc al = be * (al / be) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hbe0.le
  rcases le_or_gt (x / be) ((3 - 2 * (x / be)) / x) with hle | hlt
  · linarith
  -- the affine barrier `p = (3 - 2z)/x = 1/x + (2/x)(1 - z)` (slope `k = 2/x`)
  have hPform : ∀ z, (3 - 2 * z) / x = 1 / x + 2 / x * (1 - z) := fun z => by field_simp; ring
  have hlt' : ∀ z ∈ Icc (x / be) 1, (3 - 2 * z) / x < z := by
    intro z hz
    rw [hPform] at hlt ⊢
    exact hso_affine_lt (by have : 0 < 2 / x := by positivity
                            linarith) hlt z hz
  refine hso_order_upper (P := fun z => (3 - 2 * z) / x) (P' := fun _ => -(2 / x))
    (q₁ := x / be) hx hp₁ hq₁ (hso_norm_eq hx0 hal0 hbe0 heq) (by norm_num)
    (fun z _ => by
      have := (((hasDerivAt_id' z).const_mul 2).const_sub 3).div_const x
      convert this using 1
      ring)
    (fun z hz => div_pos (by linarith [hz.2]) hx0) hlt' ?_
  intro z hz hzeq
  have hz1 := hz.2
  have hz19 : 19 / 20 < z := lt_of_le_of_lt hq₁19 hz.1
  have hPz := hlt' z (Ioc_subset_Icc_self hz)
  have hp0 : 0 < (3 - 2 * z) / x := div_pos (by linarith) hx0
  obtain ⟨hM, hξ, hη, -⟩ := hso_contact_pos hx hp0 hPz hz1
  have hhz : (1 - z) * (x - 1 + 3) < x - 1 := by
    rw [div_lt_iff₀ hx0] at hPz
    linarith
  have hsc := hs_small_contact (z := x - 1) (h := 1 - z) (by linarith) (by linarith)
    (by linarith) (by linarith) hhz
  simp only [show 1 + (x - 1) = x by ring, show 1 - (1 - z) = z by ring] at hsc
  -- `u ≤ ũ` (two terms of `2 artanh`, `ss_log_ge_cubic`)
  have hu := hso_sec_le_ut hp0 hPz
  set ut := 1 + 1 / ((1 + (3 - 2 * z) / x) * (1 + z)) -
      (2 * ((z - (3 - 2 * z) / x) / (2 + (3 - 2 * z) / x + z)) +
        2 / 3 * ((z - (3 - 2 * z) / x) / (2 + (3 - 2 * z) / x + z)) ^ 3) /
        (z - (3 - 2 * z) / x) with hut
  have hMe : (2 * z - (3 - 2 * z) / x) * x - z ^ 2 = 2 * z * (x + 1) - z ^ 2 - 3 := by
    field_simp; ring
  rw [hMe] at hM ⊢
  have k1 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (by linarith : m2Sec ((3 - 2 * z) / x) 1 z - ss_gB 1 z ≤
      ut - ss_gB 1 z) hM.le) hx0.le
  have k2 := mul_le_mul_of_nonneg_left (by linarith :
    ss_gB 1 ((3 - 2 * z) / x) - ut ≤ ss_gB 1 ((3 - 2 * z) / x) - m2Sec ((3 - 2 * z) / x) 1 z)
    (mul_nonneg (by positivity) (by linarith) : (0:ℝ) ≤ 2 * z * (x - z))
  have key : x * ((m2Sec ((3 - 2 * z) / x) 1 z - ss_gB 1 z) * (2 * z * (x + 1) - z ^ 2 - 3)) <
      x * (-(-(2 / x)) * (ss_gB 1 ((3 - 2 * z) / x) - m2Sec ((3 - 2 * z) / x) 1 z) * z *
        (x - z)) := by
    have e2 : x * (-(-(2 / x)) * (ss_gB 1 ((3 - 2 * z) / x) - m2Sec ((3 - 2 * z) / x) 1 z) * z *
        (x - z)) = 2 * z * (x - z) *
          (ss_gB 1 ((3 - 2 * z) / x) - m2Sec ((3 - 2 * z) / x) 1 z) := by
      field_simp
    rw [e2]
    linarith
  exact lt_of_mul_lt_mul_left key hx0.le

/-- The quadratic barrier `B(δ) = 1 + c(x)δ + δ²/(1 + 4δ)` of `RATIONAL_QUADRATIC_ORDER` (1). -/
noncomputable def hsoQB (x d : ℝ) : ℝ :=
  1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * d + d ^ 2 / (1 + 4 * d)

/-- `B'(δ) = c(x) + δ(2 + 4δ)/(1 + 4δ)²`. -/
noncomputable def hsoQB' (x d : ℝ) : ℝ :=
  (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + d * (2 + 4 * d) / (1 + 4 * d) ^ 2

theorem hsoQB_hasDerivAt {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) :
    HasDerivAt (hsoQB x) (hsoQB' x d) d := by
  have h1 := ((hasDerivAt_id' d).const_mul ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1))).const_add 1
  have h2 := (hasDerivAt_pow 2 d).div (((hasDerivAt_id' d).const_mul 4).const_add 1)
    (by positivity)
  refine (h1.add h2).congr_deriv ?_
  have : 1 + 4 * d ≠ 0 := by positivity
  unfold hsoQB'
  push_cast
  field_simp
  ring

theorem hsoQB_pos {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) : 0 < hsoQB x d := by
  unfold hsoQB
  have : 0 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * d := by positivity
  have : 0 ≤ d ^ 2 / (1 + 4 * d) := by positivity
  linarith

/-- **The quadratic contact** at `z = 1/(1 + δ)` (`hs_quad_contact`, `hso_lower_alg`): the lower
contact inequality of `hso_order_lower` for the barrier `P(z) = zB(1/z - 1)/x`. -/
theorem hso_quad_contact_at {x z : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hz0 : 0 < z)
    (hz1 : z ≤ 1) (hδ2 : z⁻¹ - 1 ≤ 9 / 20) (hPz : z * hsoQB x (z⁻¹ - 1) / x < z) :
    -((1 * hsoQB x (z⁻¹ - 1) + z * (hsoQB' x (z⁻¹ - 1) * -(z ^ 2)⁻¹)) / x) *
        (ss_gB 1 (z * hsoQB x (z⁻¹ - 1) / x) - m2Sec (z * hsoQB x (z⁻¹ - 1) / x) 1 z) * z *
        (x - z) <
      (m2Sec (z * hsoQB x (z⁻¹ - 1) / x) 1 z - ss_gB 1 z) *
        ((2 * z - z * hsoQB x (z⁻¹ - 1) / x) * x - z ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz1
  have hq : 0 ≤ (1 + hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) *
        (6 + hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) -
          5 * (hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * (1 / (1 + (z⁻¹ - 1))) -
          (1 / (1 + (z⁻¹ - 1))) ^ 2 - 1 / (1 + (z⁻¹ - 1))) *
        ((2 * (1 / (1 + (z⁻¹ - 1))) - hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * x -
          (1 / (1 + (z⁻¹ - 1))) ^ 2) -
      (x - 1 / (1 + (z⁻¹ - 1))) *
        (6 * (hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) + 1 / (1 + (z⁻¹ - 1)) + 2) *
            (1 - hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) * (1 / (1 + (z⁻¹ - 1)))) -
          (1 + hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) *
            (6 + hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) -
              5 * (hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * (1 / (1 + (z⁻¹ - 1))) -
              (1 / (1 + (z⁻¹ - 1))) ^ 2 - 1 / (1 + (z⁻¹ - 1)))) *
        (hsoQB' x (z⁻¹ - 1) / x - hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) :=
    hs_quad_contact hx hx2 hδ0 hδ2
  have e1 : 1 / (1 + (z⁻¹ - 1)) = z := by rw [add_sub_cancel, one_div, inv_inv]
  have e2 : hsoQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) = z * hsoQB x (z⁻¹ - 1) / x := by
    rw [add_sub_cancel]; field_simp
  have hBpos := hsoQB_pos hx0 hδ0
  rw [e1, e2] at hq
  generalize hsoQB x (z⁻¹ - 1) = Bv at hq hPz hBpos ⊢
  generalize hsoQB' x (z⁻¹ - 1) = Bd at hq ⊢
  have hp0 : 0 < z * Bv / x := by positivity
  have hgap := hs_gap_ratio_low hp0 hPz hz1
  obtain ⟨hM, hξ, hη, hN⟩ := hso_contact_pos (x := x) (by linarith) hp0 hPz hz1
  have key := hso_lower_alg (B := (x - z) * (Bd / x - z * Bv / x)) hgap (by linarith) hM hξ hη hN
  generalize ss_gB 1 (z * Bv / x) - m2Sec (z * Bv / x) 1 z = ξ at key ⊢
  have e3 : -((1 * Bv + z * (Bd * -(z ^ 2)⁻¹)) / x) * ξ * z * (x - z) =
      (x - z) * (Bd / x - z * Bv / x) * ξ := by
    field_simp
    ring
  rw [e3]
  exact key

/-- **The rational quadratic order** (`RATIONAL_QUADRATIC_ORDER` (1); inventory HS-S3 R5): for
`2 ≤ x ≤ 13/6`, `1 ≤ α < x ≤ β` with equal secants, `δ = β/x - 1`,
`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`, `c(x) = (4x² + 11x + 1)/(7x + 1)` (`hs_strong_order` for the domain
`δ < 9/20`, `hs_quad_contact`). Status: stable.
Route: first contact for the non-affine barrier `p = zB(1/z - 1)/x` (`hso_order_lower`); the case
where the barrier meets the diagonal is excluded by the last-meeting-point argument of
`ss_order_norm` (no continuation). -/
theorem hs_quad_order {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) :
    1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) +
        (be / x - 1) ^ 2 / (1 + 4 * (be / x - 1)) ≤ al := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hc0 : 0 < (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) := by positivity
  -- the strong order gives `δ₁ = β/x - 1 ≤ 9/20` (`RATIONAL_QUADRATIC_ORDER` (3))
  have hδ₁0 : 0 ≤ be / x - 1 := by rw [sub_nonneg, le_div_iff₀ hx0]; linarith
  have hδ₁ : be / x - 1 ≤ 9 / 20 := by
    have hs := hs_strong_order hx1 (by linarith) hal hax hxb heq
    have e : be / x + hsKs x * (be - x) =
        1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) := by
      unfold hsKs; field_simp; ring
    rw [e] at hs
    by_contra h
    push Not at h
    have k1 := mul_lt_mul_of_pos_left h hc0
    have k2 : x - 1 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (9 / 20) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x)]
    linarith
  -- the barrier `P(z) = zB(1/z - 1)/x`, `B(δ) = 1 + cδ + δ²/(1 + 4δ)`
  have hP := hso_order_lower (P := fun z => z * hsoQB x (z⁻¹ - 1) / x)
    (P' := fun z => (1 * hsoQB x (z⁻¹ - 1) + z * (hsoQB' x (z⁻¹ - 1) * -(z ^ 2)⁻¹)) / x)
    (p₁ := al / be) (q₁ := x / be) hx1 (div_pos hal0 hbe0) (div_lt_div_of_pos_right hax hbe0)
    ((div_le_one hbe0).2 hxb) (hso_norm_eq hx0 hal0 hbe0 heq) (by simp [hsoQB])
    (fun z hz => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans_le hz.1
      have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz.2
      exact ((hasDerivAt_id' z).mul ((hsoQB_hasDerivAt hx0 hδ0).comp z
        ((hasDerivAt_inv hz0.ne').sub_const 1))).div_const x)
    (fun z hz => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans_le hz.1
      have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz.2
      exact div_pos (mul_pos hz0 (hsoQB_pos hx0 hδ0)) hx0)
    (fun z hz hPz _ => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans hz.1
      refine hso_quad_contact_at hx hx2 hz0 hz.2 ?_ hPz
      have : z⁻¹ < be / x := by
        rw [← inv_div]; exact inv_strictAnti₀ (div_pos hx0 hbe0) hz.1
      linarith)
  rw [inv_div] at hP
  have e : x / be * hsoQB x (be / x - 1) / x = hsoQB x (be / x - 1) / be := by field_simp
  rw [e] at hP
  exact (div_le_div_iff_of_pos_right hbe0).1 hP

end SmoothedOctagon
