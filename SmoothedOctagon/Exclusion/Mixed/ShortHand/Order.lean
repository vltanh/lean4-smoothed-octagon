module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic

/-!
# Hand proof of the smaller-short case: the equal-secant orders

The order relations between the shape coordinates `x = C/a`, `α = A/a`, `β = B/a` of a short bridge
with equal turn secants `Sec(1, x, β) = Sec(α, β, x)` (`MIXED_SMALLER_SHORT_STRONG_ORDER`,
`MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER`, `MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER`,
`MIXED_SMALLER_SHORT_RATIONAL_QUADRATIC_ORDER`; inventories HS-S01 M1-M9, HS-S3 R2-R5, HS-S4 R1-R8).
Route (inventory HS-S4 R1, HS-S01 M5): no equal-secant continuation; the barrier argument runs on
the normalized comparison function `Φ(z) = avg(ℓ + k(1 - z), z) - avg(ℓ, 1/z)` of `ss_order_norm`
with the first-contact lemma `hs_first_contact`; at a zero of `Φ` the sign of `Φ'` is the contact
inequality below.

## Main API

* Gap ratios: `hs_pade_gap` (`MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL` (3)), `hs_gap_ratio_low`
  (`STRONG_ORDER` (2)-(3)), `hs_chebyshev_gap` (`GLOBAL_UPPER_ORDER` (6)).
* Contact inequalities: `hs_strong_contact` (`STRONG_ORDER` (4)-(12)), `hs_upper_contact_54`,
  `hs_upper_contact_98` (`GLOBAL_UPPER_ORDER` (8)-(15)), `hs_small_contact` (inventory HS-S4 R6′),
  `hs_quad_contact` (`RATIONAL_QUADRATIC_ORDER` (3)-(10)).
* Orders: `hs_strong_order` (`α ≥ β/x + k_s(x)(β - x)`), `hs_upper_order_54`, `hs_upper_order_98`,
  `hs_small_upper_order` (`α ≤ 1 + 3δ`), `hs_quad_order` (`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`).
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Gap ratios of the averaged threshold `avg(p, q) = Sec(p, 1, q)` -/

/-- **The Padé gap** (`MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL` (3); inventory HS-S3 R2): for
`0 < p < q ≤ 1`, `η = avg(p, q) - g(q) > η₀ = (q - p)(6 + p - 5pq - q² - q)/(6(1 + p)(1 + q)²(p + q +
2))` (strict `log z < (z - 1)(z² + 10z + 1)/(6z(z + 1))` at `z = (1 + q)/(1 + p)`). Status: stable. -/
theorem hs_pade_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (q - p) * (6 + p - 5 * p * q - q ^ 2 - q) / (6 * (1 + p) * (1 + q) ^ 2 * (p + q + 2)) <
      m2Sec p 1 q - ss_gB 1 q := by
  sorry

/-- **The gap ratio from below** (`STRONG_ORDER` (2)-(3)): for `0 < p < q ≤ 1`, with
`N = (1 + p)(6 + p - 5pq - q² - q)`, `W = 6(p + q + 2)(1 - pq)`, `η = avg - g(q)`, `ξ = g(p) - avg`:
`η/ξ > N/(W - N)`, in cleared form `N ξ < (W - N) η`. Status: stable. -/
theorem hs_gap_ratio_low {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q) * (ss_gB 1 p - m2Sec p 1 q) <
      (6 * (p + q + 2) * (1 - p * q) - (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)) *
        (m2Sec p 1 q - ss_gB 1 q) := by
  sorry

/-- **The Chebyshev gap** (`GLOBAL_UPPER_ORDER` (6); inventory HS-S01 M6, as the log inequality
`log y > (y - 1)[3y(y + 1) - 2θ(y - 1)²]/(6y²)`, `y = (1 + q)/(1 + p)`, `θ = 1/(1 + p)`): for
`0 < p < q ≤ 1`, `avg(p, q) - 3/4 < (z_p² + z_p z_q + z_q²)/12`, `z_s = (1 - s)/(1 + s)`.
Status: stable. -/
theorem hs_chebyshev_gap {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    m2Sec p 1 q - 3 / 4 <
      (((1 - p) / (1 + p)) ^ 2 + (1 - p) / (1 + p) * ((1 - q) / (1 + q)) +
        ((1 - q) / (1 + q)) ^ 2) / 12 := by
  sorry

/-! ### Contact inequalities -/

/-- **The strong lower-barrier contact** (`STRONG_ORDER` (4)-(12)): for `1 < x ≤ 9`,
`q_min = (4x² + 11x + 1)/(x(11x + 5)) ≤ q ≤ 1`, `p = 1/x + k_s(x)(1 - q)`:
`(7x + 1)N((2q - p)x - q²) - 4(x + 1)q(x - q)(W - N) ≥ 0` (`= (1 - q)(x + 1)P(q, x)/(x²(7x + 1)²)`,
`P` concave in `q` with positive endpoint values). Status: stable. -/
theorem hs_strong_contact {x q : ℝ} (hx : 1 < x) (hx9 : x ≤ 9)
    (hq : (4 * x ^ 2 + 11 * x + 1) / (x * (11 * x + 5)) ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (7 * x + 1) * ((1 + (1 / x + hsKs x * (1 - q))) *
        (6 + (1 / x + hsKs x * (1 - q)) - 5 * (1 / x + hsKs x * (1 - q)) * q - q ^ 2 - q)) *
        ((2 * q - (1 / x + hsKs x * (1 - q))) * x - q ^ 2) -
      4 * (x + 1) * q * (x - q) *
        (6 * ((1 / x + hsKs x * (1 - q)) + q + 2) * (1 - (1 / x + hsKs x * (1 - q)) * q) -
          (1 + (1 / x + hsKs x * (1 - q))) *
            (6 + (1 / x + hsKs x * (1 - q)) - 5 * (1 / x + hsKs x * (1 - q)) * q - q ^ 2 - q)) := by
  sorry

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
  sorry

/-- **The upper-barrier contact, `k = 9/8`** (`GLOBAL_UPPER_ORDER` (14)-(15)): as
`hs_upper_contact_54` with `k = 9/8`, `1 < x ≤ 5`, `(9x + 8)/(17x) ≤ q ≤ 1`. Status: stable. -/
theorem hs_upper_contact_98 {x q : ℝ} (hx : 1 < x) (hx5 : x ≤ 5)
    (hq : (9 * x + 8) / (17 * x) ≤ q) (hq1 : q ≤ 1) :
    0 < 9 / 8 * q * (3 - (1 / x + 9 / 8 * (1 - q)) + q - 3 * (1 / x + 9 / 8 * (1 - q)) * q) *
        (x - q) -
      (3 + (1 / x + 9 / 8 * (1 - q)) - q - 3 * (1 / x + 9 / 8 * (1 - q)) * q) *
        ((2 * q - (1 / x + 9 / 8 * (1 - q))) * x - q ^ 2) := by
  sorry

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
  sorry

/-- **The quadratic lower-barrier contact** (`RATIONAL_QUADRATIC_ORDER` (3)-(10)): for
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 9/20`, `c = (4x² + 11x + 1)/(7x + 1)`, the barrier
`B(δ) = 1 + cδ + δ²/(1 + 4δ)`, `B'(δ) = c + δ(2 + 4δ)/(1 + 4δ)²`, the contact `q = 1/(1 + δ)`,
`p = B(δ)/(x(1 + δ))`: `N((2q - p)x - q²) - (x - q)(W - N)(B'(δ)/x - p) ≥ 0`
(`= δQ(δ, x)/(x³(1 + δ)⁵(1 + 4δ)⁴(7x + 1)³)`, the 8 × 9 table). Status: stable. -/
theorem hs_quad_contact {x δ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 9 / 20) :
    let c := (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1)
    let q := 1 / (1 + δ)
    let p := (1 + c * δ + δ ^ 2 / (1 + 4 * δ)) / (x * (1 + δ))
    let N := (1 + p) * (6 + p - 5 * p * q - q ^ 2 - q)
    let W := 6 * (p + q + 2) * (1 - p * q)
    0 ≤ N * ((2 * q - p) * x - q ^ 2) -
      (x - q) * (W - N) * ((c + δ * (2 + 4 * δ) / (1 + 4 * δ) ^ 2) / x - p) := by
  sorry

/-! ### The orders -/

/-- **The strong lower order** (`STRONG_ORDER` (1); inventory HS-S01 M5, HS-S4 R4): for
`1 < x ≤ 9`, `1 ≤ α < x ≤ β` with `Sec(1, x, β) = Sec(α, β, x)`,
`α ≥ β/x + k_s(x)(β - x)`, `k_s = 4(x + 1)/(7x + 1)` (barrier `p = ℓ + k_s(1 - z)`, contact
`hs_pade_gap`, `hs_gap_ratio_low`, `hs_strong_contact`, `hs_first_contact`). Status: stable. -/
theorem hs_strong_order {x al be : ℝ} (hx : 1 < x) (hx9 : x ≤ 9) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : be / x + hsKs x * (be - x) ≤ al := by
  sorry

/-- **The global upper order, `5/4`** (`GLOBAL_UPPER_ORDER` (2); inventory HS-S01 M9): for `1 < x`,
`1 ≤ α < x ≤ β` with equal secants, `α ≤ β/x + (5/4)(β - x)` (`hs_chebyshev_gap`,
`hs_upper_contact_54`, first contact from above). Status: stable. -/
theorem hs_upper_order_54 {x al be : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : al ≤ be / x + 5 / 4 * (be - x) := by
  sorry

/-- **The global upper order, `9/8`** (`GLOBAL_UPPER_ORDER` (3); inventory HS-S2 R5, HS-S3 R4): for
`1 < x ≤ 5`, `1 ≤ α < x ≤ β` with equal secants, `α ≤ β/x + (9/8)(β - x)`. Status: stable. -/
theorem hs_upper_order_98 {x al be : ℝ} (hx : 1 < x) (hx5 : x ≤ 5) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : al ≤ be / x + 9 / 8 * (be - x) := by
  sorry

/-- **The extended small-shape upper order** (`SMALL_SHAPE_UPPER_ORDER` (1); inventory HS-S4 R7):
for `1 < x ≤ 13/6`, `1 ≤ α < x ≤ β ≤ (20/19)x` (`0 ≤ δ ≤ 1/19`) with equal secants,
`α ≤ 1 + 3δ`, `δ = β/x - 1` (barrier `k = 2/x`, `hs_small_contact`). Status: stable. -/
theorem hs_small_upper_order {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hδ : be ≤ 20 / 19 * x) (heq : m2Sec 1 x be = m2Sec al be x) :
    al ≤ 1 + 3 * (be / x - 1) := by
  sorry

/-- **The rational quadratic order** (`RATIONAL_QUADRATIC_ORDER` (1); inventory HS-S3 R5): for
`2 ≤ x ≤ 13/6`, `1 ≤ α < x ≤ β` with equal secants, `δ = β/x - 1`,
`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`, `c(x) = (4x² + 11x + 1)/(7x + 1)` (`hs_strong_order` for the domain
`δ < 9/20`, `hs_quad_contact`). Status: stable. -/
theorem hs_quad_order {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) :
    1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) +
        (be / x - 1) ^ 2 / (1 + 4 * (be / x - 1)) ≤ al := by
  sorry

end SmoothedOctagon
