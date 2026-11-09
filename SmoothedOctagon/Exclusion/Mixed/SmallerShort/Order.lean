module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Barrier
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Contacts
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Upper
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.SmallUpper

/-!
# Smaller-short window: the equal-secant orders

The order relations between the shape coordinates `x = C/a`, `α = A/a`, `β = B/a` of a short bridge
with equal turn secants `Sec(1, x, β) = Sec(α, β, x)`: a strong lower order, two global upper
orders, a small-shape upper order and a rational quadratic lower order. The barrier argument runs
on the normalized comparison function `Φ(z) = avg(ℓ + k(1 - z), z) - avg(ℓ, 1/z)` of
`ss_order_norm` with the first-contact lemma `ss_first_contact`; at a zero of `Φ` the sign of `Φ'`
is the contact inequality below. The barrier machinery (any differentiable barrier, so also the
non-affine barrier of `ss_quad_order`) is `SmallerShort/Order/Barrier.lean`. The global
upper contacts use the integral comparisons and positive products in `Order/Upper.lean`.
The small-box upper order uses tilted weights and monotonicity in `Order/SmallUpper.lean`;
the lower contact inequalities are in `Order/Contacts.lean`.

## Main API

* Gap ratios: `ss_pade_gap`, `ss_gap_ratio_low`, `ss_gap_ratio_lower`.
* Contact inequalities: `ss_strong_contact`, `ss_upper_contact_54`, `ss_upper_contact_98`,
  `ss_small_contact_one`, `ss_small_contact_max`, `ss_quad_contact`.
* Orders: `ss_strong_order` (`α ≥ β/x + k_s(x)(β - x)`), `ss_upper_order_54`, `ss_upper_order_98`,
  `ss_small_upper_order` (`α ≤ 1 + 3δ`), `ss_quad_order` (`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`).
* Helpers: `ord_upper_contact_of_ratio`, `ord_affine_deriv`,
  `ord_affine_lt` (affine barriers), `ord_contact_pos` (signs of `M`, `ξ`, `η`, `N` at a contact).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Gap ratios of the averaged threshold `avg(p, q) = Sec(p, 1, q)` -/

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

/-! ### Contact inequalities -/

/-- **The strong lower-barrier contact**: for `1 < x ≤ 9`,
`q_min = (4x² + 11x + 1)/(x(11x + 5)) ≤ q ≤ 1`, `p = 1/x + k_s(x)(1 - q)`:
`(7x + 1)N((2q - p)x - q²) - 4(x + 1)q(x - q)(W - N) ≥ 0` (`= (1 - q)(x + 1)P(q, x)/(x²(7x + 1)²)`),
since `P ≥ 0` on `[q_min, 1]` by its quartic Bernstein form (`ord_strong_bern`, five coefficients
positive for every `x > 1`); `x ≤ 9` is not used. -/
theorem ss_strong_contact {x q : ℝ} (hx : 1 < x) (hx9 : x ≤ 9)
    (hq : (4 * x ^ 2 + 11 * x + 1) / (x * (11 * x + 5)) ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (7 * x + 1) * ((1 + (1 / x + ssKs x * (1 - q))) *
        (6 + (1 / x + ssKs x * (1 - q)) - 5 * (1 / x + ssKs x * (1 - q)) * q - q ^ 2 - q)) *
        ((2 * q - (1 / x + ssKs x * (1 - q))) * x - q ^ 2) -
      4 * (x + 1) * q * (x - q) *
        (6 * ((1 / x + ssKs x * (1 - q)) + q + 2) * (1 - (1 / x + ssKs x * (1 - q)) * q) -
          (1 + (1 / x + ssKs x * (1 - q))) *
            (6 + (1 / x + ssKs x * (1 - q)) - 5 * (1 / x + ssKs x * (1 - q)) * q - q ^ 2 - q)) := by
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
  have hpos := ord_bern4_pos hT hS1 hTS1
    (b0 := 18 * (x + 1) ^ 2 * (7 * x + 1) * (11 * x + 1) * (15 * x + 1) ^ 2 *
      (4 * x ^ 2 + 11 * x + 1) * x ^ 2)
    (b1 := (x + 1) * (15 * x + 1) *
      (82008 * x ^ 5 + 141569 * x ^ 4 + 62540 * x ^ 3 + 10134 * x ^ 2 + 692 * x + 17) * x)
    (b3 := 2 * (10742 * x ^ 4 + 10397 * x ^ 3 + 1685 * x ^ 2 + 87 * x + 1))
    (b4 := 2 * (313 * x ^ 2 + 38 * x + 1))
    (by positivity) (by positivity) hb2 (by positivity) (by positivity)
  rw [← ord_strong_bern x q] at hpos
  have hP := pos_of_mul_pos_right hpos (by positivity)
  have hR := mul_nonneg (mul_nonneg hS1 (by linarith : (0:ℝ) ≤ x + 1)) hP.le
  rw [← ord_strong_eq hx] at hR
  exact nonneg_of_mul_nonneg_right hR (by positivity)

/-- **The quadratic lower-barrier contact**: for
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 9/20`, `c = (4x² + 11x + 1)/(7x + 1)`, the barrier
`B(δ) = 1 + cδ + δ²/(1 + 4δ)`, `B'(δ) = c + δ(2 + 4δ)/(1 + 4δ)²`, the contact `q = 1/(1 + δ)`,
`p = B(δ)/(x(1 + δ))`: `N((2q - p)x - q²) - (x - q)(W - N)(B'(δ)/x - p) ≥ 0`
(`= δQ(δ, x)/(x³(1 + δ)⁵(1 + 4δ)⁴(7x + 1)³)`, the 8 × 9 table).
Proof: `Q ≥ 0` row by row of the table (`ord_quad_Q_nonneg`); only `X = x - 2 ≥ 0` is used. -/
theorem ss_quad_contact {x δ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
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
  have key := ord_quad_eq (c := c) (q := q) (p := p) (N := N) (W := W) hx0 hδ rfl rfl rfl rfl rfl
  have h := mul_nonneg hδ (ord_quad_Q_nonneg hx hδ hδ2)
  rw [← key] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

/-! ### The orders -/

/-- The derivative of an affine barrier `z ↦ ℓ + k(1 - z)`. -/
theorem ord_affine_deriv (ℓ k z : ℝ) : HasDerivAt (fun z => ℓ + k * (1 - z)) (-k) z := by
  have := (((hasDerivAt_id' z).const_sub 1).const_mul k).const_add ℓ
  rwa [mul_neg_one] at this

/-- An affine barrier with slope `-k > -1` below the diagonal at `q₁` stays below it on
`[q₁, 1]`. -/
theorem ord_affine_lt {ℓ k q₁ : ℝ} (hk : -1 < k) (h : ℓ + k * (1 - q₁) < q₁) :
    ∀ z ∈ Icc q₁ 1, ℓ + k * (1 - z) < z := by
  intro z hz
  have := mul_nonneg (by linarith : (0:ℝ) ≤ k + 1) (sub_nonneg.2 hz.1)
  linarith

/-- The contact data of an affine lower barrier `p = 1/x + k(1 - z)` below the diagonal. -/
theorem ord_contact_pos {x p z : ℝ} (hx : 1 < x) (hp : 0 < p) (hpz : p < z) (hz : z ≤ 1) :
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

/-- **The strong lower order**: for
`1 < x ≤ 9`, `1 ≤ α < x ≤ β` with `Sec(1, x, β) = Sec(α, β, x)`,
`α ≥ β/x + k_s(x)(β - x)`, `k_s = 4(x + 1)/(7x + 1)` (barrier `p = ℓ + k_s(1 - z)`, contact
`ss_pade_gap`, `ss_gap_ratio_low`, `ss_strong_contact`, `ss_first_contact`). -/
theorem ss_strong_order {x al be : ℝ} (hx : 1 < x) (hx9 : x ≤ 9) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) : be / x + ssKs x * (be - x) ≤ al := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hk : 0 ≤ ssKs x := by unfold ssKs; positivity
  have hP := ord_order_lower (P := fun z => 1 / x + ssKs x * (1 - z)) (P' := fun _ => -ssKs x)
    (p₁ := al / be) (q₁ := x / be) hx (div_pos hal0 hbe0) (div_lt_div_of_pos_right hax hbe0)
    ((div_le_one hbe0).2 hxb) (ord_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => ord_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) ?_
  · have e : be / x + ssKs x * (be - x) = be * (1 / x + ssKs x * (1 - x / be)) := by
      field_simp
    rw [e]
    calc be * (1 / x + ssKs x * (1 - x / be)) ≤ be * (al / be) :=
          mul_le_mul_of_nonneg_left hP hbe0.le
      _ = al := by field_simp
  intro z hz hPz hzeq
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + ssKs x * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  obtain ⟨hM, hξ, hη, hN⟩ := ord_contact_pos hx hp0 hPz hz1
  have hq : (4 * x ^ 2 + 11 * x + 1) / (x * (11 * x + 5)) ≤ z := by
    have e : 1 / x + ssKs x * (1 - z) =
        (7 * x + 1 + 4 * (x + 1) * x * (1 - z)) / (x * (7 * x + 1)) := by
      unfold ssKs; field_simp
    rw [e, div_lt_iff₀ (by positivity)] at hPz
    rw [div_le_iff₀ (by positivity)]
    linarith only [hPz]
  have hcont := ss_strong_contact hx hx9 hq hz1
  have hgap := ss_gap_ratio_low hp0 hPz hz1
  set pz := 1 / x + ssKs x * (1 - z) with hpz
  set N := (1 + pz) * (6 + pz - 5 * pz * z - z ^ 2 - z) with hNdef
  set W := 6 * (pz + z + 2) * (1 - pz * z) with hWdef
  set M := (2 * z - pz) * x - z ^ 2 with hMdef
  have hcon : ssKs x * z * (x - z) * (W - N) ≤ N * M := by
    have h7 : 0 < 7 * x + 1 := by linarith
    have ek : ssKs x * (7 * x + 1) = 4 * (x + 1) := by unfold ssKs; field_simp
    have key : (7 * x + 1) * (N * M - ssKs x * z * (x - z) * (W - N)) =
        (7 * x + 1) * N * M - 4 * (x + 1) * z * (x - z) * (W - N) := by rw [← ek]; ring
    rw [← key] at hcont
    have := nonneg_of_mul_nonneg_right hcont h7
    linarith only [this]
  have := ord_lower_alg hgap hcon hM hξ hη hN
  exact lt_of_eq_of_lt (by ring) this

/-- The `5/4` upper order from the integral gap bound and first contact. -/
theorem ss_upper_order_54 {x al be : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al < x)
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
  refine ord_order_upper (P := fun z => 1 / x + 5 / 4 * (1 - z)) (P' := fun _ => -(5 / 4))
    (q₁ := x / be) hx hp₁ hq₁ (ord_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => ord_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) (ord_affine_lt (by norm_num) hlt) ?_
  intro z hz _
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + 5 / 4 * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hPz : 1 / x + 5 / 4 * (1 - z) < z :=
    ord_affine_lt (by norm_num) hlt z (Ioc_subset_Icc_self hz)
  have hgap := ss_gap_ratio_lower hp0 hPz hz1
  have hz0 : 0 < z := hp0.trans hPz
  have hxz : 0 < x - z := by linarith
  have hR : (3 - 2 * (1 / x + 5 / 4 * (1 - z)) - z) /
      (3 - (1 / x + 5 / 4 * (1 - z)) - 2 * z) <
      (ss_gB 1 (1 / x + 5 / 4 * (1 - z)) - m2Sec (1 / x + 5 / 4 * (1 - z)) 1 z) /
      (m2Sec (1 / x + 5 / 4 * (1 - z)) 1 z - ss_gB 1 z) := by
    linarith only [hgap, hPz]
  simpa only [neg_neg] using
    ord_upper_contact_of_ratio (k := 5 / 4) hp0 hPz hz1 (by positivity)
      hR (ss_upper_contact_54 hx hz1 hPz)

/-- The `9/8` upper order for `x ≤ 5`, using the refined integral gap bound. -/
theorem ss_upper_order_98 {x al be : ℝ} (hx : 1 < x) (hx5 : x ≤ 5) (hal : 1 ≤ al) (hax : al < x)
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
  refine ord_order_upper (P := fun z => 1 / x + 9 / 8 * (1 - z)) (P' := fun _ => -(9 / 8))
    (q₁ := x / be) hx hp₁ hq₁ (ord_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => ord_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) (ord_affine_lt (by norm_num) hlt) ?_
  intro z hz _
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + 9 / 8 * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hPz : 1 / x + 9 / 8 * (1 - z) < z :=
    ord_affine_lt (by norm_num) hlt z (Ioc_subset_Icc_self hz)
  have hgap := ss_gap_ratio_lower hp0 hPz hz1
  have hz0 : 0 < z := hp0.trans hPz
  have hxz : 0 < x - z := by linarith
  simpa only [neg_neg] using
    ord_upper_contact_of_ratio (k := 9 / 8) hp0 hPz hz1 (by positivity)
      hgap (ss_upper_contact_98 hx hx5 hz1 hPz)

/-- The unit-slope upper order on the middle range of the small box. -/
private theorem small_order_one {x al be : ℝ} (hx : 16/9 ≤ x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (hδ : be ≤ 20/19*x) (heq : m2Sec 1 x be = m2Sec al be x) : al ≤ be / x + 1 * (be - x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hq19 : 19/20 ≤ x/be := by rw [le_div_iff₀ hbe0]; linarith only [hδ]
  have hp₁ : al / be < x / be := div_lt_div_of_pos_right hax hbe0
  have hq₁ : x / be ≤ 1 := (div_le_one hbe0).2 hxb
  have e : be / x + 1 * (be - x) = be * (1 / x + 1 * (1 - x / be)) := by field_simp
  rw [e]
  suffices h : al / be ≤ 1 / x + 1 * (1 - x / be) by
    calc al = be * (al / be) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hbe0.le
  rcases le_or_gt (x / be) (1 / x + 1 * (1 - x / be)) with hle | hlt
  · linarith
  refine ord_order_upper (P := fun z => 1 / x + 1 * (1 - z)) (P' := fun _ => -(1))
    (q₁ := x / be) hx1 hp₁ hq₁ (ord_norm_eq hx0 hal0 hbe0 heq) (by simp)
    (fun z _ => ord_affine_deriv _ _ z) (fun z hz => by
      have : 0 ≤ 1 - z := by linarith [hz.2]
      positivity) (ord_affine_lt (by norm_num) hlt) ?_
  intro z hz _
  have hz1 := hz.2
  have hp0 : 0 < 1 / x + 1 * (1 - z) := by
    have : 0 ≤ 1 - z := by linarith
    positivity
  have hPz : 1 / x + 1 * (1 - z) < z :=
    ord_affine_lt (by norm_num) hlt z (Ioc_subset_Icc_self hz)
  have hz19 : 19/20 ≤ z := hq19.trans hz.1.le
  simpa only [one_mul,neg_neg,add_sub_assoc] using ss_small_contact_one hx hx2 hz19 hz1

/-- The small-box upper order. The `9/8` global order covers `x ≤ 16/9`;
the half tilt covers `16/9 ≤ x ≤ 2`; the maximal tilt covers `2 ≤ x ≤ 13/6`. -/
theorem ss_small_upper_order {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hδ : be ≤ 20 / 19 * x) (heq : m2Sec 1 x be = m2Sec al be x) :
    al ≤ 1 + 3 * (be / x - 1) := by
  by_cases hxsmall : x ≤ 16/9
  · have hs := ss_upper_order_98 hx (by linarith) hal hax hxb heq
    have hx0 : 0 < x := by linarith
    have hd : 0 ≤ be/x-1 := by rw [sub_nonneg,le_div_iff₀ hx0]; linarith only [hxb]
    have hid : be/x+(9/8)*(be-x) = 1+(1+9*x/8)*(be/x-1) := by field_simp; ring
    rw [hid] at hs
    have hm := mul_le_mul_of_nonneg_right (show 1+9*x/8 ≤ 3 by linarith only [hxsmall]) hd
    linarith only [hs,hm]
  by_cases hxmid : x ≤ 2
  · have hs := small_order_one (by linarith : 16/9 ≤ x) hxmid hal hax hxb hδ heq
    have hx0 : 0 < x := by linarith
    have hd : 0 ≤ be/x-1 := by rw [sub_nonneg,le_div_iff₀ hx0]; linarith only [hxb]
    have hid : be/x+1*(be-x) = 1+(1+x)*(be/x-1) := by field_simp; ring
    rw [hid] at hs
    have hm := mul_le_mul_of_nonneg_right (show 1+x ≤ 3 by linarith only [hxmid]) hd
    linarith only [hs,hm]
  have hxlarge : 2 ≤ x := le_of_lt (lt_of_not_ge hxmid)
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
    exact ord_affine_lt (by have : 0 < 2 / x := by positivity
                            linarith) hlt z hz
  refine ord_order_upper (P := fun z => (3 - 2 * z) / x) (P' := fun _ => -(2 / x))
    (q₁ := x / be) hx hp₁ hq₁ (ord_norm_eq hx0 hal0 hbe0 heq) (by norm_num)
    (fun z _ => by
      have := (((hasDerivAt_id' z).const_mul 2).const_sub 3).div_const x
      convert this using 1
      ring)
    (fun z hz => div_pos (by linarith [hz.2]) hx0) hlt' ?_
  intro z hz _
  simpa only [neg_neg] using ss_small_contact_max hxlarge hx2
    (hq₁19.trans hz.1.le) hz.2

/-- The quadratic barrier `B(δ) = 1 + c(x)δ + δ²/(1 + 4δ)` of the rational quadratic order. -/
noncomputable def ordQB (x d : ℝ) : ℝ :=
  1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * d + d ^ 2 / (1 + 4 * d)

/-- `B'(δ) = c(x) + δ(2 + 4δ)/(1 + 4δ)²`. -/
noncomputable def ordQB' (x d : ℝ) : ℝ :=
  (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + d * (2 + 4 * d) / (1 + 4 * d) ^ 2

theorem ordQB_hasDerivAt {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) :
    HasDerivAt (ordQB x) (ordQB' x d) d := by
  have h1 := ((hasDerivAt_id' d).const_mul ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1))).const_add 1
  have h2 := (hasDerivAt_pow 2 d).div (((hasDerivAt_id' d).const_mul 4).const_add 1)
    (by positivity)
  refine (h1.add h2).congr_deriv ?_
  have : 1 + 4 * d ≠ 0 := by positivity
  unfold ordQB'
  push_cast
  field_simp
  ring

theorem ordQB_pos {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) : 0 < ordQB x d := by
  unfold ordQB
  have : 0 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * d := by positivity
  have : 0 ≤ d ^ 2 / (1 + 4 * d) := by positivity
  linarith

/-- **The quadratic contact** at `z = 1/(1 + δ)` (`ss_quad_contact`, `ord_lower_alg`): the lower
contact inequality of `ord_order_lower` for the barrier `P(z) = zB(1/z - 1)/x`. -/
theorem ord_quad_contact_at {x z : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hz0 : 0 < z)
    (hz1 : z ≤ 1) (hδ2 : z⁻¹ - 1 ≤ 9 / 20) (hPz : z * ordQB x (z⁻¹ - 1) / x < z) :
    -((1 * ordQB x (z⁻¹ - 1) + z * (ordQB' x (z⁻¹ - 1) * -(z ^ 2)⁻¹)) / x) *
        (ss_gB 1 (z * ordQB x (z⁻¹ - 1) / x) - m2Sec (z * ordQB x (z⁻¹ - 1) / x) 1 z) * z *
        (x - z) <
      (m2Sec (z * ordQB x (z⁻¹ - 1) / x) 1 z - ss_gB 1 z) *
        ((2 * z - z * ordQB x (z⁻¹ - 1) / x) * x - z ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz1
  have hq : 0 ≤ (1 + ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) *
        (6 + ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) -
          5 * (ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * (1 / (1 + (z⁻¹ - 1))) -
          (1 / (1 + (z⁻¹ - 1))) ^ 2 - 1 / (1 + (z⁻¹ - 1))) *
        ((2 * (1 / (1 + (z⁻¹ - 1))) - ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * x -
          (1 / (1 + (z⁻¹ - 1))) ^ 2) -
      (x - 1 / (1 + (z⁻¹ - 1))) *
        (6 * (ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) + 1 / (1 + (z⁻¹ - 1)) + 2) *
            (1 - ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) * (1 / (1 + (z⁻¹ - 1)))) -
          (1 + ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) *
            (6 + ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) -
              5 * (ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) * (1 / (1 + (z⁻¹ - 1))) -
              (1 / (1 + (z⁻¹ - 1))) ^ 2 - 1 / (1 + (z⁻¹ - 1)))) *
        (ordQB' x (z⁻¹ - 1) / x - ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1)))) :=
    ss_quad_contact hx hx2 hδ0 hδ2
  have e1 : 1 / (1 + (z⁻¹ - 1)) = z := by rw [add_sub_cancel, one_div, inv_inv]
  have e2 : ordQB x (z⁻¹ - 1) / (x * (1 + (z⁻¹ - 1))) = z * ordQB x (z⁻¹ - 1) / x := by
    rw [add_sub_cancel]; field_simp
  have hBpos := ordQB_pos hx0 hδ0
  rw [e1, e2] at hq
  generalize ordQB x (z⁻¹ - 1) = Bv at hq hPz hBpos ⊢
  generalize ordQB' x (z⁻¹ - 1) = Bd at hq ⊢
  have hp0 : 0 < z * Bv / x := by positivity
  have hgap := ss_gap_ratio_low hp0 hPz hz1
  obtain ⟨hM, hξ, hη, hN⟩ := ord_contact_pos (x := x) (by linarith) hp0 hPz hz1
  have key := ord_lower_alg (B := (x - z) * (Bd / x - z * Bv / x)) hgap (by linarith) hM hξ hη hN
  generalize ss_gB 1 (z * Bv / x) - m2Sec (z * Bv / x) 1 z = ξ at key ⊢
  have e3 : -((1 * Bv + z * (Bd * -(z ^ 2)⁻¹)) / x) * ξ * z * (x - z) =
      (x - z) * (Bd / x - z * Bv / x) * ξ := by
    field_simp
    ring
  rw [e3]
  exact key

/-- **The rational quadratic order**: for
`2 ≤ x ≤ 13/6`, `1 ≤ α < x ≤ β` with equal secants, `δ = β/x - 1`,
`α ≥ 1 + c(x)δ + δ²/(1 + 4δ)`, `c(x) = (4x² + 11x + 1)/(7x + 1)` (`ss_strong_order` for the domain
`δ < 9/20`, `ss_quad_contact`). Proof: first contact for the non-affine barrier
`p = zB(1/z - 1)/x` (`ord_order_lower`); the case where the barrier meets the diagonal is excluded
by the last-meeting-point argument of `ss_order_norm`. -/
theorem ss_quad_order {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (heq : m2Sec 1 x be = m2Sec al be x) :
    1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) +
        (be / x - 1) ^ 2 / (1 + 4 * (be / x - 1)) ≤ al := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hc0 : 0 < (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) := by positivity
  -- the strong order gives `δ₁ = β/x - 1 ≤ 9/20`
  have hδ₁0 : 0 ≤ be / x - 1 := by rw [sub_nonneg, le_div_iff₀ hx0]; linarith
  have hδ₁ : be / x - 1 ≤ 9 / 20 := by
    have hs := ss_strong_order hx1 (by linarith) hal hax hxb heq
    have e : be / x + ssKs x * (be - x) =
        1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) := by
      unfold ssKs; field_simp; ring
    rw [e] at hs
    by_contra h
    push Not at h
    have k1 := mul_lt_mul_of_pos_left h hc0
    have k2 : x - 1 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (9 / 20) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x)]
    linarith
  -- the barrier `P(z) = zB(1/z - 1)/x`, `B(δ) = 1 + cδ + δ²/(1 + 4δ)`
  have hP := ord_order_lower (P := fun z => z * ordQB x (z⁻¹ - 1) / x)
    (P' := fun z => (1 * ordQB x (z⁻¹ - 1) + z * (ordQB' x (z⁻¹ - 1) * -(z ^ 2)⁻¹)) / x)
    (p₁ := al / be) (q₁ := x / be) hx1 (div_pos hal0 hbe0) (div_lt_div_of_pos_right hax hbe0)
    ((div_le_one hbe0).2 hxb) (ord_norm_eq hx0 hal0 hbe0 heq) (by simp [ordQB])
    (fun z hz => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans_le hz.1
      have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz.2
      exact ((hasDerivAt_id' z).mul ((ordQB_hasDerivAt hx0 hδ0).comp z
        ((hasDerivAt_inv hz0.ne').sub_const 1))).div_const x)
    (fun z hz => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans_le hz.1
      have hδ0 : 0 ≤ z⁻¹ - 1 := by rw [sub_nonneg]; exact (one_le_inv₀ hz0).2 hz.2
      exact div_pos (mul_pos hz0 (ordQB_pos hx0 hδ0)) hx0)
    (fun z hz hPz _ => by
      have hz0 : 0 < z := (div_pos hx0 hbe0).trans hz.1
      refine ord_quad_contact_at hx hx2 hz0 hz.2 ?_ hPz
      have : z⁻¹ < be / x := by
        rw [← inv_div]; exact inv_strictAnti₀ (div_pos hx0 hbe0) hz.1
      linarith)
  rw [inv_div] at hP
  have e : x / be * ordQB x (be / x - 1) / x = ordQB x (be / x - 1) / be := by field_simp
  rw [e] at hP
  exact (div_le_div_iff_of_pos_right hbe0).1 hP

end SmoothedOctagon
