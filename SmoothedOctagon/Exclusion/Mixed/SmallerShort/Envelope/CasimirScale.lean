module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Envelope
public import SmoothedOctagon.Exclusion.Mixed.Short.Calc

/-!
# Gates S1/S4 helpers: the scale form of `Γ_*` and the slope `L(p)`

## Main API

* `hs14_Gs_s`: `16Γ_* = 3 - H² - 2H + 2H(2S - 1 - H)s - H²s²`, `s = q/(α²(1 - q))`,
  `H = S(U(1/S) - u)`.
* `hs14_Gs_inc`: `Γ_*(q₂) - Γ_*(q₁) ≤ H(2S - 1)(q₂ - q₁)/(8α²(1 - q₁)(1 - q₂))`.
* `hs14_pL` (the `B₀` form of `pL`), `hs14_Lp_mono` (lowering `β` lowers `L`),
  `hs14_B0_nonneg`, `hs14_Lp_top_pos` (`L > 0` at `β = x`, `u = U(1/S)`).
* `hs14_slope_gen`: `κH(2S - 1) < 3α²L(p)` from its value at `(β₀, u = 3/4)`.
* `hs14_Rs2_inc`: `(R*_2)' > 1` on `(q₁, q₂)` gives `R*_2(q₂) - R*_2(q₁) > q₂ - q₁`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `Γ_*` as a function of `ρ` in the variable `s = ρ/(1 - ρ)`. -/
private theorem hs14_Gs_rho {x u ρ : ℝ} (hx : 0 < x) (hρ : ρ < 1) :
    (4 * u * m2U (ρ * (1 + x)) - (hsE0 x u + ρ * (2 * (1 + x) - 1)) ^ 2) / (16 * (1 - ρ) ^ 2) =
    (3 - ((1 + x) * (m2U (1 / (1 + x)) - u)) ^ 2 -
      2 * ((1 + x) * (m2U (1 / (1 + x)) - u)) +
      2 * ((1 + x) * (m2U (1 / (1 + x)) - u)) * (2 * (1 + x) - 1 -
        (1 + x) * (m2U (1 / (1 + x)) - u)) * (ρ / (1 - ρ)) -
      ((1 + x) * (m2U (1 / (1 + x)) - u)) ^ 2 * (ρ / (1 - ρ)) ^ 2) / 16 := by
  have h1 : (1 - ρ) ≠ 0 := by linarith
  have hS : (1 + x) ≠ 0 := by linarith
  unfold hsE0 m2U
  field_simp
  ring

/-- **`Γ_*` in the variable `s = q/(α²(1 - q))`**. -/
theorem hs14_Gs_s {x al u q : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hq1 : q < 1) :
    hsGs x al u q = (3 - ((1 + x) * (m2U (1 / (1 + x)) - u)) ^ 2 -
      2 * ((1 + x) * (m2U (1 / (1 + x)) - u)) +
      2 * ((1 + x) * (m2U (1 / (1 + x)) - u)) * (2 * (1 + x) - 1 -
        (1 + x) * (m2U (1 / (1 + x)) - u)) * (q / (al ^ 2 * (1 - q))) -
      ((1 + x) * (m2U (1 / (1 + x)) - u)) ^ 2 * (q / (al ^ 2 * (1 - q))) ^ 2) / 16 := by
  have ha2 : 1 ≤ al ^ 2 := by nlinarith
  have hden : 0 < al ^ 2 - (al ^ 2 - 1) * q := by nlinarith
  have h1q : 0 < 1 - q := by linarith
  have hρ1 : hsRhoOf al q < 1 := by
    unfold hsRhoOf; rw [div_lt_one hden]; nlinarith
  have hs : hsRhoOf al q / (1 - hsRhoOf al q) = q / (al ^ 2 * (1 - q)) := by
    unfold hsRhoOf
    have e : al ^ 2 * (1 - q) = (al ^ 2 - (al ^ 2 - 1) * q) - q := by ring
    rw [e]
    have h3 : al ^ 2 - (al ^ 2 - 1) * q - q ≠ 0 := by rw [← e]; positivity
    generalize al ^ 2 - (al ^ 2 - 1) * q = d at hden h3 ⊢
    have h2 : d ≠ 0 := hden.ne'
    field_simp
  unfold hsGs
  rw [hs14_Gs_rho hx hρ1, hs]

/-- **The increment of `Γ_*`**: for `H = S(U(1/S) - u) ≥ 0` and
`0 ≤ q₁ ≤ q₂ < 1`, `Γ_*(q₂) - Γ_*(q₁) ≤ H(2S - 1)/(8α²) · (q₂ - q₁)/((1 - q₁)(1 - q₂))`. -/
theorem hs14_Gs_inc {x al u q₁ q₂ : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hH : u ≤ m2U (1 / (1 + x)))
    (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hq₂ : q₂ < 1) :
    hsGs x al u q₂ - hsGs x al u q₁ ≤ (1 + x) * (m2U (1 / (1 + x)) - u) * (2 * (1 + x) - 1) /
      (8 * al ^ 2) * ((q₂ - q₁) / ((1 - q₁) * (1 - q₂))) := by
  rw [hs14_Gs_s hx hal hq₂, hs14_Gs_s hx hal (by linarith)]
  have ha : 0 < al ^ 2 := by positivity
  have h1 : 0 < 1 - q₁ := by linarith
  have h2 : 0 < 1 - q₂ := by linarith
  have hds : q₂ / (al ^ 2 * (1 - q₂)) - q₁ / (al ^ 2 * (1 - q₁)) =
      (q₂ - q₁) / (al ^ 2 * ((1 - q₁) * (1 - q₂))) := by
    field_simp; ring
  have hs₁ : 0 ≤ q₁ / (al ^ 2 * (1 - q₁)) := by positivity
  have hd : 0 ≤ (q₂ - q₁) / (al ^ 2 * ((1 - q₁) * (1 - q₂))) := by
    apply div_nonneg (by linarith); positivity
  have hrhs : (1 + x) * (m2U (1 / (1 + x)) - u) * (2 * (1 + x) - 1) / (8 * al ^ 2) *
      ((q₂ - q₁) / ((1 - q₁) * (1 - q₂))) = (1 + x) * (m2U (1 / (1 + x)) - u) *
      (2 * (1 + x) - 1) / 8 * ((q₂ - q₁) / (al ^ 2 * ((1 - q₁) * (1 - q₂)))) := by
    field_simp
  rw [hrhs]
  have hH0 : 0 ≤ (1 + x) * (m2U (1 / (1 + x)) - u) := mul_nonneg (by linarith) (by linarith)
  generalize (1 + x) * (m2U (1 / (1 + x)) - u) = H at *
  generalize q₁ / (al ^ 2 * (1 - q₁)) = s₁ at *
  generalize q₂ / (al ^ 2 * (1 - q₂)) = s₂ at *
  generalize (q₂ - q₁) / (al ^ 2 * ((1 - q₁) * (1 - q₂))) = e at *
  have : s₂ = s₁ + e := by linarith
  subst this
  nlinarith [mul_nonneg (mul_nonneg hH0 hH0) hd, mul_nonneg (mul_nonneg (mul_nonneg hH0 hH0) hd) hs₁,
    mul_nonneg (mul_nonneg (mul_nonneg hH0 hH0) hd) hd]

/-! ### The slope `L(p)` -/

/-- **The `B₀` form of the slope**:
`pL = uB₀² + pB₀[(x - 1)/S + H(1 + α⁻²)] + U(p) - u - SHp²/α²`, `B₀ = 1 + p(S - D)/α²`. -/
theorem hs14_pL {x be al u p : ℝ} (hx : 0 < x) (hal : 0 < al) (hp : 0 < p) :
    p * hsLp x be al u p =
      u * (1 + p * ((1 + x) - hsDg x be al) / al ^ 2) ^ 2 +
      p * (1 + p * ((1 + x) - hsDg x be al) / al ^ 2) *
        ((x - 1) / (1 + x) + (1 + x) * (m2U (1 / (1 + x)) - u) * (1 + 1 / al ^ 2)) +
      m2U p - u - (1 + x) * ((1 + x) * (m2U (1 / (1 + x)) - u)) * p ^ 2 / al ^ 2 := by
  have h1 : (1 + x) ≠ 0 := by linarith
  unfold hsLp hsA2 hsA3 hsE0 m2U
  field_simp
  ring

/-- **Lowering `β` lowers `L`**: for
`1 ≤ α ≤ x`, `β' ≤ β`, `0 < p`, `0 ≤ u ≤ U(1/S)` and `B₀(β') ≥ 0`, `L(β') ≤ L(β)`. -/
theorem hs14_Lp_mono {x be be' al u p : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hbb : be' ≤ be) (hp : 0 < p) (hu : 0 ≤ u) (huS : u ≤ m2U (1 / (1 + x)))
    (hB : 0 ≤ 1 + p * ((1 + x) - hsDg x be' al) / al ^ 2) :
    hsLp x be' al u p ≤ hsLp x be al u p := by
  have hal0 : 0 < al := by linarith
  have h1 := hs14_pL (x := x) (be := be) (u := u) (by linarith) hal0 hp
  have h2 := hs14_pL (x := x) (be := be') (u := u) (by linarith) hal0 hp
  have hD : hsDg x be al ≤ hsDg x be' al := by
    unfold hsDg; nlinarith
  have hBB : 1 + p * ((1 + x) - hsDg x be' al) / al ^ 2 ≤
      1 + p * ((1 + x) - hsDg x be al) / al ^ 2 := by
    have : p * ((1 + x) - hsDg x be' al) ≤ p * ((1 + x) - hsDg x be al) :=
      mul_le_mul_of_nonneg_left (by linarith) hp.le
    have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ al ^ 2)
    linarith
  have hc : 0 ≤ (x - 1) / (1 + x) + (1 + x) * (m2U (1 / (1 + x)) - u) * (1 + 1 / al ^ 2) := by
    have : 0 ≤ (x - 1) / (1 + x) := div_nonneg (by linarith) (by linarith)
    have : 0 ≤ (1 + x) * (m2U (1 / (1 + x)) - u) * (1 + 1 / al ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  have key : p * hsLp x be' al u p ≤ p * hsLp x be al u p := by
    rw [h1, h2]
    generalize 1 + p * ((1 + x) - hsDg x be' al) / al ^ 2 = b' at *
    generalize 1 + p * ((1 + x) - hsDg x be al) / al ^ 2 = b at *
    nlinarith [mul_le_mul_of_nonneg_left hBB hu, mul_nonneg hu hB,
      mul_le_mul_of_nonneg_left hBB (mul_nonneg hp.le hc)]
  exact le_of_mul_le_mul_left key hp

/-- **`L > 0` at the upper norm endpoint and `β = x`** (the
quadratic `pL = A₂p² - (1 + A₃)p + 1` with `4UA₂ = 3 + A₃²` decreases in `A₃ ≤ 1 + 2/x` on
`p ≤ 1/2`, and equals `(x² + x + 1)((x + 1)p - x)²/(Ux²(x + 1)²) > 0` at `A₃ = 1 + 2/x`). -/
theorem hs14_Lp_top_pos {x al p : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x) (hp : 0 < p)
    (hp2 : p ≤ 1 / 2) : 0 < hsLp x x al (m2U (1 / (1 + x))) p := by
  have hal0 : 0 < al := by linarith
  have hx0 : 0 < x := by linarith
  have hS : 0 < 1 + x := by linarith
  set U := m2U (1 / (1 + x)) with hUdef
  have hU : U = (x ^ 2 + x + 1) / (1 + x) ^ 2 := by
    rw [hUdef]; unfold m2U; field_simp; ring
  have hU34 : 3 / 4 ≤ U := by
    rw [hU, le_div_iff₀ (by positivity)]; nlinarith
  have hid1 : 4 * U * hsA2 x x al U - hsA3 x x al U ^ 2 = 3 := by
    rw [hU]; unfold hsA2 hsA3 hsE0 hsDg
    field_simp
    ring
  have hid2 : hsA3 x x al U - (1 + 2 / x) =
      -2 * (x - al) * (2 * x ^ 2 - x - al) * (x ^ 2 + x + 1) / (al ^ 2 * x * (x + 1) ^ 2) := by
    rw [hU]; unfold hsA3 hsE0 hsDg
    field_simp
    ring
  have hA3 : hsA3 x x al U ≤ 1 + 2 / x := by
    have : 0 ≤ 2 * (x - al) * (2 * x ^ 2 - x - al) * (x ^ 2 + x + 1) / (al ^ 2 * x * (x + 1) ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by positivity)
    have h := hid2
    rw [neg_mul, neg_mul, neg_mul, neg_div] at h
    linarith
  have hpL : p * hsLp x x al U p = hsA2 x x al U * p ^ 2 - (1 + hsA3 x x al U) * p + 1 := by
    unfold hsLp; field_simp; ring
  have hb3 : 1 + 2 / x < 3 := by
    have : 2 / x < 2 := by rw [div_lt_iff₀ hx0]; linarith
    linarith
  have hGb : 0 < (3 + (1 + 2 / x) ^ 2) * p ^ 2 - 4 * U * (1 + (1 + 2 / x)) * p + 4 * U := by
    have e : (3 + (1 + 2 / x) ^ 2) * p ^ 2 - 4 * U * (1 + (1 + 2 / x)) * p + 4 * U =
        4 * (x ^ 2 + x + 1) * ((x + 1) * p - x) ^ 2 / (x ^ 2 * (x + 1) ^ 2) := by
      rw [hU]; field_simp; ring
    rw [e]
    have hneg : (x + 1) * p - x < 0 := by nlinarith
    have : 0 < ((x + 1) * p - x) ^ 2 := by nlinarith
    apply div_pos (mul_pos (by positivity) this) (by positivity)
  set a := hsA3 x x al U
  set b := 1 + 2 / x
  have hG : (3 + b ^ 2) * p ^ 2 - 4 * U * (1 + b) * p + 4 * U ≤
      (3 + a ^ 2) * p ^ 2 - 4 * U * (1 + a) * p + 4 * U := by
    have e : (3 + a ^ 2) * p ^ 2 - 4 * U * (1 + a) * p + 4 * U -
        ((3 + b ^ 2) * p ^ 2 - 4 * U * (1 + b) * p + 4 * U) = (b - a) * p * (4 * U - (a + b) * p) := by
      ring
    have : 0 ≤ (b - a) * p * (4 * U - (a + b) * p) := by
      apply mul_nonneg (mul_nonneg (by linarith) hp.le)
      nlinarith
    linarith
  have h4 : 0 < 4 * U * (p * hsLp x x al U p) := by
    rw [hpL]
    have : 4 * U * (hsA2 x x al U * p ^ 2 - (1 + a) * p + 1) =
        (3 + a ^ 2) * p ^ 2 - 4 * U * (1 + a) * p + 4 * U := by
      have : 4 * U * hsA2 x x al U = 3 + a ^ 2 := by linarith
      linear_combination p ^ 2 * this
    rw [this]; linarith
  have : 0 < p * hsLp x x al U p := by
    have hU0 : 0 < 4 * U := by linarith
    exact pos_of_mul_pos_right h4 hU0.le
  exact pos_of_mul_pos_right this hp.le

/-- `B₀(β') = 1 + p(S - D(β'))/α² ≥ 0` for `x ≤ β' ≤ β`, `p ≤ α/(α + β)`. -/
theorem hs14_B0_nonneg {x be be' al p : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb' : x ≤ be') (hbb : be' ≤ be) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    0 ≤ 1 + p * ((1 + x) - hsDg x be' al) / al ^ 2 := by
  have hal0 : 0 < al := by linarith
  have hpab : p * (al + be) ≤ al := by
    unfold hsRA at hpr; rwa [le_div_iff₀ (by linarith)] at hpr
  have key : 0 ≤ al ^ 2 + p * ((1 + x) - hsDg x be' al) := by
    unfold hsDg
    nlinarith [mul_le_mul_of_nonneg_left hpab hal0.le, mul_nonneg hp.le (by nlinarith :
      (0 : ℝ) ≤ be' * (2 * x - al) - x), mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ be - be')]
  have : 1 + p * ((1 + x) - hsDg x be' al) / al ^ 2 =
      (al ^ 2 + p * ((1 + x) - hsDg x be' al)) / al ^ 2 := by
    field_simp
  rw [this]; positivity

/-- **The slope inequality from its lower endpoint**: if `κ ≥ 0`, `x ≤ β₀ ≤ β`, `0 < p ≤ α/(α + β)`,
`3/4 ≤ u ≤ U(1/S)` and the inequality `κH(2S - 1) < 3α²L` holds at `(β₀, u = 3/4)`, it holds at
`(β, u)` (lower `β` to `β₀`, affine in `u`, and `hs14_Lp_top_pos` at `u = U(1/S)`). -/
theorem hs14_slope_gen {κ x be be₀ al u p : ℝ} (hx : 1 < x) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb₀ : x ≤ be₀) (hb₀ : be₀ ≤ be) (hp : 0 < p) (hpr : p ≤ hsRA al be)
    (hu : 3 / 4 ≤ u) (huS : u ≤ m2U (1 / (1 + x)))
    (hbot : κ * ((1 + x) * (m2U (1 / (1 + x)) - 3 / 4)) * (2 * (1 + x) - 1) <
      3 * al ^ 2 * hsLp x be₀ al (3 / 4) p) :
    κ * ((1 + x) * (m2U (1 / (1 + x)) - u)) * (2 * (1 + x) - 1) <
      3 * al ^ 2 * hsLp x be al u p := by
  have hal0 : 0 < al := by linarith
  have hS : 0 < 1 + x := by linarith
  set U := m2U (1 / (1 + x)) with hUdef
  have hU34 : 0 < U - 3 / 4 := by
    have : U - 3 / 4 = (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
      rw [hUdef]; unfold m2U; field_simp; ring
    rw [this]; apply div_pos (by nlinarith) (by positivity)
  -- lower β to β₀ at the actual u
  have hm1 : hsLp x be₀ al u p ≤ hsLp x be al u p :=
    hs14_Lp_mono hx hal hax hb₀ hp (by linarith) huS (hs14_B0_nonneg hx hal hax hxb₀ hb₀ hp hpr)
  -- the upper endpoint
  have hp2 : p ≤ 1 / 2 := by
    have : hsRA al be ≤ 1 / 2 := by
      unfold hsRA; rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have htop : 0 < hsLp x be₀ al U p := by
    have h1 := hs14_Lp_top_pos hx hal hax hp hp2
    have h2 : hsLp x x al U p ≤ hsLp x be₀ al U p :=
      hs14_Lp_mono hx hal hax hxb₀ hp (by linarith) le_rfl
        (hs14_B0_nonneg hx hal hax le_rfl (hxb₀.trans hb₀) hp hpr)
    linarith
  -- affine in u
  have haff : (U - 3 / 4) * (κ * ((1 + x) * (U - u)) * (2 * (1 + x) - 1) -
      3 * al ^ 2 * hsLp x be₀ al u p) =
      (U - u) * (κ * ((1 + x) * (U - 3 / 4)) * (2 * (1 + x) - 1) -
        3 * al ^ 2 * hsLp x be₀ al (3 / 4) p) +
      (u - 3 / 4) * (κ * ((1 + x) * (U - U)) * (2 * (1 + x) - 1) -
        3 * al ^ 2 * hsLp x be₀ al U p) := by
    unfold hsLp hsA2 hsA3 hsE0
    ring
  have hneg : κ * ((1 + x) * (U - u)) * (2 * (1 + x) - 1) - 3 * al ^ 2 * hsLp x be₀ al u p < 0 := by
    have h3 : κ * ((1 + x) * (U - U)) * (2 * (1 + x) - 1) - 3 * al ^ 2 * hsLp x be₀ al U p < 0 := by
      simp only [sub_self, mul_zero, zero_mul, zero_sub, neg_lt_zero]; positivity
    have h4 : (U - 3 / 4) * (κ * ((1 + x) * (U - u)) * (2 * (1 + x) - 1) -
        3 * al ^ 2 * hsLp x be₀ al u p) < 0 := by
      rw [haff]
      rcases eq_or_lt_of_le hu with h | h
      · rw [← h]; nlinarith
      · nlinarith
    exact neg_of_mul_neg_right h4 hU34.le
  nlinarith [mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 3 * al ^ 2)]

/-! ### The `τ = 2` residual -/

/-- **The `τ = 2` residual increases faster than `q`**: if
`(R*_2)'(q) = 1/q - (1 + 2A₁ + A₃) + 4qA₂ > 1` on `(q₁, q₂)`, then
`R*_2(q₂) - R*_2(q₁) > q₂ - q₁`. -/
theorem hs14_Rs2_inc {x be al u q₁ q₂ : ℝ} (hrA : 0 < hsRA al be) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hd : ∀ q ∈ Ioo q₁ q₂, 1 < 1 / q - (1 + 2 * hsA1 x be al u + hsA3 x be al u) +
      4 * q * hsA2 x be al u) :
    q₂ - q₁ < hsRs x be al u q₂ 2 - hsRs x be al u q₁ 2 := by
  set A1 := hsA1 x be al u
  set A2 := hsA2 x be al u
  set A3 := hsA3 x be al u
  set rA := hsRA al be
  have hf : ∀ q, hsRs x be al u q 2 - q = (-q * A1 + q ^ 2 * A2) * 2 + 1 / 2 + (u - 1) / rA + rA +
      1 - q - (-hsE0 x u + q * A3) + log (2 * q / rA) - q := by
    intro q; unfold hsRs hsF hsWs hsELs; ring
  have hderiv : ∀ q ∈ Icc q₁ q₂, HasDerivAt (fun q => (-q * A1 + q ^ 2 * A2) * 2 + 1 / 2 +
      (u - 1) / rA + rA + 1 - q - (-hsE0 x u + q * A3) + log (2 * q / rA) - q)
      (1 / q - (1 + 2 * A1 + A3) + 4 * q * A2 - 1) q := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le hq₁ hq.1
    have hl := (((hasDerivAt_id' q).const_mul 2).div_const rA).log (by positivity)
    have hp := ((((((((hasDerivAt_id' q).neg.mul_const A1).add (((hasDerivAt_id' q).pow 2).mul_const
      A2)).mul_const 2).add_const (1 / 2)).add_const ((u - 1) / rA)).add_const rA).add_const 1).sub
      (hasDerivAt_id' q)
    have hp2 := ((hp.sub (((hasDerivAt_id' q).mul_const A3).const_add (-hsE0 x u))).add hl).sub
      (hasDerivAt_id' q)
    convert hp2 using 1
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have := ss_lt_of_deriv hq hderiv (fun q hq => by have := hd q hq; linarith)
  rw [← hf, ← hf] at this
  linarith

end SmoothedOctagon
