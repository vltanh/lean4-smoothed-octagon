module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CasimirScale
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.NormEndpoint
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CapData
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.DerivativeRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace

/-!
# Smaller-short window, lower ratio: `x > 2`

This module excludes `1 < x ≤ 2`. Assuming it, the corrected envelope cap
`Γ_actual ≥ Γ_* - (7/96)R*_τ` (`SmallerShortData.lr_cap_env`, from the retained root bound `lr_root_cap` and
the derivative ratio `lr_ratio`), the scale motions at fixed `p` and at `τ = 2` (`lr_scale_dec`,
`lr_tau2_dec`) reach a face `q = q_c ≤ 1/7` or `q = 1/7 ≤ q_c`, where the terminal face signs
`lr_central_face`, `lr_outer_face` give `Γ_* - (7/96)R*_τ > 9193/50000`, contradicting `cas_lt`.

## Main API

* Supporting modules: `SmallerShort/Envelope/CasimirScale` (the scale form of `Γ_*`, the slope
  `L(p)`, the `τ = 2` residual), `SmallerShort/Envelope/NormEndpoint` (the lower norm endpoints of
  the slope inequalities), `SmallerShort/Envelope/Cap` and `SmallerShort/Envelope/CapData` (the
  corrected envelope cap), `SmallerShort/LowerRatio/DerivativeRatio` (the ratio `7/96` on the
  order strip).

* `lr_root_cap` (the retained root bound), `lr_ratio` (the derivative ratio `7/96`),
  `lr_slope` (the sharper slope), `lr_scale_dec` (the fixed-`p` decrease), `lr_tau2_dec` (the
  `τ = 2` decrease), `lr_u_ell` (the β-dependent ceiling).
* `SmallerShortData.lr_cap_env` (the corrected envelope cap).
* Terminal face signs, proved in `SmallerShort/LowerRatio/CentralFace` and `SmallerShort/LowerRatio/OuterFace`:
  `lr_central_face`, `lr_outer_face`.
* The bound: `SmallerShortData.two_lt_ratio`, `M2Short.two_lt_ratio`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The retained incoming deficit at the actual root**: if `0 < r_A < 1/2`, `τ > 2`, `0 < q`,
`τq < r_A`, `u ≤ U(r_A)`, `w ≤ U(1/τ)` and
`E_L = (w - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q + log(τq/r_A)`, then `E_L ≤ 3q - J_A`,
`J_A = (U(r_A) - u)/r_A` (`ss_E_le_three` with the norm `U(r_A)`). -/
theorem lr_root_cap {rA τ q u w EL : ℝ} (hrA : 0 < rA) (hrA2 : rA < 1 / 2) (hτ : 2 < τ)
    (hq : 0 < q) (hτq : τ * q < rA) (hu : u ≤ m2U rA) (hw : w ≤ m2U (1 / τ))
    (hEL : EL = (w - 1) * τ + 1 / τ + (u - 1) / rA + rA + 1 - q + log (τ * q / rA)) :
    EL ≤ 3 * q - (m2U rA - u) / rA :=
  env_root_cap hrA hrA2.le hτ.le hq hτq.le hw hEL

/-- **The derivative ratio is at most `7/96`**: for `1 < x ≤ 2`, `1 ≤ α < x ≤ β`, `D > 0`,
`3/4 ≤ u ≤ u₀(x)`, `u ≤ U(r_A)`, `ρ > 0`, `q = α²λρ ≤ 1/7`, `2 ≤ τ`, `τq < r_A`,
`0 < t ≤ 1/(1 + x)`, `b = λt - d` with `1 + τb > 0`, and any `E_L ≤ 3q - J_A`:
`2ub + E_L ≤ (7/12)(1 - q)²(1 + τb)`, i.e. `Γ_v/(R_τ)_v = (2ub + E_L)/(8(1 - q)²(1 + τb)) ≤ 7/96`.
The order strip `x + (8/17)(α - 1) ≤ β ≤ x + (4/5)(α - 1)` (from the strong and `9/8` orders) is a
hypothesis. -/
theorem lr_ratio {x be al u rho τ t EL : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hD : 0 < ssDg x be al) (hu : 3 / 4 ≤ u) (hu0 : u ≤ ssU0 x)
    (hurA : u ≤ m2U (ssRA al be)) (hρ : 0 < rho) (hq7 : ssQ al rho ≤ 1 / 7) (hτ : 2 ≤ τ)
    (hτq : τ * ssQ al rho < ssRA al be) (ht : 0 < t) (htr : t ≤ 1 / (1 + x))
    (hB : 0 < 1 + τ * (ssLam al rho * t - ssLam al rho * rho * ssDg x be al))
    (hEL : EL ≤ 3 * ssQ al rho - (m2U (ssRA al be) - u) / ssRA al be)
    (hlo : x + 8 / 17 * (al - 1) ≤ be) (hhi : be ≤ x + 4 / 5 * (al - 1)) :
    2 * u * (ssLam al rho * t - ssLam al rho * rho * ssDg x be al) + EL ≤
      7 / 12 * (1 - ssQ al rho) ^ 2 *
        (1 + τ * (ssLam al rho * t - ssLam al rho * rho * ssDg x be al)) :=
  lr_ratio_strip hx hx2 hal hax hxb hD hu hu0 hurA hρ hq7 hτ hτq ht htr hB hEL hlo hhi

/-- **The sharper slope**: for `1 < x ≤ 2`, `1 ≤ α ≤ x`, `β ≥ x + 8x(α - 1)/(9x + 8)`,
`0 < p ≤ α/(α + β)`, `3/4 ≤ u ≤ U(1/S)`: `3α²L(p) > 7J(2S - 1)`, `J = S[U(1/S) - u]`.
Proof: `env_slope_gen` (lower `β`, affine in `u`) with the identity `env_bot_sharp`; the
upper norm endpoint by `env_Lp_top_pos` (monotone in `A₃`). -/
theorem lr_slope {x be al u p : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be) (hp : 0 < p) (hpr : p ≤ ssRA al be)
    (hu : 3 / 4 ≤ u) (huS : u ≤ m2U (1 / (1 + x))) :
    7 * ((1 + x) * (m2U (1 / (1 + x)) - u)) * (2 * (1 + x) - 1) < 3 * al ^ 2 * ssLp x be al u p := by
  have hal0 : 0 < al := by linarith
  have hM : 0 < 9 * x + 8 := by linarith
  have hb0 : x + 8 * x * (al - 1) / (9 * x + 8) = x * (9 * x + 8 * al) / (9 * x + 8) := by
    field_simp; ring
  rw [hb0] at hb
  have hxb0 : x ≤ x * (9 * x + 8 * al) / (9 * x + 8) := by
    rw [le_div_iff₀ hM]; nlinarith
  have hpr' : p ≤ al / (al + x * (9 * x + 8 * al) / (9 * x + 8)) := by
    refine hpr.trans ?_
    unfold ssRA
    exact div_le_div_of_nonneg_left hal0.le (by positivity) (by linarith)
  exact env_slope_gen hx hal hax hxb0 hb hp hpr hu huS (env_bot_sharp hx hal hax hp hpr')

/-- **The fixed-`p` decrease**: under the hypotheses of `lr_slope`,
`q ↦ Γ_*(q) - (7/96)R*_{p/q}(q)` is strictly decreasing on `(0, 1/7]`
(`∂_q Γ_* ≤ J(2S - 1)/(8α²(1 - q)²) < (7/96)L(p)`). -/
theorem lr_scale_dec {x be al u p q₁ q₂ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be) (hp : 0 < p)
    (hpr : p ≤ ssRA al be) (hu : 3 / 4 ≤ u) (huS : u ≤ m2U (1 / (1 + x))) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    ssGs x al u q₂ - 7 / 96 * ssPhi x be al u p 0 q₂ <
      ssGs x al u q₁ - 7 / 96 * ssPhi x be al u p 0 q₁ := by
  have hal0 : 0 < al := by linarith
  have hS : 0 < 1 + x := by linarith
  have hsl := lr_slope hx hx2 hal hax hb hp hpr hu huS
  set H := (1 + x) * (m2U (1 / (1 + x)) - u) with hH
  set L := ssLp x be al u p with hL
  have hH0 : 0 ≤ H := mul_nonneg hS.le (by linarith)
  have hL0 : 0 < L := by
    have : 0 ≤ 7 * H * (2 * (1 + x) - 1) := mul_nonneg (by positivity) (by linarith)
    have : 0 < 3 * al ^ 2 * L := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  have hG := env_Gs_inc (by linarith) hal huS hq₁.le hq.le (by linarith : q₂ < 1)
  have hd : (q₂ - q₁) / ((1 - q₁) * (1 - q₂)) ≤ 49 / 36 * (q₂ - q₁) := by
    have h36 : 36 / 49 ≤ (1 - q₁) * (1 - q₂) := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h36 (by linarith : (0 : ℝ) ≤ 49 / 36 * (q₂ - q₁))]
  have hG2 : ssGs x al u q₂ - ssGs x al u q₁ ≤ H * (2 * (1 + x) - 1) / (8 * al ^ 2) *
      (49 / 36 * (q₂ - q₁)) :=
    hG.trans (mul_le_mul_of_nonneg_left hd (div_nonneg (mul_nonneg hH0 (by linarith))
      (by positivity)))
  have hG3 : H * (2 * (1 + x) - 1) / (8 * al ^ 2) * (49 / 36 * (q₂ - q₁)) <
      7 / 96 * L * (q₂ - q₁) := by
    have e : H * (2 * (1 + x) - 1) / (8 * al ^ 2) * (49 / 36 * (q₂ - q₁)) =
        (7 * H * (2 * (1 + x) - 1)) * (7 * (q₂ - q₁) / (288 * al ^ 2)) := by
      field_simp; ring
    have e2 : 7 / 96 * L * (q₂ - q₁) = (3 * al ^ 2 * L) * (7 * (q₂ - q₁) / (288 * al ^ 2)) := by
      field_simp; ring
    rw [e, e2]
    exact mul_lt_mul_of_pos_right hsl (by apply div_pos (by linarith); positivity)
  have hΦ : ssPhi x be al u p 0 q₂ - ssPhi x be al u p 0 q₁ = (q₂ - q₁) * L := by
    rw [hL]; unfold ssPhi; ring
  nlinarith

/-! ### The `τ = 2` slope -/

/-- `F(1/7, 1) > 1/7` in the cleared form `4u/7 < G₁(1/7)`, `G₁ = 4uF(·, 1)`, on
`3/4 ≤ u ≤ u₀` (concave in `u`, two endpoint values). -/
private theorem lr_G1_seventh {S u : ℝ} (hS : 2 < S) (hu : 3 / 4 ≤ u)
    (hu0 : u ≤ 3 / 4 + (S - 2) ^ 2 / (12 * S ^ 2)) :
    4 * u / 7 < 4 * u * (1 - 2 * (1 / 7) + 4 * S ^ 2 * (1 / 7) ^ 2) -
      (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * (1 / 7)) ^ 2 := by
  have hS0 : 0 < S := by linarith
  set u₀ := 3 / 4 + (S - 2) ^ 2 / (12 * S ^ 2) with hu₀
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun v => 4 * v * (1 - 2 * (1 / 7) + 4 * S ^ 2 * (1 / 7) ^ 2) -
      (v - (S * (1 - v) - 1 / S) + 2 * (2 * S - 1) * (1 / 7)) ^ 2 - 4 * v / 7 := ⟨_, rfl⟩
  have hgu : g u = 4 * u * (1 - 2 * (1 / 7) + 4 * S ^ 2 * (1 / 7) ^ 2) -
      (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * (1 / 7)) ^ 2 - 4 * u / 7 := by rw [hg]
  have hconc : (u₀ - 3 / 4) * g u = (u₀ - u) * g (3 / 4) + (u - 3 / 4) * g u₀ +
      (S + 1) ^ 2 * (u - 3 / 4) * (u₀ - u) * (u₀ - 3 / 4) := by
    simp only [hg]; ring
  have hg34 : g (3 / 4) * (784 * S ^ 2) = 111 * (S - 2) ^ 4 + 654 * (S - 2) ^ 3 +
      1931 * (S - 2) ^ 2 + 2700 * (S - 2) + 348 := by
    simp only [hg]; field_simp; ring
  have hgu0 : g u₀ * (1764 * S ^ 4) = 191 * (S - 2) ^ 6 + 1794 * (S - 2) ^ 5 + 8523 * (S - 2) ^ 4 +
      24408 * (S - 2) ^ 3 + 38904 * (S - 2) ^ 2 + 27432 * (S - 2) + 3132 := by
    simp only [hg, hu₀]; field_simp; ring
  have hz : 0 ≤ S - 2 := by linarith
  have h1 : 0 < g (3 / 4) := by
    have : 0 < g (3 / 4) * (784 * S ^ 2) := by rw [hg34]; positivity
    exact pos_of_mul_pos_left this (by positivity)
  have h2 : 0 < g u₀ := by
    have : 0 < g u₀ * (1764 * S ^ 4) := by rw [hgu0]; positivity
    exact pos_of_mul_pos_left this (by positivity)
  have hu₀34 : 0 < u₀ - 3 / 4 := by rw [hu₀]; simp only [add_sub_cancel_left]; positivity
  have : 0 < (u₀ - 3 / 4) * g u := by
    rw [hconc]
    have : 0 ≤ (S + 1) ^ 2 * (u - 3 / 4) * (u₀ - u) * (u₀ - 3 / 4) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
        hu₀34.le
    have hm : 0 < min (g (3 / 4)) (g u₀) := lt_min h1 h2
    have h3 := mul_le_mul_of_nonneg_left (min_le_left (g (3 / 4)) (g u₀))
      (by linarith : (0 : ℝ) ≤ u₀ - u)
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (g (3 / 4)) (g u₀))
      (by linarith : (0 : ℝ) ≤ u - 3 / 4)
    have h5 := mul_pos hu₀34 hm
    linarith
  have := pos_of_mul_pos_right this hu₀34.le
  rw [hgu] at this
  linarith

/-- `F(q, 1) > 1/7` for `0 < q ≤ 1/7` (convex in `q` with negative slope at `1/7`). -/
private theorem lr_G1_pos {S u q : ℝ} (hS : 2 < S) (hS3 : S ≤ 3) (hu : 3 / 4 ≤ u)
    (hu0 : u ≤ 3 / 4 + (S - 2) ^ 2 / (12 * S ^ 2)) (hq7 : q ≤ 1 / 7) :
    4 * u / 7 < 4 * u * (1 - 2 * q + 4 * S ^ 2 * q ^ 2) -
      (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * q) ^ 2 := by
  have hS0 : 0 < S := by linarith
  have h7 := lr_G1_seventh hS hu hu0
  set c₂ := 16 * u * S ^ 2 - 4 * (2 * S - 1) ^ 2 with hc₂
  set c₁ := -8 * u - 4 * (2 * S - 1) * (u - (S * (1 - u) - 1 / S)) with hc₁
  have e : 4 * u * (1 - 2 * q + 4 * S ^ 2 * q ^ 2) -
      (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * q) ^ 2 -
      (4 * u * (1 - 2 * (1 / 7) + 4 * S ^ 2 * (1 / 7) ^ 2) -
        (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * (1 / 7)) ^ 2) =
      (1 / 7 - q) * (-(c₂ * (q + 1 / 7) + c₁)) := by
    rw [hc₂, hc₁]; ring
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; nlinarith
  have hsl : c₂ * (2 / 7) + c₁ < 0 := by
    have e2 : c₂ * (2 / 7) + c₁ = (6 * S ^ 3 - 17 * S ^ 2 - 85 * S + 28) / (7 * S) -
        4 * (6 * S ^ 2 + 7 * S + 7) / 7 * (u - 3 / 4) := by
      rw [hc₂, hc₁]; field_simp; ring
    rw [e2]
    have : (6 * S ^ 3 - 17 * S ^ 2 - 85 * S + 28) / (7 * S) < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity); nlinarith
    have : 0 ≤ 4 * (6 * S ^ 2 + 7 * S + 7) / 7 * (u - 3 / 4) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have : 0 ≤ (1 / 7 - q) * (-(c₂ * (q + 1 / 7) + c₁)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  linarith

/-- `F(q, 0) > 1/7`. -/
private theorem lr_G0_pos {u q h : ℝ} (hu : 3 / 4 ≤ u) (hu41 : u ≤ 41 / 54) (hq : 0 < q)
    (hq7 : q ≤ 1 / 7) (hh0 : 0 ≤ h) (hh : h ≤ 5 / 12) :
    4 * u / 7 < 4 * u * (1 - (2 + (3 - h)) * q + 4 * q ^ 2) - (u - h + 2 * h * q) ^ 2 := by
  have h1 : 18 / 49 ≤ 1 - 5 * q + 4 * q ^ 2 := by nlinarith
  have h2 : (u - h + 2 * h * q) ^ 2 ≤ u ^ 2 := by
    have : 0 ≤ u - h + 2 * h * q := by nlinarith
    have : u - h + 2 * h * q ≤ u := by nlinarith
    nlinarith
  have h3 : 4 * u * (1 - 5 * q + 4 * q ^ 2) ≤ 4 * u * (1 - (2 + (3 - h)) * q + 4 * q ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
  nlinarith

/-- **`q(R*_2)' > q`**: with `a = α⁻²`, `ε = 1 - a`, `h = -E₀`, `X = qΔ`,
`1 - [2 + ε(3 - h)]q + 4Aq² + 4uX² - [2(u - h) + 4K₀q]X > q` (complete the square in `X`; concave in
`a`; the endpoint signs `lr_G0_pos`, `lr_G1_pos`). -/
private theorem lr_phi_gt {S u q a X h : ℝ} (hS : 2 < S) (hS3 : S ≤ 3) (hu : 3 / 4 ≤ u)
    (hu0 : u ≤ 3 / 4 + (S - 2) ^ 2 / (12 * S ^ 2)) (hq : 0 < q) (hq7 : q ≤ 1 / 7) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hh : h = S * (1 - u) - 1 / S) :
    q < 1 - (2 + (1 - a) * (3 - h)) * q + 4 * ((1 - a) ^ 2 + (1 - a) * S * a + S ^ 2 * a ^ 2) * q ^ 2 +
      4 * u * X ^ 2 - (2 * (u - h) + 4 * ((1 - a) * h + (2 * S - 1) * a) * q) * X := by
  have hS0 : 0 < S := by linarith
  have hu41 : u ≤ 41 / 54 := by
    have : (S - 2) ^ 2 / (12 * S ^ 2) ≤ 1 / 108 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hh0 : 0 ≤ h := by
    rw [hh]
    have : S * (1 - u) ≥ S * (1 / 4 - (S - 2) ^ 2 / (12 * S ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hS0.le
    have e : S * (1 / 4 - (S - 2) ^ 2 / (12 * S ^ 2)) - 1 / S = (S + 4) * (S - 2) / (6 * S) := by
      field_simp; ring
    have : 0 ≤ (S + 4) * (S - 2) / (6 * S) := div_nonneg (mul_nonneg (by linarith) (by linarith))
      (by positivity)
    linarith
  have hh5 : h ≤ 5 / 12 := by
    rw [hh]
    have : S * (1 - u) ≤ S * (1 / 4) := mul_le_mul_of_nonneg_left (by linarith) hS0.le
    have : 1 / 3 ≤ 1 / S := by rw [div_le_div_iff₀ (by norm_num) hS0]; linarith
    linarith
  -- complete the square in `X`
  set B := u - h + 2 * ((1 - a) * h + (2 * S - 1) * a) * q with hB
  have hsq : 4 * u * (4 * u * X ^ 2 - (2 * (u - h) + 4 * ((1 - a) * h + (2 * S - 1) * a) * q) * X)
      = (4 * u * X - B) ^ 2 - B ^ 2 := by rw [hB]; ring
  -- concavity in `a`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun a => 4 * u * (1 - (2 + (1 - a) * (3 - h)) * q +
      4 * ((1 - a) ^ 2 + (1 - a) * S * a + S ^ 2 * a ^ 2) * q ^ 2) -
      (u - h + 2 * ((1 - a) * h + (2 * S - 1) * a) * q) ^ 2 := ⟨_, rfl⟩
  have hconc : G a = (1 - a) * G 0 + a * G 1 +
      4 * q ^ 2 * S ^ 2 * (u - (1 - 1 / S + 1 / S ^ 2)) ^ 2 * (a * (1 - a)) := by
    simp only [hG]; rw [hh]; field_simp; ring
  have hG0 : 4 * u / 7 < G 0 := by
    have := lr_G0_pos hu hu41 hq hq7 hh0 hh5
    have e : G 0 = 4 * u * (1 - (2 + (3 - h)) * q + 4 * q ^ 2) - (u - h + 2 * h * q) ^ 2 := by
      simp only [hG]; ring
    rw [e]; exact this
  have hG1 : 4 * u / 7 < G 1 := by
    have := lr_G1_pos hS hS3 hu hu0 hq7
    have e : G 1 = 4 * u * (1 - 2 * q + 4 * S ^ 2 * q ^ 2) -
        (u - (S * (1 - u) - 1 / S) + 2 * (2 * S - 1) * q) ^ 2 := by
      simp only [hG]; rw [hh]; ring
    rw [e]; exact this
  have hGa : 4 * u / 7 < G a := by
    rw [hconc]
    have : 0 ≤ 4 * q ^ 2 * S ^ 2 * (u - (1 - 1 / S + 1 / S ^ 2)) ^ 2 * (a * (1 - a)) :=
      mul_nonneg (by positivity) (mul_nonneg ha (by linarith))
    have hm : 0 < min (G 0 - 4 * u / 7) (G 1 - 4 * u / 7) := lt_min (by linarith) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left (min_le_left (G 0 - 4 * u / 7) (G 1 - 4 * u / 7))
      (by linarith : (0 : ℝ) ≤ 1 - a)
    have h4 := mul_le_mul_of_nonneg_left (min_le_right (G 0 - 4 * u / 7) (G 1 - 4 * u / 7)) ha
    linarith
  have key : 4 * u * q < 4 * u * (1 - (2 + (1 - a) * (3 - h)) * q +
      4 * ((1 - a) ^ 2 + (1 - a) * S * a + S ^ 2 * a ^ 2) * q ^ 2 +
      4 * u * X ^ 2 - (2 * (u - h) + 4 * ((1 - a) * h + (2 * S - 1) * a) * q) * X) := by
    have e : 4 * u * (1 - (2 + (1 - a) * (3 - h)) * q +
        4 * ((1 - a) ^ 2 + (1 - a) * S * a + S ^ 2 * a ^ 2) * q ^ 2 +
        4 * u * X ^ 2 - (2 * (u - h) + 4 * ((1 - a) * h + (2 * S - 1) * a) * q) * X) =
        G a + (4 * u * X - B) ^ 2 := by
      have := hsq; simp only [hG]; rw [hB] at this ⊢; linear_combination this
    rw [e]
    have : 4 * u * q ≤ 4 * u * (1 / 7) := mul_le_mul_of_nonneg_left hq7 (by linarith)
    have := sq_nonneg (4 * u * X - B)
    linarith
  exact lt_of_mul_lt_mul_left key (by linarith)

/-- **The `τ = 2` decrease**: for `1 < x ≤ 2`, `α ≥ 1`, `β ≥ x`, `3/4 ≤ u ≤ u₀(x)`,
`q ↦ Γ_*(q) - (7/96)R*_2(q)` is strictly decreasing on `(0, 1/7]` (`q·R*_2' > 1/7 ≥ q`).
Proof: `lr_phi_gt` (square completion in `X = qΔ`, concavity in `a = α⁻²`, endpoint signs
`lr_G0_pos`, `lr_G1_pos`) and `env_Rs2_inc`; `Γ_*` increment by `env_Gs_inc`. -/
theorem lr_tau2_dec {x be al u q₁ q₂ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hxb : x ≤ be) (hu : 3 / 4 ≤ u) (hu0 : u ≤ ssU0 x) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 7) :
    ssGs x al u q₂ - 7 / 96 * ssRs x be al u q₂ 2 < ssGs x al u q₁ - 7 / 96 * ssRs x be al u q₁ 2 := by
  have hS : 0 < 1 + x := by linarith
  have hal0 : 0 < al := by linarith
  have hu0' : u ≤ 3 / 4 + ((1 + x) - 2) ^ 2 / (12 * (1 + x) ^ 2) := by
    unfold ssU0 at hu0; rw [show (1 + x) - 2 = x - 1 by ring, add_comm 1 x]; exact hu0
  have hU34 : m2U (1 / (1 + x)) - 3 / 4 = (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
    unfold m2U; field_simp; ring
  have huS : u ≤ m2U (1 / (1 + x)) := by
    have : (x - 1) ^ 2 / (12 * (x + 1) ^ 2) ≤ (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
      rw [add_comm x 1]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    unfold ssU0 at hu0; linarith
  -- the increment of `Γ_*`
  have hG := env_Gs_inc (by linarith) hal huS hq₁.le hq.le (by linarith : q₂ < 1)
  have hH0 : 0 ≤ (1 + x) * (m2U (1 / (1 + x)) - u) := mul_nonneg hS.le (by linarith)
  have hH : (1 + x) * (m2U (1 / (1 + x)) - u) ≤ 1 / 12 := by
    have : (1 + x) * (m2U (1 / (1 + x)) - u) ≤ (1 + x) * (m2U (1 / (1 + x)) - 3 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hS.le
    rw [hU34] at this
    have e : (1 + x) * ((x - 1) ^ 2 / (4 * (1 + x) ^ 2)) = (x - 1) ^ 2 / (4 * (1 + x)) := by
      field_simp
    rw [e] at this
    have : (x - 1) ^ 2 / (4 * (1 + x)) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hd : (q₂ - q₁) / ((1 - q₁) * (1 - q₂)) ≤ 49 / 36 * (q₂ - q₁) := by
    have h36 : 36 / 49 ≤ (1 - q₁) * (1 - q₂) := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h36 (by linarith : (0 : ℝ) ≤ 49 / 36 * (q₂ - q₁))]
  have hc : (1 + x) * (m2U (1 / (1 + x)) - u) * (2 * (1 + x) - 1) / (8 * al ^ 2) ≤ 5 / 96 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 + x) * (m2U (1 / (1 + x)) - u) * (2 * (1 + x) - 1) ≤ 1 / 12 * 5 :=
      mul_le_mul hH (by linarith) (by linarith) (by norm_num)
    have h2 : 1 ≤ al ^ 2 := by nlinarith
    nlinarith
  have hG2 : ssGs x al u q₂ - ssGs x al u q₁ ≤ 5 / 96 * (49 / 36 * (q₂ - q₁)) :=
    hG.trans (mul_le_mul hc hd (div_nonneg (by linarith) (by nlinarith)) (by norm_num))
  -- the residual slope `(R*_2)' > 1`
  have hrA : 0 < ssRA al be := by unfold ssRA; apply div_pos <;> linarith
  have hR := env_Rs2_inc hrA hq₁ hq (fun q hq' => by
    have hq0 : 0 < q := hq₁.trans hq'.1
    have hq7 : q ≤ 1 / 7 := hq'.2.le.trans hq₂
    have ha : 0 ≤ 1 / al ^ 2 := by positivity
    have ha1 : 1 / al ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have hphi := lr_phi_gt (X := q * (ssDg x be al / al ^ 2)) (by linarith : 2 < 1 + x)
      (by linarith) hu hu0' hq0 hq7 ha ha1
      (show -ssE0 x u = (1 + x) * (1 - u) - 1 / (1 + x) by unfold ssE0; ring)
    have e : 1 - (2 + (1 - 1 / al ^ 2) * (3 - -ssE0 x u)) * q +
        4 * ((1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * (1 + x) * (1 / al ^ 2) +
          (1 + x) ^ 2 * (1 / al ^ 2) ^ 2) * q ^ 2 +
        4 * u * (q * (ssDg x be al / al ^ 2)) ^ 2 -
        (2 * (u - -ssE0 x u) + 4 * ((1 - 1 / al ^ 2) * -ssE0 x u +
          (2 * (1 + x) - 1) * (1 / al ^ 2)) * q) * (q * (ssDg x be al / al ^ 2)) =
        q * (1 / q - (1 + 2 * ssA1 x be al u + ssA3 x be al u) + 4 * q * ssA2 x be al u) := by
      unfold ssA1 ssA2 ssA3; field_simp; ring
    rw [e] at hphi
    have := lt_of_mul_lt_mul_left (by linarith : q * 1 < q * (1 / q - (1 + 2 * ssA1 x be al u +
      ssA3 x be al u) + 4 * q * ssA2 x be al u)) hq0.le
    exact this)
  nlinarith

/-- **The β-dependent ceiling**: for `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`,
`x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`: `ū(x, β) ≤ u_ℓ(x, β)`. -/
theorem lr_u_ell {x al be : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hal' : al ≤ 6 / 5)
    (hxb : x ≤ be) (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssUbar x be ≤ ssUl x be := by
  have hS : 0 < 1 + x := by linarith
  have hZ : 0 < 35 * x + 13 := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hb1 : 0 < be - 1 := by linarith
  have hbx : 0 ≤ be - x := by linarith
  -- `(β - x)²SZ ≤ 6x²(x - 1)²` from the upper strip
  have hbx2 : (be - x) * (4 * x ^ 2 + 11 * x + 1) ≤ x * (7 * x + 1) / 5 := by
    have h1 : be - x ≤ x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by linarith
    rw [le_div_iff₀ hR] at h1
    have : x * (7 * x + 1) * (al - 1) ≤ x * (7 * x + 1) * (1 / 5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hpoly : (7 * x + 1) ^ 2 * ((1 + x) * (35 * x + 13)) ≤
      150 * (4 * x ^ 2 + 11 * x + 1) ^ 2 * (x - 1) ^ 2 := by
    have e : 150 * (4 * x ^ 2 + 11 * x + 1) ^ 2 * (x - 1) ^ 2 -
        (7 * x + 1) ^ 2 * ((1 + x) * (35 * x + 13)) =
        2400 * (x - 3 / 2) ^ 6 + 30000 * (x - 3 / 2) ^ 5 + 137635 * (x - 3 / 2) ^ 4 +
        287768 * (x - 3 / 2) ^ 3 + 557379 / 2 * (x - 3 / 2) ^ 2 + 104452 * (x - 3 / 2) +
        74855 / 16 := by ring
    have hv : 0 ≤ x - 3 / 2 := by linarith
    have : 0 ≤ 2400 * (x - 3 / 2) ^ 6 + 30000 * (x - 3 / 2) ^ 5 + 137635 * (x - 3 / 2) ^ 4 +
        287768 * (x - 3 / 2) ^ 3 + 557379 / 2 * (x - 3 / 2) ^ 2 + 104452 * (x - 3 / 2) +
        74855 / 16 := by positivity
    linarith
  have hkey : (be - x) ^ 2 * ((1 + x) * (35 * x + 13)) ≤ 6 * x ^ 2 * (x - 1) ^ 2 := by
    have h1 : ((be - x) * (4 * x ^ 2 + 11 * x + 1)) ^ 2 ≤ (x * (7 * x + 1) / 5) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hbx hR.le) hbx2 2
    have h2 : (be - x) ^ 2 * ((1 + x) * (35 * x + 13)) * (4 * x ^ 2 + 11 * x + 1) ^ 2 ≤
        6 * x ^ 2 * (x - 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (1 + x) * (35 * x + 13))
      have h3 := mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ x ^ 2 / 25)
      nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  unfold ssUbar ssUl
  have e : (x - 1) ^ 2 * (be + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (be - 1)) -
      (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (be - x) ^ 3 / (48 * x ^ 2)) / (be - 1) =
      (be - x) * (6 * x ^ 2 * (x - 1) ^ 2 - (be - x) ^ 2 * ((1 + x) * (35 * x + 13))) /
        (48 * x ^ 2 * ((1 + x) * (35 * x + 13)) * (be - 1)) := by
    have : x ≠ 0 := by linarith
    field_simp; ring
  have : 0 ≤ (be - x) * (6 * x ^ 2 * (x - 1) ^ 2 - (be - x) ^ 2 * ((1 + x) * (35 * x + 13))) /
      (48 * x ^ 2 * ((1 + x) * (35 * x + 13)) * (be - 1)) :=
    div_nonneg (mul_nonneg hbx (by linarith)) (by positivity)
  linarith

/-! ### Terminal face signs -/

/-- **The central low-ratio face**: for `1 < x ≤ 2`, `1 ≤ α`, `6α² ≤ x(x + 2)` (`q_c ≤ 1/7`), the
strip `x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `3/4 ≤ u ≤ u_ℓ(x, β)` and
every `τ ∈ [2, T]`, `T = r_A/q_c`: `Γ_*(q_c) - (7/96)R*_τ(q_c) > 9193/50000`. Proved in
`SmallerShort/LowerRatio/CentralFace`. -/
theorem lr_central_face {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : 3 / 4 ≤ u)
    (hul : u ≤ ssUl x be) (hτ : 2 ≤ τ) (hτT : τ * ssQc x al ≤ ssRA al be) :
    9193 / 50000 < ssGs x al u (ssQc x al) - 7 / 96 * ssRs x be al u (ssQc x al) τ := by
  apply lr_central_face_proof <;> assumption

/-- **The outer low-ratio face**: for `1 < x ≤ 2`, `1 ≤ α ≤ x`, `x ≤ β ≤ αx`, `x(x + 2) ≤ 6α²`
(`q_c ≥ 1/7`), the strip of `lr_central_face`, `u_f(x) ≤ u ≤ V̄(x)` with `u ≤ u_ℓ(x, β)` when
`x ≥ 3/2` and `α ≤ 6/5`, and every `τ ∈ [2, 7r_A]`: `Γ_*(1/7) - (7/96)R*_τ(1/7) > 9193/50000`.
Proved in `SmallerShort/LowerRatio/OuterFace`. -/
theorem lr_outer_face {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hbx : be ≤ al * x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : ssUf x ≤ u)
    (huv : u ≤ ssVbar x) (hul : 3 / 2 ≤ x → al ≤ 6 / 5 → u ≤ ssUl x be) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * ssRA al be) :
    9193 / 50000 < ssGs x al u (1 / 7) - 7 / 96 * ssRs x be al u (1 / 7) τ := by
  apply lr_outer_face_proof <;> assumption

/-- **`D > 0` on the lower-ratio range** (from `β ≤ αx` and the quadratic `(1 + 2x)α² - 2x²α + (1 + 2x)`,
which has negative discriminant for `x < 1 + √2`). -/
private theorem lr_D_pos {x be al : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hax : al ≤ x)
    (hbx : be ≤ al * x) : 0 < ssDg x be al := by
  unfold ssDg
  have h1 : 2 * (al * x) * (x - al) ≥ 2 * be * (x - al) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : 0 < (1 + 2 * x) * al ^ 2 - 2 * x ^ 2 * al + (1 + 2 * x) := by
    have e : (1 + 2 * x) * ((1 + 2 * x) * al ^ 2 - 2 * x ^ 2 * al + (1 + 2 * x)) =
        ((1 + 2 * x) * al - x ^ 2) ^ 2 + ((1 + 2 * x) ^ 2 - x ^ 4) := by ring
    have h3 : 0 < (1 + 2 * x) ^ 2 - x ^ 4 := by
      have : x ^ 2 < 1 + 2 * x := by nlinarith
      have : (x ^ 2) ^ 2 < (1 + 2 * x) ^ 2 := pow_lt_pow_left₀ this (by positivity) (by norm_num)
      nlinarith
    have : 0 < (1 + 2 * x) * ((1 + 2 * x) * al ^ 2 - 2 * x ^ 2 * al + (1 + 2 * x)) := by
      rw [e]; positivity
    exact pos_of_mul_pos_right this (by linarith)
  nlinarith

/-- **The order strip**: the strong lower order and the upper order `9/8` give
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`. -/
private theorem lr_strip {x be al : ℝ} (hx : 1 < x)
    (hso : be / x + ssKs x * (be - x) ≤ al) (huo : al ≤ be / x + 9 / 8 * (be - x)) :
    x + 8 * x * (al - 1) / (9 * x + 8) ≤ be ∧
      be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by
  have hx0 : 0 < x := by linarith
  have e1 : be / x * x = be := div_mul_cancel₀ _ hx0.ne'
  constructor
  · have : al * x ≤ be + 9 / 8 * (be - x) * x := by
      have := mul_le_mul_of_nonneg_right huo hx0.le
      rw [add_mul, e1] at this; linarith
    have : 8 * x * (al - 1) / (9 * x + 8) ≤ be - x := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · have : be * (7 * x + 1) + 4 * x * (x + 1) * (be - x) ≤ al * x * (7 * x + 1) := by
      unfold ssKs at hso
      have := mul_le_mul_of_nonneg_right hso (by positivity : (0 : ℝ) ≤ x * (7 * x + 1))
      have e2 : (be / x + 4 * (x + 1) / (7 * x + 1) * (be - x)) * (x * (7 * x + 1)) =
          be * (7 * x + 1) + 4 * x * (x + 1) * (be - x) := by
        field_simp
      linarith
    have : be - x ≤ x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith

/-! ### The lower-ratio bound -/

namespace SmallerShortData

variable (H : SmallerShortData)

/-- **The corrected envelope cap**: for actual data with `x ≤ 2`,
`Γ_actual ≥ Γ_*(q) - (7/96)R*_τ(q)` at the actual `q`, `τ`, shape and `u` (two-segment monotonicity
of `Γ - (7/96)R_τ`: the `v`-segment by concavity, the `t`-segment along `v = U(t)`, both from
`lr_ratio` with `lr_root_cap`, `ss_B_factor_pos`; endpoint values `root_zero`, `ss_env_scale`).
Proof: the generic two-segment lemma `SmallerShortData.env_cap_data`, with the ratio bound
`lr_ratio_strip` (`lr_ratio` plus the order strip, obtained from `strong_order`,
`upper_order_98`). -/
theorem lr_cap_env (hx2 : H.x ≤ 2) :
    ssGs H.x H.al H.u H.q - 7 / 96 * ssRs H.x H.be H.al H.u H.q H.τ ≤ H.Γ := by
  have hx := H.one_lt_x
  have hu0 : H.u ≤ ssU0 H.x := H.u_le_V.trans (ss_V_le_U0 hx)
  have hD : 0 < ssDg H.x H.be H.al := lr_D_pos hx hx2 H.al_lt_x.le H.be_le_al_x
  have hq7 : ssQ H.al H.rho ≤ 1 / 7 := H.q_lt_seventh.le
  obtain ⟨hlo, hhi⟩ := lr_strip hx H.strong_order (H.upper_order_98 (by linarith))
  have hlo' : H.x + 8 / 17 * (H.al - 1) ≤ H.be := by
    have : 8 / 17 * (H.al - 1) ≤ 8 * H.x * (H.al - 1) / (9 * H.x + 8) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [H.one_le_al]
    linarith
  have hhi' : H.be ≤ H.x + 4 / 5 * (H.al - 1) := by
    have : H.x * (7 * H.x + 1) * (H.al - 1) / (4 * H.x ^ 2 + 11 * H.x + 1) ≤ 4 / 5 * (H.al - 1) := by
      rw [div_le_iff₀ (by nlinarith)]
      have : 0 ≤ (H.al - 1) * (4 + 39 * H.x - 19 * H.x ^ 2) :=
        mul_nonneg (by linarith [H.one_le_al]) (by nlinarith)
      nlinarith
    linarith
  have h := H.env_cap_data (c := 7 / 96) (fun s hs e he hB => by
    have hs0 : 0 < s := lt_of_lt_of_le (by have := H.rho_pos; positivity) hs.1
    have := lr_ratio_strip hx hx2 H.one_le_al H.al_lt_x H.x_le_be hD H.u_ge_34 hu0 H.u_le_rA
      H.rho_pos hq7 H.two_lt_τ.le H.τ_lt hs0 (hs.2.trans H.t_le_r) hB (he.trans H.env_EL_cap)
      hlo' hhi'
    unfold SmallerShortData.q
    linarith)
  exact h

/-- **The lower-ratio bound**: `x > 2`.
Proof: if `x ≤ 2`: `lr_cap_env`; with `p = τq` (`q ≤ p/2`, `p < r_A`), raise `q` at fixed `p`
to `min{q_c, 1/7, p/2}` (`lr_scale_dec`, `ss_phi_eq`; strip from `strong_order`,
`upper_order_98`), then at `τ = 2` to `min{q_c, 1/7}` (`lr_tau2_dec`; `ss_V_le_U0`, `u_le_V`); on
the central face (`ss_qc_le_iff`) `lr_central_face` with `u ≤ ū ≤ u_ℓ` (`ss_sec_le_ubar`,
`lr_u_ell`; `x ≥ 23/14`, `α ≤ 1351/1170`), on the outer face `lr_outer_face` with
`ss_sec_gt_floor`, `ss_V_le_Vbar`, `lr_u_ell`; this gives `Γ > 9193/50000`, contradicting
`cas_lt`. The terminal faces cover the full duration range, so no duration maximum is needed. -/
theorem two_lt_ratio : 2 < H.x := by

  by_contra hcon
  push Not at hcon
  have hx := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hal := H.one_le_al
  have hax := H.al_lt_x
  have hxb := H.x_le_be
  have hbx := H.be_le_al_x
  obtain ⟨hlo, hhi⟩ := lr_strip hx H.strong_order (H.upper_order_98 (by linarith))
  have hu34 := H.u_ge_34
  have hu0 : H.u ≤ ssU0 H.x := H.u_le_V.trans (ss_V_le_U0 hx)
  have hubar : H.u ≤ ssUbar H.x H.be := H.u_eq ▸ ss_sec_le_ubar hx hxb
  have hrA3 : 1 / 3 ≤ ssRA H.al H.be := by
    unfold ssRA; rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  -- the two terminal faces
  have hcen : 6 * H.al ^ 2 ≤ H.x * (H.x + 2) → ∀ τ', 2 ≤ τ' → τ' * ssQc H.x H.al ≤ ssRA H.al H.be →
      9193 / 50000 < ssGs H.x H.al H.u (ssQc H.x H.al) -
        7 / 96 * ssRs H.x H.be H.al H.u (ssQc H.x H.al) τ' := by
    intro hqc τ' hτ' hτT
    have hx32 : 3 / 2 ≤ H.x := by nlinarith
    have hal65 : H.al ≤ 6 / 5 := by nlinarith
    exact lr_central_face hx hcon hal hqc hlo hhi hu34
      (hubar.trans (lr_u_ell hx32 hcon hal hal65 hxb hhi)) hτ' hτT
  have hout : H.x * (H.x + 2) ≤ 6 * H.al ^ 2 → ∀ τ', 2 ≤ τ' → τ' ≤ 7 * ssRA H.al H.be →
      9193 / 50000 < ssGs H.x H.al H.u (1 / 7) - 7 / 96 * ssRs H.x H.be H.al H.u (1 / 7) τ' := by
    intro hqc τ' hτ' hτT
    have huf : ssUf H.x ≤ H.u := H.u_eq ▸ (ss_sec_gt_floor hx H.x_le_nine hxb).le
    have huv : H.u ≤ ssVbar H.x := H.u_le_V.trans (ss_V_le_Vbar hx)
    exact lr_outer_face hx hcon hal hax.le hxb hbx hqc hlo hhi huf huv
      (fun h1 h2 => hubar.trans (lr_u_ell h1 hcon hal h2 hxb hhi)) hτ' hτT
  -- the corrected envelope cap at the actual scale, in the fixed-`p` form
  have hcap := H.lr_cap_env hcon
  have hq0 := H.env_q_pos
  have hτ0 : 0 < H.τ := by linarith [H.two_lt_τ]
  rw [env_Rs_phi hq0 hτ0] at hcap
  have hp0 : 0 < H.τ * H.q := by positivity
  have hpr : H.τ * H.q ≤ ssRA H.al H.be := H.τ_lt.le
  have hqp : H.q < H.τ * H.q / 2 := by nlinarith [H.two_lt_τ]
  have hqqc : H.q ≤ ssQc H.x H.al := H.q_le_qc
  have hq7 : H.q < 1 / 7 := H.q_lt_seventh
  have hdec := fun {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h : q₁ < q₂) (h₂ : q₂ ≤ 1 / 7) =>
    lr_scale_dec (be := H.be) (p := H.τ * H.q) hx hcon hal hax.le hlo hp0 hpr hu34 H.u_le_r h₁ h h₂
  have hmove : ∀ q', H.q ≤ q' → q' ≤ 1 / 7 → ssGs H.x H.al H.u q' -
      7 / 96 * ssPhi H.x H.be H.al H.u (H.τ * H.q) 0 q' ≤ H.Γ := by
    intro q' h1 h2
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hcap
    · have := hdec hq0 h h2; linarith
  -- at `τ = 2`, from `p/2` to the face
  have htau : ∀ qf, H.τ * H.q / 2 ≤ qf → qf ≤ 1 / 7 →
      ssGs H.x H.al H.u qf - 7 / 96 * ssRs H.x H.be H.al H.u qf 2 ≤ H.Γ := by
    intro qf h1 h2
    have hm := hmove (H.τ * H.q / 2) hqp.le (h1.trans h2)
    have e : ssRs H.x H.be H.al H.u (H.τ * H.q / 2) 2 =
        ssPhi H.x H.be H.al H.u (H.τ * H.q) 0 (H.τ * H.q / 2) := by
      rw [env_Rs_phi (by linarith) (by norm_num), show 2 * (H.τ * H.q / 2) = H.τ * H.q by ring]
    rw [← e] at hm
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hm
    · have := lr_tau2_dec (be := H.be) hx hcon hal hxb hu34 hu0 (by linarith) h h2
      linarith
  have hlt : ¬ (9193 / 50000 < H.Γ) := not_lt.mpr H.cas_lt.le
  apply hlt
  by_cases hc7 : ssQc H.x H.al ≤ 1 / 7
  · have hqc := (ss_qc_le_iff hx0).mp hc7
    have hqc0 : 0 < ssQc H.x H.al := by unfold ssQc; positivity
    by_cases hc : ssQc H.x H.al ≤ H.τ * H.q / 2
    · have hm := hmove _ hqqc hc7
      have e : ssRs H.x H.be H.al H.u (ssQc H.x H.al) (H.τ * H.q / ssQc H.x H.al) =
          ssPhi H.x H.be H.al H.u (H.τ * H.q) 0 (ssQc H.x H.al) := by
        rw [env_Rs_phi hqc0 (by positivity), div_mul_cancel₀ _ hqc0.ne']
      rw [← e] at hm
      have := hcen hqc (H.τ * H.q / ssQc H.x H.al) (by rw [le_div_iff₀ hqc0]; linarith)
        (by rw [div_mul_cancel₀ _ hqc0.ne']; exact hpr)
      linarith
    · push Not at hc
      have hm := htau _ hc.le hc7
      have := hcen hqc 2 le_rfl (by linarith)
      linarith
  · push Not at hc7
    have hqc : H.x * (H.x + 2) ≤ 6 * H.al ^ 2 := by
      by_contra h; push Not at h
      exact absurd ((ss_qc_le_iff hx0).mpr h.le) (not_le.mpr hc7)
    by_cases hc : 1 / 7 ≤ H.τ * H.q / 2
    · have hm := hmove (1 / 7) hq7.le le_rfl
      have e : ssRs H.x H.be H.al H.u (1 / 7) (7 * (H.τ * H.q)) =
          ssPhi H.x H.be H.al H.u (H.τ * H.q) 0 (1 / 7) := by
        rw [env_Rs_phi (by norm_num) (by positivity)]; ring_nf
      rw [← e] at hm
      have := hout hqc (7 * (H.τ * H.q)) (by linarith) (by linarith)
      linarith
    · push Not at hc
      have hm := htau (1 / 7) hc.le le_rfl
      have := hout hqc 2 le_rfl (by linarith)
      linarith

end SmallerShortData

/-- **The lower-ratio bound for the actual window**: `C/a > 2`. -/
theorem M2Short.two_lt_ratio (D : M2Short) : 2 < D.C / D.a := by
  have h := D.toData.two_lt_ratio
  rwa [D.toData_x] at h

end SmoothedOctagon
