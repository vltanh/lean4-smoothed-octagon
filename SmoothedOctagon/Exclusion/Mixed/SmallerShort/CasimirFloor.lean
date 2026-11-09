module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CasimirScale
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.NormEndpoint
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CapData
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.FloorBox

/-!
# Smaller-short window, Casimir floor: `α ≤ 1 + 3δ` and `Γ > 1829/10000`

This module proves the small-shape upper order (U) `α ≤ 1 + 3δ` and the extended Casimir floor (F)
`Γ > 1829/10000`. On `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`: (U) is `ss_small_upper_order`; for (F), the
corrected envelope cap with constant `1/7` (`SmallerShortData.cas_cap_env`), the scale moves
(`cas_scale_dec_p`, `cas_tau2_dec`) to the central scale `q_c`, the duration maximum (`ss_dur_max`),
the norm substitution `u ↦ ū` (`cas_u_dec`) and the central-scale floor `min{Φ, Ψ}(ū) > 1829/10000`
(`cas_floor_box`).

## Main API

* Supporting modules: `SmallerShort/Envelope/CasimirScale` (the scale form of `Γ_*`, the slope
  `L(p)`, the `τ = 2` residual), `SmallerShort/Envelope/NormEndpoint` (the lower norm endpoints of
  the slope inequalities), `SmallerShort/Envelope/Cap` and `SmallerShort/Envelope/CapData` (the
  corrected envelope cap).

* `casPhi`, `casPsi`: `Φ = Γ_*(q_c) - R*_2(q_c)/7`, `Ψ = Φ - (T - 2)(w_*(q_c) - 3/4)/7`.
* `SmallerShortData.cas_cap_env`, `cas_scale_dec_p`, `cas_tau2_dec`, `cas_u_dec`, `cas_ubar_box`.
* `cas_floor_box`, proved in `CasimirFloor/FloorBox` from six monotonicity steps and three scalar
  endpoints: W1 (`Φ` decreases in the displacement, `CasimirFloor/PhiDisplacement`), W2 (`Ψ`
  increases in the shape, `CasimirFloor/PsiShape`), W3 (`Ψ` decreases in the ratio,
  `CasimirFloor/PsiRatio`), W4 (`Φ` decreases in the ratio, `CasimirFloor/PhiRatio`), W5 (`Φ`
  decreases in the shape, `CasimirFloor/PhiShape`), W6 (the terminal concavity,
  `CasimirFloor/TerminalConcavity`); the names `cas_w1_*`, …, `cas_w6_*` follow these steps.
* The bound: `SmallerShortData.upper_order_casimir_floor`, `M2Short.upper_order_casimir_floor`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The fixed-`p` scale move**: for `x > 1`, `1 ≤ α < x ≤ β`, `0 < p ≤ r_A`,
`3/4 ≤ u ≤ min{U(1/(1 + x)), U(r_A)}`, `q ↦ Γ_*(q) - (C(p) + qL(p))/7` is strictly decreasing on
`(0, 1/6]` (`L > 0`, `∂_q Γ_* < (27/200)L`).
Proof: the monotonicity in `q` by increments (`env_Gs_inc`); the slope inequality
`4H(2S - 1) < 3α²L` by `env_slope_gen` with its lower norm endpoint at `β = x` (`env_bot_ccs`)
and `env_Lp_top_pos` (monotone in `A₃`). -/
theorem cas_scale_dec_p {x be al u p q₁ q₂ : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (hp : 0 < p) (hpr : p ≤ ssRA al be) (hu : 3 / 4 ≤ u)
    (hur : u ≤ m2U (1 / (1 + x))) (_hurA : u ≤ m2U (ssRA al be)) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 6) :
    ssGs x al u q₂ - ssPhi x be al u p 0 q₂ / 7 < ssGs x al u q₁ - ssPhi x be al u p 0 q₁ / 7 := by
  have hal0 : 0 < al := by linarith
  have hS : 0 < 1 + x := by linarith
  -- the slope inequality `4H(2S - 1) < 3α²L`
  have hpx : p ≤ al / (al + x) := by
    refine hpr.trans ?_
    unfold ssRA; exact div_le_div_of_nonneg_left hal0.le (by linarith) (by linarith)
  have hsl := env_slope_gen (be₀ := x) hx hal hax.le le_rfl hxb hp hpr hu hur
    (env_bot_ccs hx hal hax.le hp hpx)
  set H := (1 + x) * (m2U (1 / (1 + x)) - u) with hH
  set L := ssLp x be al u p with hL
  have hH0 : 0 ≤ H := mul_nonneg hS.le (by linarith)
  have hS1 : 0 ≤ 2 * (1 + x) - 1 := by linarith
  have hL0 : 0 < L := by
    have : 0 ≤ 4 * H * (2 * (1 + x) - 1) := by positivity
    have : 0 < 3 * al ^ 2 * L := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  -- the increment of `Γ_*`
  have hG := env_Gs_inc (by linarith) hal hur hq₁.le hq.le (by linarith : q₂ < 1)
  have hd : (q₂ - q₁) / ((1 - q₁) * (1 - q₂)) ≤ 36 / 25 * (q₂ - q₁) := by
    have h25 : 25 / 36 ≤ (1 - q₁) * (1 - q₂) := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h25 (by linarith : (0 : ℝ) ≤ 36 / 25 * (q₂ - q₁))]
  have hG2 : ssGs x al u q₂ - ssGs x al u q₁ ≤ H * (2 * (1 + x) - 1) / (8 * al ^ 2) *
      (36 / 25 * (q₂ - q₁)) :=
    hG.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have hG3 : H * (2 * (1 + x) - 1) / (8 * al ^ 2) * (36 / 25 * (q₂ - q₁)) <
      27 / 200 * L * (q₂ - q₁) := by
    have e : H * (2 * (1 + x) - 1) / (8 * al ^ 2) * (36 / 25 * (q₂ - q₁)) =
        (4 * H * (2 * (1 + x) - 1)) * (9 * (q₂ - q₁) / (200 * al ^ 2)) := by
      field_simp; ring
    have e2 : 27 / 200 * L * (q₂ - q₁) = (3 * al ^ 2 * L) * (9 * (q₂ - q₁) / (200 * al ^ 2)) := by
      field_simp; ring
    rw [e, e2]
    exact mul_lt_mul_of_pos_right hsl (by apply div_pos (by linarith); positivity)
  have hΦ : ssPhi x be al u p 0 q₂ - ssPhi x be al u p 0 q₁ = (q₂ - q₁) * L := by
    rw [hL]; unfold ssPhi; ring
  have : 27 / 200 * L * (q₂ - q₁) ≤ (q₂ - q₁) * L / 7 := by nlinarith
  linarith

/-- `C₀ = 1 + 2A₁ + A₃ ≤ 5` on the small box:
`C₀ = 2 + 3ε + εE₀ + 2Δ(E₀ + u)`, `E₀ < 0 < E₀ + u`, `D ≤ S`, `2S(E₀ + u) ≤ 13/5`. -/
private theorem cas_C0_le {x be al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal1 : 1 ≤ al) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 31 / 40) (hDS : ssDg x be al ≤ 1 + x) :
    1 + 2 * ssA1 x be al u + ssA3 x be al u ≤ 5 := by
  have hS : 0 < 1 + x := by linarith
  have e : 1 + 2 * ssA1 x be al u + ssA3 x be al u = 2 + 3 * (1 - 1 / al ^ 2) +
      (1 - 1 / al ^ 2) * ssE0 x u + 2 * (ssDg x be al * (1 / al ^ 2)) * (ssE0 x u + u) := by
    unfold ssA1 ssA3; ring
  rw [e]
  have ha : 0 < 1 / al ^ 2 := by positivity
  have ha1 : 1 / al ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hSE' : (1 + x) * (ssE0 x u + u) = (1 + x) * (2 + x) * u - (1 + x) ^ 2 + 1 := by
    unfold ssE0; field_simp; ring
  have hE0 : ssE0 x u ≤ 0 := by
    unfold ssE0
    have h1 : 1 / (1 + x) ≤ 1 / 3 := by rw [div_le_div_iff₀ hS (by norm_num)]; linarith
    have h2 : (1 + x) * (u - 1) ≤ 3 * (u - 1) :=
      mul_le_mul_of_nonpos_right (by linarith) (by linarith)
    linarith
  have hE0u : 0 ≤ ssE0 x u + u := by
    have h2 : 0 ≤ (1 + x) * (2 + x) * u - (1 + x) ^ 2 + 1 := by
      have : (1 + x) * (2 + x) * (3 / 4) ≤ (1 + x) * (2 + x) * u :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      have : 0 ≤ (3 - x) * (x + 2) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    rw [← hSE'] at h2
    exact nonneg_of_mul_nonneg_right (by linarith) hS
  have hSE : (1 + x) * (ssE0 x u + u) ≤ 13 / 10 := by
    rw [hSE']
    have h1 : (1 + x) * (2 + x) * u ≤ (1 + x) * (2 + x) * (31 / 40) :=
      mul_le_mul_of_nonneg_left hu' (by positivity)
    have h2 : 0 ≤ (x - 2) * (9 * x + 5) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h1 : 2 * (ssDg x be al * (1 / al ^ 2)) * (ssE0 x u + u) ≤
      2 * ((1 + x) * (1 / al ^ 2)) * (ssE0 x u + u) := by
    apply mul_le_mul_of_nonneg_right _ hE0u
    have := mul_le_mul_of_nonneg_right hDS ha.le
    linarith
  have h2 : (1 - 1 / al ^ 2) * ssE0 x u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hE0
  have h3 : 2 * ((1 + x) * (1 / al ^ 2)) * (ssE0 x u + u) ≤ 13 / 5 * (1 / al ^ 2) := by
    have e : 2 * ((1 + x) * (1 / al ^ 2)) * (ssE0 x u + u) =
        2 * ((1 + x) * (ssE0 x u + u)) * (1 / al ^ 2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hSE ha.le
    linarith
  linarith

/-- **The `τ = 2` scale move**: on `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`,
`β = x(1 + δ)`, `3/4 ≤ u ≤ 31/40`, `u ≤ U(1/(1 + x))`: `q ↦ Γ_*(q) - R*_2(q)/7` is strictly
decreasing on `(0, 1/6]` (`(R*_2)' > 1`, `(Γ_*)_q < 11/100`).
Proof: `C₀ ≤ 5` (`cas_C0_le`), `A₂ > 0` (`ss_A2_pos`), `env_Rs2_inc`; `env_Gs_inc`. -/
theorem cas_tau2_dec {x δ al u q₁ q₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 31 / 40) (hur : u ≤ m2U (1 / (1 + x))) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 6) :
    ssGs x al u q₂ - ssRs x (x * (1 + δ)) al u q₂ 2 / 7 <
      ssGs x al u q₁ - ssRs x (x * (1 + δ)) al u q₁ 2 / 7 := by
  have hal1 : 1 ≤ al := by linarith
  have hal22 : al ≤ 22 / 19 := by linarith
  have hS : 0 < 1 + x := by linarith
  have hx0 : 0 < x := by linarith
  set be := x * (1 + δ) with hbe
  have hxb : x ≤ be := by rw [hbe]; nlinarith
  -- `D ≤ S` on the box
  have hDS : ssDg x be al ≤ 1 + x := by
    unfold ssDg
    have h1 : 2 * be * (x - al) ≥ 2 * x * (x - al) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  -- the increment of `Γ_*`
  have hG := env_Gs_inc hx0 hal1 hur hq₁.le hq.le (by linarith : q₂ < 1)
  have hH0 : 0 ≤ (1 + x) * (m2U (1 / (1 + x)) - u) := mul_nonneg hS.le (by linarith)
  have hH : (1 + x) * (m2U (1 / (1 + x)) - u) ≤ 49 / 456 := by
    have e : (1 + x) * (m2U (1 / (1 + x)) - 3 / 4) = (x - 1) ^ 2 / (4 * (1 + x)) := by
      unfold m2U; field_simp; ring
    have : (1 + x) * (m2U (1 / (1 + x)) - u) ≤ (1 + x) * (m2U (1 / (1 + x)) - 3 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hS.le
    rw [e] at this
    have : (x - 1) ^ 2 / (4 * (1 + x)) ≤ 49 / 456 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hd : (q₂ - q₁) / ((1 - q₁) * (1 - q₂)) ≤ 36 / 25 * (q₂ - q₁) := by
    have h25 : 25 / 36 ≤ (1 - q₁) * (1 - q₂) := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h25 (by linarith : (0 : ℝ) ≤ 36 / 25 * (q₂ - q₁))]
  have hG2 : ssGs x al u q₂ - ssGs x al u q₁ ≤ 11 / 100 * (q₂ - q₁) := by
    refine hG.trans ?_
    have hc : (1 + x) * (m2U (1 / (1 + x)) - u) * (2 * (1 + x) - 1) / (8 * al ^ 2) ≤
        49 / 456 * (16 / 3) / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have : 49 / 456 * (16 / 3) / 8 ≤ 49 / 456 * (16 / 3) / 8 * al ^ 2 := by
        have : 1 ≤ al ^ 2 := by nlinarith
        nlinarith
      nlinarith [mul_le_mul hH (by linarith : 2 * (1 + x) - 1 ≤ 16 / 3) (by linarith) (by norm_num)]
    calc _ ≤ 49 / 456 * (16 / 3) / 8 * (36 / 25 * (q₂ - q₁)) :=
          mul_le_mul hc hd (div_nonneg (by linarith) (by nlinarith)) (by norm_num)
      _ ≤ 11 / 100 * (q₂ - q₁) := by nlinarith
  -- the residual increment: `(R*_2)' = 1/q - C₀ + 4qA₂ > 1` (`C₀ ≤ 5`, `A₂ > 0`)
  have hrA : 0 < ssRA al be := by unfold ssRA; apply div_pos (by linarith) (by linarith)
  have hC0 : 1 + 2 * ssA1 x be al u + ssA3 x be al u ≤ 5 :=
    cas_C0_le hx hx2 hal1 hu hu' hDS
  have hA2 : 0 < ssA2 x be al u := ss_A2_pos hx (by linarith) hal1 hu (by linarith)
  have hR := env_Rs2_inc (x := x) (u := u) hrA hq₁ hq (fun q hq' => by
    have hq0 : 0 < q := hq₁.trans hq'.1
    have hq6 : q ≤ 1 / 6 := hq'.2.le.trans hq₂
    have : 6 ≤ 1 / q := by rw [le_div_iff₀ hq0]; linarith
    nlinarith [mul_pos hq0 hA2])
  linarith

/-- `D ≤ S` on the small box. -/
private theorem cas_D_le_S {x be al : ℝ} (hx : 2 ≤ x) (hal1 : 1 ≤ al) (hal22 : al ≤ 22 / 19)
    (hxb : x ≤ be) : ssDg x be al ≤ 1 + x := by
  unfold ssDg
  have h1 : 2 * x * (x - al) ≤ 2 * be * (x - al) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : al ^ 2 + x - 2 * x ^ 2 + 2 * x * al ≤ 0 := by nlinarith
  nlinarith

/-- The shape bounds of the small box used by `cas_u_dec`: `3D ≤ Σ ≤ S³ ≤ (19/6)Σ`,
`19α ≤ 11(α + β)`, `2α(α + β) ≤ Σ ≤ (19/6)α(α + β)`, `Σ = x(x + 2) + α²`. -/
private theorem cas_shape {x be al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hal22 : al ≤ 22 / 19) (hxb : x ≤ be) (hb130 : be ≤ 130 / 57) (hDS : ssDg x be al ≤ 1 + x) :
    3 * ssDg x be al ≤ x * (x + 2) + al ^ 2 ∧ x * (x + 2) + al ^ 2 ≤ (1 + x) ^ 3 ∧
      (1 + x) ^ 3 ≤ 19 / 6 * (x * (x + 2) + al ^ 2) ∧ 19 * al ≤ 11 * (al + be) ∧
      2 * (al * (al + be)) ≤ x * (x + 2) + al ^ 2 ∧
      x * (x + 2) + al ^ 2 ≤ (7 / 6 + 2) * (al * (al + be)) := by
  have hal2 : al ^ 2 ≤ 2 := by nlinarith
  have hx3 : 8 ≤ x ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
    linarith
  refine ⟨by nlinarith, by nlinarith, ?_, by linarith, ?_, ?_⟩
  · have h1 : (1 + x) ^ 3 ≤ 19 / 6 * (1 + x) ^ 2 := by nlinarith
    nlinarith
  · have : al * be ≤ 22 / 19 * (130 / 57) := mul_le_mul hal22 hb130 (by linarith) (by norm_num)
    nlinarith
  · have h1 : x * (x + 2) + al ^ 2 ≤ (1 + x) * (al * (al + be)) := by
      have : (1 + x) * (al * (al + x)) ≤ (1 + x) * (al * (al + be)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have : 0 ≤ x * ((al - 1) * (al + 2 + x)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
      nlinarith
    have : (1 + x) * (al * (al + be)) ≤ (7 / 6 + 2) * (al * (al + be)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith

/-- The algebraic core of the `u`-increment of `Γ_*` at `q_c` (`s = 1/X`). -/
private theorem cas_Gqc_alg {x H H' sc d : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hHH : H = H' + (1 + x) * d) (hH : (1 + x) * H ≤ (x - 1) ^ 2 / 4) (hH'0 : 0 ≤ H')
    (hsc : sc = 1 / (x * (x + 2))) :
    (3 - H' ^ 2 - 2 * H' + 2 * H' * (2 * (1 + x) - 1 - H') * sc - H' ^ 2 * sc ^ 2) / 16 -
      (3 - H ^ 2 - 2 * H + 2 * H * (2 * (1 + x) - 1 - H) * sc - H ^ 2 * sc ^ 2) / 16 ≤ d / 4 := by
  have hS : 0 < 1 + x := by linarith
  have hX : 8 ≤ x * (x + 2) := by nlinarith
  have hsc0 : 0 < sc := by rw [hsc]; positivity
  have hsc8 : sc ≤ 1 / 8 := by rw [hsc]; exact one_div_le_one_div_of_le (by norm_num) hX
  have e : (3 - H' ^ 2 - 2 * H' + 2 * H' * (2 * (1 + x) - 1 - H') * sc - H' ^ 2 * sc ^ 2) / 16 -
      (3 - H ^ 2 - 2 * H + 2 * H * (2 * (1 + x) - 1 - H) * sc - H ^ 2 * sc ^ 2) / 16 =
      d * ((1 + x) * (H + H') * (1 + sc) ^ 2 + (1 + x) * (2 - 2 * (2 * (1 + x) - 1) * sc)) / 16 := by
    rw [hHH]; ring
  rw [e]
  have e2 : (1 + x) * (2 - 2 * (2 * (1 + x) - 1) * sc) = 2 * (x - 1) * (1 + sc) := by
    rw [hsc]; field_simp; ring
  rw [e2]
  have hb1 : (1 + x) * (H + H') ≤ (x - 1) ^ 2 / 2 := by
    have : (1 + x) * H' ≤ (1 + x) * H := by
      apply mul_le_mul_of_nonneg_left _ hS.le; rw [hHH]; nlinarith
    nlinarith
  have hHp : 0 ≤ (1 + x) * (H + H') := by
    have : 0 ≤ H := by rw [hHH]; positivity
    positivity
  have hsq : (1 + sc) ^ 2 ≤ 81 / 64 := by nlinarith
  have h1 : (1 + x) * (H + H') * (1 + sc) ^ 2 ≤ (49 / 72) * (81 / 64) := by
    calc (1 + x) * (H + H') * (1 + sc) ^ 2 ≤ (x - 1) ^ 2 / 2 * (81 / 64) :=
          mul_le_mul hb1 hsq (by positivity) (by positivity)
      _ ≤ (49 / 72) * (81 / 64) := by nlinarith
  have h2 : 2 * (x - 1) * (1 + sc) ≤ 2 * (7 / 6) * (9 / 8) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have := mul_le_mul_of_nonneg_left (by linarith : (1 + x) * (H + H') * (1 + sc) ^ 2 +
    2 * (x - 1) * (1 + sc) ≤ 4) hd
  linarith

/-- The `u`-increment of `Γ_*` at the central scale: `Γ_*(u') - Γ_*(u) ≤ (u' - u)/4`. -/
private theorem cas_Gqc_inc {x al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hu : 3 / 4 ≤ u) (huu : u ≤ u') (hu' : u' ≤ 31 / 40) :
    ssGs x al u' (ssQc x al) - ssGs x al u (ssQc x al) ≤ (u' - u) / 4 := by
  have hS : 0 < 1 + x := by linarith
  have hx0 : 0 < x := by linarith
  have hSig : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hqc' : ssQc x al = al ^ 2 / (x * (x + 2) + al ^ 2) := rfl
  have hqc1 : ssQc x al < 1 := by rw [hqc', div_lt_one hSig]; nlinarith
  have hs : ssQc x al / (al ^ 2 * (1 - ssQc x al)) = 1 / (x * (x + 2)) := by
    rw [hqc']; field_simp; ring
  rw [env_Gs_s hx0 hal1 hqc1, env_Gs_s hx0 hal1 hqc1, hs]
  have e : (1 + x) * (m2U (1 / (1 + x)) - 3 / 4) = (x - 1) ^ 2 / (4 * (1 + x)) := by
    unfold m2U; field_simp; ring
  have hU : (1 : ℝ) / 40 ≤ m2U (1 / (1 + x)) - 3 / 4 := by
    have e2 : m2U (1 / (1 + x)) - 3 / 4 = (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
      unfold m2U; field_simp; ring
    rw [e2, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  apply cas_Gqc_alg hx hx2 (by linarith) (by ring) _ (mul_nonneg hS.le (by linarith)) rfl
  have : (1 + x) * (m2U (1 / (1 + x)) - u) ≤ (x - 1) ^ 2 / (4 * (1 + x)) := by
    rw [← e]; exact mul_le_mul_of_nonneg_left (by linarith) hS.le
  have := mul_le_mul_of_nonneg_left this hS.le
  rw [show (1 + x) * ((x - 1) ^ 2 / (4 * (1 + x))) = (x - 1) ^ 2 / 4 by field_simp] at this
  exact this

/-- The final sign of the `u`-slopes of `Φ`, `Ψ`:
`7/4 - R_u < 0` and `7/4 - R_u - (T - 2)w_u < 0`, `R_u = 1/r_A + C(1 - 2z) - 2z(1 - z)`,
`w_u = z² - zC`. -/
private theorem cas_u_comb {d rA z C τ' : ℝ} (hd : 0 ≤ d) (hz3 : z ≤ 1 / 3) (hC1 : 1 ≤ C)
    (hC19 : C ≤ 19 / 6) (hrA : 30 / 11 ≤ rA) (hT0 : 0 ≤ τ') (hT1 : τ' ≤ 7 / 6) :
    d / 4 - d * (rA + C * (1 - 2 * z) - 2 * z * (1 - z)) / 7 ≤ 0 ∧
      d / 4 - d * (rA + C * (1 - 2 * z) - 2 * z * (1 - z)) / 7 - τ' * (d * (z ^ 2 - z * C)) / 7 ≤ 0 := by
  have hRu : 7 / 4 - (rA + C * (1 - 2 * z) - 2 * z * (1 - z)) ≤ 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 3 - z) (by linarith : (0 : ℝ) ≤ C)]
  have hRu' : 7 / 4 - (rA + C * (1 - 2 * z) - 2 * z * (1 - z)) - τ' * (z ^ 2 - z * C) ≤ 0 := by
    have h1 : 0 ≤ (1 / 3 - z) * (2 * C + 2 + τ' * C - (2 + τ') * (1 / 3 + z)) := by
      apply mul_nonneg (by linarith)
      nlinarith
    nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hRu hd]
  · nlinarith [mul_le_mul_of_nonneg_left hRu' hd]

/-- **`Φ`, `Ψ` decrease in `u`**: on the box of `cas_tau2_dec`, for `3/4 ≤ u ≤ u' ≤ 31/40`:
`Φ(u') ≤ Φ(u)` and `Ψ(u') ≤ Ψ(u)`.
Proof: `Γ_*(u') - Γ_*(u) ≤ (u' - u)/4` at `q_c` (`cas_Gqc_inc`), and
`R_u = 1/r_A + C(1 - 2z) - 2z(1 - z)` with `1/r_A ≥ 30/11`, `z ≤ 1/3`, `1 ≤ C ≤ 19/6`,
`0 ≤ T - 2 ≤ 7/6` (`cas_shape`, `cas_u_comb`). -/
theorem cas_u_dec {x δ al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : 3 / 4 ≤ u) (huu : u ≤ u')
    (hu' : u' ≤ 31 / 40) :
    casPhi x (x * (1 + δ)) al u' ≤ casPhi x (x * (1 + δ)) al u ∧
      casPsi x (x * (1 + δ)) al u' ≤ casPsi x (x * (1 + δ)) al u := by
  have hal1 : 1 ≤ al := by linarith
  have hal22 : al ≤ 22 / 19 := by linarith
  have hS : 0 < 1 + x := by linarith
  have hx0 : 0 < x := by linarith
  have hxb : x ≤ x * (1 + δ) := by nlinarith
  have hb130 : x * (1 + δ) ≤ 130 / 57 := by nlinarith
  have hDS := cas_D_le_S hx hal1 hal22 hxb
  have hG := cas_Gqc_inc hx hx2 hal1 hu huu hu'
  have hSig : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hqc' : ssQc x al = al ^ 2 / (x * (x + 2) + al ^ 2) := rfl
  have hqc0 : 0 < ssQc x al := by rw [hqc']; positivity
  set be := x * (1 + δ) with hbe
  set qc := ssQc x al with hqc
  -- the residual and the outer norm at `q_c` are affine in `u`
  set z := qc * (ssDg x be al / al ^ 2) with hz
  set C := (1 + x) * (1 - qc * (1 - 1 / al ^ 2)) with hC
  have hR : ssRs x be al u' qc 2 - ssRs x be al u qc 2 =
      (u' - u) * (1 / ssRA al be + C * (1 - 2 * z) - 2 * z * (1 - z)) := by
    rw [hz, hC]; unfold ssRs ssF ssWs ssELs ssA1 ssA2 ssA3 ssE0; ring
  have hW : ssWs x be al u' qc - ssWs x be al u qc = (u' - u) * (z ^ 2 - z * C) := by
    rw [hz, hC]; unfold ssWs ssA1 ssA2 ssE0; ring
  -- the shape bounds
  have hzS : z = ssDg x be al / (x * (x + 2) + al ^ 2) := by rw [hz, hqc']; field_simp
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := cas_shape hx hx2 hal1 hal22 hxb hb130 hDS
  have hz3 : z ≤ 1 / 3 := by rw [hzS, div_le_iff₀ hSig]; linarith
  have hCe : C = (1 + x) ^ 3 / (x * (x + 2) + al ^ 2) := by rw [hC, hqc']; field_simp; ring
  have hC1 : 1 ≤ C := by rw [hCe, le_div_iff₀ hSig]; linarith
  have hC19 : C ≤ 19 / 6 := by rw [hCe, div_le_iff₀ hSig]; linarith
  have hrA : 30 / 11 ≤ 1 / ssRA al be := by
    unfold ssRA; rw [one_div_div, le_div_iff₀ (by linarith)]; linarith
  have e : ssRA al be / qc = (x * (x + 2) + al ^ 2) / (al * (al + be)) := by
    rw [hqc']; unfold ssRA; field_simp
  have hab : 0 < al * (al + be) := by positivity
  have hT0 : 0 ≤ ssRA al be / qc - 2 := by
    rw [e, sub_nonneg, le_div_iff₀ hab]; linarith
  have hT1 : ssRA al be / qc - 2 ≤ 7 / 6 := by
    rw [e, sub_le_iff_le_add, div_le_iff₀ hab]; linarith
  have hfin := cas_u_comb (d := u' - u) (by linarith) hz3 hC1 hC19 hrA hT0 hT1
  rw [← hR, ← hW] at hfin
  obtain ⟨h1, h2⟩ := hfin
  constructor
  · unfold casPhi; linarith
  · unfold casPsi casPhi; linarith

/-- **The incoming majorant on the box**: for
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`: `ū(x, x(1 + δ)) < 31/40`. -/
theorem cas_ubar_box {x δ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19) :
    ssUbar x (x * (1 + δ)) < 31 / 40 := by
  unfold ssUbar
  have hx0 : 0 < x := by linarith
  have hb1 : 1 ≤ x * (1 + δ) - 1 := by nlinarith
  have h1 : 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) ≤ (x - 1) / 90 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 180 * (x - 1) ^ 2 ≤ (x + 1) * (35 * x + 13) := by nlinarith
    nlinarith
  have h2 : (x * (1 + δ) - x) ^ 3 / (48 * x ^ 2) ≤ 1 / 1000 := by
    have e : (x * (1 + δ) - x) ^ 3 / (48 * x ^ 2) = x * δ ^ 3 / 48 := by field_simp; ring
    rw [e]
    have : δ ^ 3 ≤ (1 / 19) ^ 3 := pow_le_pow_left₀ hδ hδ2 3
    have : x * δ ^ 3 ≤ 13 / 6 * (1 / 19) ^ 3 :=
      mul_le_mul hx2 this (by positivity) (by norm_num)
    rw [div_le_iff₀ (by norm_num)]; norm_num at this ⊢; linarith
  have h3 : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (x * (1 + δ) - x) ^ 3 / (48 * x ^ 2)) /
      (x * (1 + δ) - 1) < 1 / 40 := by
    rw [div_lt_iff₀ (by linarith)]
    have : 0 ≤ x * δ := by positivity
    nlinarith
  linarith

/-- **The extended original-Casimir floor at the central scale**: on the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`, with `u = ū(x, β)`:
`Φ > 1829/10000` and `Ψ > 1829/10000`. Proved in `SmallerShort/CasimirFloor/FloorBox` (the six derivative signs
W1-W6, then three scalar endpoints). -/
theorem cas_floor_box {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1829 / 10000 < casPhi x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) ∧
      1829 / 10000 < casPsi x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) := by
  apply cas_floor_box_proof <;> assumption

/-- **The ratio bound with constant `1/7`**:
`2ub + e ≤ (8/7)(1 - q)²(1 + τb)` when `e ≤ 3q`, `u ≤ 13/16`, `q < 3/20`, `τ > 2`,
`τq < 1/2`, `1 + τb > 0`. -/
private theorem cas_ratio {u q τ b e : ℝ} (hu : 3 / 4 ≤ u) (hu13 : u ≤ 13 / 16) (hq0 : 0 < q)
    (hq : q < 3 / 20) (hτ : 2 < τ) (hτq : τ * q < 1 / 2) (he : e ≤ 3 * q) (hB : 0 < 1 + τ * b) :
    2 * u * b + e ≤ 8 * (1 / 7) * (1 - q) ^ 2 * (1 + τ * b) := by
  have hτ0 : 0 < τ := by linarith
  have h1 : τ * (2 * u * b + e) ≤ 2 * u * (1 + τ * b) := by nlinarith
  have h2 : 2 * u ≤ 8 * (1 / 7) * (1 - q) ^ 2 * τ := by
    have : (17 / 20) ^ 2 ≤ (1 - q) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    nlinarith
  have h3 : τ * (2 * u * b + e) ≤ τ * (8 * (1 / 7) * (1 - q) ^ 2 * (1 + τ * b)) := by
    have := mul_le_mul_of_nonneg_right h2 hB.le
    nlinarith
  exact le_of_mul_le_mul_left h3 hτ0

/-- `0 < q_c ≤ 1/6` and `2q_c ≤ r_A` on the small box. -/
private theorem cas_qc {x be al : ℝ} (hx : 2 ≤ x) (hal1 : 1 ≤ al) (hal22 : al ≤ 22 / 19)
    (hxb : x ≤ be) (hb130 : be ≤ 130 / 57) :
    0 < ssQc x al ∧ ssQc x al ≤ 1 / 6 ∧ 2 * ssQc x al ≤ ssRA al be := by
  have hSig : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hX : 8 ≤ x * (x + 2) := by nlinarith
  have hal2 : al ^ 2 ≤ 7 / 5 := by nlinarith
  refine ⟨by unfold ssQc; positivity, ?_, ?_⟩
  · unfold ssQc; rw [div_le_iff₀ hSig]; linarith
  · unfold ssQc ssRA
    rw [mul_div_assoc', div_le_div_iff₀ hSig (by linarith)]
    have : al * be ≤ 22 / 19 * (130 / 57) := mul_le_mul hal22 hb130 (by linarith) (by norm_num)
    nlinarith

/-! ### The Casimir floor -/

namespace SmallerShortData

variable (H : SmallerShortData)

/-- **The corrected envelope cap with constant `1/7`**: for actual data,
`Γ_actual ≥ Γ_*(q) - R*_τ(q)/7` at the actual `q`, `τ`, shape and `u` (ratio
`(2ub + E_L)/(8(1 - q)²(1 + τb)) < u/(4τ(1 - q)²) < 1/7` from `E_L ≤ 3q`, `u ≤ 13/16`, `q < 3/20`;
two-segment monotonicity as in `lr_cap_env`).
Proof: `SmallerShortData.env_cap_data` with the ratio bound `cas_ratio` (`u ≤ 13/16` from `ss_V_le`,
`q < 3/20` from `q_lt`, `E_L ≤ 3q` from `env_EL_cap`). -/
theorem cas_cap_env : ssGs H.x H.al H.u H.q - ssRs H.x H.be H.al H.u H.q H.τ / 7 ≤ H.Γ := by
  have hEL : H.EL ≤ 3 * H.q := by
    have h := H.env_EL_cap
    have : 0 ≤ (m2U (ssRA H.al H.be) - H.u) / ssRA H.al H.be :=
      div_nonneg (by linarith [H.u_le_rA]) H.env_rA_pos.le
    linarith
  have hu13 : H.u ≤ 13 / 16 := H.u_le_V.trans (ss_V_le one_pos H.one_lt_x)
  have hτq : H.τ * H.q < 1 / 2 := H.τ_lt.trans H.env_rA_lt
  have h := H.env_cap_data (c := 1 / 7) (fun s _ e he hB =>
    cas_ratio H.u_ge_34 hu13 H.env_q_pos H.q_lt H.two_lt_τ hτq (he.trans hEL) hB)
  linarith

/-- **The Casimir floor**: on `2 ≤ x ≤ 13/6`, `δ ≤ 1/19`: `α ≤ 1 + 3δ` and `Γ > 1829/10000`.
Proof: (U) `ss_small_upper_order`; (F) `strong_box` and (U) give the box; `cas_cap_env`;
`p = τq`, `q ≤ q_c` (`q_le_qc`), `q ≤ p/2`; `cas_scale_dec_p` (`ss_phi_eq`) to `min{q_c, p/2}`, then
`cas_tau2_dec` to `q_c` (`ssQc ≤ 1/6`); `ss_dur_max` at `q_c` gives `Γ ≥ min{Φ, Ψ}(u)`;
`cas_u_dec` with `ss_sec_le_ubar`, `cas_ubar_box`; `cas_floor_box`.
The proof also uses `env_Rs_phi` (`R*_τ = Φ_p`) and `env_Rs_dur`. -/
theorem upper_order_casimir_floor (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) (h3 : H.δ ≤ 1 / 19) :
    H.al ≤ 1 + 3 * H.δ ∧ 1829 / 10000 < H.Γ := by
  have hx := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hδ : H.δ = H.be / H.x - 1 := rfl
  have hbe : H.be = H.x * (1 + H.δ) := by rw [hδ]; field_simp; ring
  have hδ0 : 0 ≤ H.δ := by rw [hδ, sub_nonneg, le_div_iff₀ hx0]; linarith [H.x_le_be]
  have hbe20 : H.be ≤ 20 / 19 * H.x := by
    rw [hbe]; have := mul_le_mul_of_nonneg_left h3 hx0.le; linarith
  have heq : m2Sec 1 H.x H.be = m2Sec H.al H.be H.x := H.u_eq.symm.trans H.u_eq'
  -- (U): the extended small-shape upper order
  have hU := ss_small_upper_order hx (by linarith) H.one_le_al H.al_lt_x H.x_le_be hbe20 heq
  rw [← hδ] at hU
  refine ⟨hU, ?_⟩
  -- (F): the box `13δ/5 ≤ α - 1 ≤ 3δ`
  have hL := H.strong_box h1
  have hal1 : 13 / 5 * H.δ ≤ H.al - 1 := by linarith
  have hal2 : H.al - 1 ≤ 3 * H.δ := by linarith
  have hal22 : H.al ≤ 22 / 19 := by linarith
  have hb130 : H.be ≤ 130 / 57 := by
    rw [hbe]; have := mul_le_mul h2 (by linarith : 1 + H.δ ≤ 20 / 19) (by linarith) (by norm_num)
    linarith
  obtain ⟨hqc0, hqc6, hTc⟩ := cas_qc h1 H.one_le_al hal22 H.x_le_be hb130
  have hu34 := H.u_ge_34
  have hubar : H.u ≤ ssUbar H.x H.be := H.u_eq ▸ ss_sec_le_ubar hx H.x_le_be
  have hub31 : ssUbar H.x H.be < 31 / 40 := by rw [hbe]; exact cas_ubar_box h1 h2 hδ0 h3
  -- the corrected envelope cap at the actual scale, in the fixed-`p` form
  have hcap := H.cas_cap_env
  have hq0 := H.env_q_pos
  have hτ0 : 0 < H.τ := by linarith [H.two_lt_τ]
  rw [env_Rs_phi hq0 hτ0] at hcap
  have hp0 : 0 < H.τ * H.q := by positivity
  have hpr : H.τ * H.q ≤ ssRA H.al H.be := H.τ_lt.le
  have hqp : H.q < H.τ * H.q / 2 := by nlinarith [H.two_lt_τ]
  have hqqc : H.q ≤ ssQc H.x H.al := H.q_le_qc
  have hdec := fun {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h : q₁ < q₂) (h₂ : q₂ ≤ 1 / 6) =>
    cas_scale_dec_p (be := H.be) (p := H.τ * H.q) hx H.one_le_al H.al_lt_x H.x_le_be hp0 hpr hu34
      H.u_le_r H.u_le_rA h₁ h h₂
  -- the scale move to `q_c`
  obtain ⟨τ', hτ'2, hτ'T, hΓ'⟩ : ∃ τ', 2 ≤ τ' ∧ τ' * ssQc H.x H.al ≤ ssRA H.al H.be ∧
      ssGs H.x H.al H.u (ssQc H.x H.al) - ssRs H.x H.be H.al H.u (ssQc H.x H.al) τ' / 7 ≤ H.Γ := by
    by_cases hc : ssQc H.x H.al ≤ H.τ * H.q / 2
    · refine ⟨H.τ * H.q / ssQc H.x H.al, by rw [le_div_iff₀ hqc0]; linarith, by
        rw [div_mul_cancel₀ _ hqc0.ne']; exact hpr, ?_⟩
      rw [env_Rs_phi hqc0 (by positivity), div_mul_cancel₀ _ hqc0.ne']
      rcases eq_or_lt_of_le hqqc with h | h
      · rw [← h]; linarith
      · have := hdec hq0 h hqc6; linarith
    · push Not at hc
      refine ⟨2, le_rfl, hTc, ?_⟩
      have h1' := hdec hq0 hqp (by linarith)
      have e : ssRs H.x H.be H.al H.u (H.τ * H.q / 2) 2 =
          ssPhi H.x H.be H.al H.u (H.τ * H.q) 0 (H.τ * H.q / 2) := by
        rw [env_Rs_phi (by linarith) (by norm_num), show 2 * (H.τ * H.q / 2) = H.τ * H.q by ring]
      rw [← e] at h1'
      have h2' := cas_tau2_dec h1 h2 hδ0 h3 hal1 hal2 hu34 (hubar.trans hub31.le) H.u_le_r
        (by linarith : 0 < H.τ * H.q / 2) hc hqc6
      rw [← hbe] at h2'
      linarith
  -- the duration maximum, then `u ↦ ū` and the floor
  have hdur := env_Rs_dur (x := H.x) (be := H.be) (u := H.u) hqc0 hτ'2 hτ'T
  have hud := cas_u_dec h1 h2 hδ0 h3 hal1 hal2 hu34 hubar hub31.le
  have hfl := cas_floor_box h1 h2 hδ0 h3 hal1 hal2
  rw [← hbe] at hud hfl
  unfold casPsi casPhi at hud hfl
  rcases max_cases (ssRs H.x H.be H.al H.u (ssQc H.x H.al) 2)
    (ssRs H.x H.be H.al H.u (ssQc H.x H.al) 2 + (ssRA H.al H.be / ssQc H.x H.al - 2) *
      (ssWs H.x H.be H.al H.u (ssQc H.x H.al) - 3 / 4)) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm] at hdur; linarith [hud.1, hfl.1]
  · rw [hm] at hdur; linarith [hud.2, hfl.2]

end SmallerShortData

/-- **The Casimir floor for the actual window**: given `2 ≤ C/a ≤ 13/6` and `B/C - 1 ≤ 1/19`,
`A/a ≤ 1 + 3(B/C - 1)` and `Γ > 1829/10000`. -/
theorem M2Short.upper_order_casimir_floor (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : D.B / D.C - 1 ≤ 1 / 19) :
    D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1) ∧ 1829 / 10000 < D.Γ := by
  have h := D.toData.upper_order_casimir_floor (by rwa [D.toData_x]) (by rwa [D.toData_x]) (by rwa [D.toData_δ])
  rwa [D.toData_al, D.toData_δ, D.toData_Γ] at h

end SmoothedOctagon
