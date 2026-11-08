module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S3: `δ < 1/19`

`MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION` with `DISPLACEMENT_{WEIGHT_REDUCTION, ZERO_SCALE,
SCALE_CONTINUATION, CENTRAL_BETA, CENTRAL_FACE, OUTER_FACE}`; inventory HS-S3 (R1-R45). Assuming
`2 ≤ x ≤ 13/6` (S1, S2) and `δ ≥ 1/19`: the displacement weight `m(y) = 4(4 - 3y)/(5α - 1)` gives
`G_τ = R_τ + m(w - 3/4) ≥ 0` at the actual root (`hs_env_weighted`, `hs3_B_pos`); the convex scale
polynomial (`hs_A2_pos`, `hs_phi_convex_max`), the zero-scale face (`hs3_zero_neg`) and the
`τ = 2` continuation (`hs3_tau2_cont`) reach `q* = min{q_c, 1/7}`; the duration tests (`hs3_dur`)
and the incoming slope (`hs3_uslope`) reduce to `F₀, F₁ < 0` on the central face (`hs3_central_*`)
or the outer face (`hs3_outer_*`).

## Main API

* `hs3Fn` (the test `J + n(w_* - 3/4)`), `hs3F0`, `hs3F1`, the ceilings `hsUCB`, `hsUO`, the central
  boundary `hs3b`, `hs3amin`.
* Stable: `hs3_shape`, `hs3_B_pos`, `hs3_uslope`, `hs3_dur`, `hs3_zero_neg`, `hs3_tau2_cont`,
  `hs3_central_straight`, `hs3_central_ceiling`, `hs3_beta_mono`, `hs3_log_maj`,
  `hs3_central_endpoint`, `hs3_outer_enclose`, `hs3_outer_ceiling`.
* Heavy: `hs3_central_alpha` (`DISPLACEMENT_CENTRAL_FACE` §2), `hs3_outer_face`
  (`DISPLACEMENT_OUTER_FACE` (7)-(21)).
* Gate: `HsData.s3`, `M2Short.hs_S3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The duration test `J + n(w_* - 3/4)`, `J = (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ`
(`DISPLACEMENT_HAND_EXCLUSION` l.66-75). -/
noncomputable def hs3Fn (x be al u q n ℓ : ℝ) : ℝ :=
  (u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q + ℓ +
    n * (hsWs x be al u q - 3 / 4)

/-- `F₀ = J + n₀(w_* - 3/4)`, `n₀ = 2 + 4(4 - 3y)/k`, `y = 2q/r_A`, `k = 5α - 1`, with
`ℓ = log(2q/r_A)`; `F₀ = G*_2`. -/
noncomputable def hs3F0 (x be al u q : ℝ) : ℝ :=
  hs3Fn x be al u q (2 + 4 * (4 - 3 * (2 * q / hsRA al be)) / (5 * al - 1))
    (log (2 * q / hsRA al be))

/-- `F₁ = J + n₁(w_* - 3/4)`, `n₁ = T + 4/k`, `T = r_A/q`. -/
noncomputable def hs3F1 (x be al u q : ℝ) : ℝ :=
  hs3Fn x be al u q (hsRA al be / q + 4 / (5 * al - 1)) (log (2 * q / hsRA al be))

/-- The central ceiling `ū(x, β) = 3/4 + ((x - 1)g(x) + (β - x)/5808)/(β - 1)`,
`g(x) = V_G(x) - 3/4` (`DISPLACEMENT_CENTRAL_BETA` (2)). -/
noncomputable def hsUCB (x be : ℝ) : ℝ := 3 / 4 + ((x - 1) * (hsVG x - 3 / 4) + (be - x) / 5808) / (be - 1)

/-- The outer ceiling `ū = 3/4 + (x - 1)²(x + β - 2)/((β - 1)(x + 1)(35x + 13))`
(`DISPLACEMENT_OUTER_FACE` (3)). -/
noncomputable def hsUO (x be : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (x + be - 2) / ((be - 1) * (x + 1) * (35 * x + 13))

/-- The central boundary `b(x, α) = x + (25x/(15x + 36))(α - 1)` (`DISPLACEMENT_CENTRAL_FACE` (1)). -/
noncomputable def hs3b (x al : ℝ) : ℝ := x + 25 * x / (15 * x + 36) * (al - 1)

/-- `a_min(x) = (15x + 511)/475` (`DISPLACEMENT_CENTRAL_FACE` (2)). -/
noncomputable def hs3amin (x : ℝ) : ℝ := (15 * x + 511) / 475

/-! ### The weighted reduction -/

/-- **Shape bounds on the displacement domain** (`DISPLACEMENT_WEIGHT_REDUCTION` §1 (2)-(4);
inventory HS-S3 R9): for `2 ≤ x ≤ 13/6`, `1 ≤ α ≤ x ≤ β`, `δ = β/x - 1 ≥ 1/19`,
`α ≥ 1 + c(x)δ` and `β ≥ x(9x + 8α)/(9x + 8)`: `α ≥ 108/95`, `β < 2α`, `1/3 < r_A ≤ 13/30`.
Status: stable. -/
theorem hs3_shape {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hL : 1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) ≤ al)
    (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) :
    108 / 95 ≤ al ∧ be < 2 * al ∧ 1 / 3 < hsRA al be ∧ hsRA al be ≤ 13 / 30 := by
  sorry

/-- **The displacement-weighted positive factor** (`DISPLACEMENT_WEIGHT_REDUCTION` (8)-(11);
inventory HS-S3 R11): for `x ≥ 2`, `1 ≤ α ≤ x ≤ β`, `ρ > 0`, `s ≥ ρ(1 + x)`, `2 ≤ τ`, `τq ≤ r_A`,
with `m = 4(4 - 3τq/r_A)/(5α - 1)`: `B_{τ+m}(s) > 0`. Status: stable. -/
theorem hs3_B_pos {x be al rho s τ : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hτ : 2 ≤ τ) (hτT : τ * hsQ al rho ≤ hsRA al be) :
    0 < 1 + (τ + 4 * (4 - 3 * (τ * hsQ al rho / hsRA al be)) / (5 * al - 1)) *
      (hsLam al rho * s - hsLam al rho * rho * hsDg x be al) := by
  sorry

/-- **The positive incoming coefficient** (`DISPLACEMENT_WEIGHT_REDUCTION` (13)-(15); inventory
HS-S3 R12): for `2 ≤ x ≤ 13/6`, `11/10 ≤ α ≤ x ≤ β`, `0 < D < α(α + β)`, `D < 3α²`, `0 < q ≤ 1/7`,
`r_A ≤ 13/30` and `0 ≤ n ≤ r_A/q + 1`, the test `J + n(w_* - 3/4)` is nondecreasing in `u`
(slope `c_u(n) > 17/182`). Status: stable. -/
theorem hs3_uslope {x be al q n ℓ u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 11 / 10 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD : 0 < hsDg x be al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hrA : hsRA al be ≤ 13 / 30)
    (hn : 0 ≤ n) (hnT : n ≤ hsRA al be / q + 1) (huu : u ≤ u') :
    hs3Fn x be al u q n ℓ ≤ hs3Fn x be al u' q n ℓ := by
  sorry

/-- **The two duration tests** (`DISPLACEMENT_WEIGHT_REDUCTION` (19)-(21); inventory HS-S3 R14):
for `α ≥ 1`, `β > 0`, `q > 0`, `2 ≤ τ`, `τq ≤ r_A`, the weighted envelope
`G*_τ = R*_τ + m(τq/r_A)(w_* - 3/4)` satisfies `G*_τ ≤ max{F₀, F₁}` (exact remainder
`τ/4 - 1/τ - log(τ/2) ≥ 0`). Status: stable. -/
theorem hs3_dur {x be al u q τ : ℝ} (hal : 1 ≤ al) (hbe : 0 < be) (hq : 0 < q) (hτ : 2 ≤ τ)
    (hτT : τ * q ≤ hsRA al be) :
    hsF x be al u q τ (log (τ * q / hsRA al be)) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) ≤
      max (hs3F0 x be al u q) (hs3F1 x be al u q) := by
  sorry

/-- **The zero-scale face** (`DISPLACEMENT_ZERO_SCALE` (2)-(23); inventory HS-S3 R16-R22): for
`2 ≤ x ≤ 13/6`, `1 < α ≤ x ≤ β`, `β ≥ x(9x + 8α)/(9x + 8)`, `1/3 < r_A ≤ 13/30`,
`3/4 ≤ u ≤ U(r_A)`, `D < α(α + β)` and `0 < p ≤ r_A`: `Φ(0) = C(p) + m/4 < 0`,
`m = 4(4 - 3p/r_A)/(5α - 1)`. Status: stable. -/
theorem hs3_zero_neg {x be al u p : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 < al) (hax : al ≤ x)
    (hxb : x ≤ be) (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) (hrA : 1 / 3 < hsRA al be)
    (hrA' : hsRA al be ≤ 13 / 30) (hu : 3 / 4 ≤ u) (hurA : u ≤ m2U (hsRA al be))
    (hDQ : hsDg x be al < al * (al + be)) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    hsPhi x be al u p (4 * (4 - 3 * (p / hsRA al be)) / (5 * al - 1)) 0 < 0 := by
  sorry

/-- **The `τ = 2` continuation** (`DISPLACEMENT_SCALE_CONTINUATION` (1)-(19); inventory HS-S3
R23-R28): for `2 ≤ x ≤ 13/6`, `11/10 ≤ α ≤ x ≤ β`, `1/3 ≤ r_A`, `3/4 ≤ u ≤ 19/25`,
`0 < D < 3α²`, `G*_2(q) = R*_2(q) + m(2q/r_A)(w_*(q) - 3/4)` is strictly increasing on `(0, 1/7]`.
Status: stable. -/
theorem hs3_tau2_cont {x be al u q₁ q₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 11 / 10 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hrA : 1 / 3 ≤ hsRA al be) (hu : 3 / 4 ≤ u) (hu' : u ≤ 19 / 25)
    (hD : 0 < hsDg x be al) (hD3 : hsDg x be al < 3 * al ^ 2) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 7) :
    hsF x be al u q₁ 2 (log (2 * q₁ / hsRA al be))
        (4 * (4 - 3 * (2 * q₁ / hsRA al be)) / (5 * al - 1)) <
      hsF x be al u q₂ 2 (log (2 * q₂ / hsRA al be))
        (4 * (4 - 3 * (2 * q₂ / hsRA al be)) / (5 * al - 1)) := by
  sorry

/-! ### The central face `q* = q_c ≤ 1/7` -/

/-- **The straight order bound** (`DISPLACEMENT_CENTRAL_FACE` §1 (1)-(3); inventory HS-S3 R33): for
`2 ≤ x ≤ 13/6`, `δ = β/x - 1 ≥ 1/19` and the quadratic order `α ≥ 1 + (c(x) + 1/23)δ`
(`hs_quad_order`, `δ/(1 + 4δ) ≥ 1/23`):
`a_min(x) < α` and `β < b(x, α)`. Status: stable. -/
theorem hs3_central_straight {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6)
    (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al) :
    hs3amin x < al ∧ be < hs3b x al := by
  sorry

/-- **The central incoming ceiling** (`DISPLACEMENT_CENTRAL_BETA` §2 (2), (5); inventory HS-S3 R29):
on `2 ≤ x ≤ 13/6`, `α ≥ 108/95`, `6α² ≤ x(x + 2)`, `20x/19 ≤ β ≤ x + 5x(α - 1)/13`:
`Sec(1, x, β) ≤ ū(x, β)`. Status: stable. -/
theorem hs3_central_ceiling {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be)
    (hb' : be ≤ x + 5 * x * (al - 1) / 13) : m2Sec 1 x be ≤ hsUCB x be := by
  sorry

/-- **β-monotonicity on the central face** (`DISPLACEMENT_CENTRAL_BETA` (4), (18)-(21); inventory
HS-S3 R30-R32): on `2 ≤ x ≤ 13/6`, `α ≥ 108/95`, `6α² ≤ x(x + 2)`, for
`20x/19 ≤ β₁ ≤ β₂ ≤ min{2α, x + 5x(α - 1)/13}`, `F_i(x, α, β₁; ū) ≤ F_i(x, α, β₂; ū)` at `q = q_c`
(`(F₀)_β > 7/1500`, `(F₁)_β > 1/1200`). Status: stable. -/
theorem hs3_beta_mono {x al be₁ be₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be₁) (hbb : be₁ ≤ be₂)
    (hb2 : be₂ ≤ 2 * al) (hb2' : be₂ ≤ x + 5 * x * (al - 1) / 13) :
    hs3F0 x be₁ al (hsUCB x be₁) (hsQc x al) ≤ hs3F0 x be₂ al (hsUCB x be₂) (hsQc x al) ∧
      hs3F1 x be₁ al (hsUCB x be₁) (hsQc x al) ≤ hs3F1 x be₂ al (hsUCB x be₂) (hsQc x al) := by
  sorry

/-- **The rational log majorant** (`DISPLACEMENT_CENTRAL_FACE` (11); inventory HS-S3 R35): for
`0 < y ≤ 6/7`, `log y ≤ -40153/180000 + 2(5y - 4)/(5y + 4)`. Status: stable. -/
theorem hs3_log_maj {y : ℝ} (hy : 0 < y) (hy7 : y ≤ 6 / 7) :
    log y ≤ -40153 / 180000 + 2 * (5 * y - 4) / (5 * y + 4) := by
  sorry

/-- **The central endpoint signs** (`DISPLACEMENT_CENTRAL_FACE` (12)-(13); inventory HS-S3 R36):
for `2 ≤ x ≤ 13/6`, at `α = a_min(x)`, `β = 20x/19`, `q = q_c`, `u = ū`: `F₀ < 0`, `F₁ < 0`.
Status: stable. -/
theorem hs3_central_endpoint {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    hs3F0 x (20 * x / 19) (hs3amin x) (hsUCB x (20 * x / 19)) (hsQc x (hs3amin x)) < 0 ∧
      hs3F1 x (20 * x / 19) (hs3amin x) (hsUCB x (20 * x / 19)) (hsQc x (hs3amin x)) < 0 := by
  sorry

/-- **The central face along the boundary** (`DISPLACEMENT_CENTRAL_FACE` §2 (4)-(10) with
(11)-(13); inventory HS-S3 R34, R37): for `2 ≤ x ≤ 13/6` and `a_min(x) ≤ α ≤ 89/72`, at
`β = b(x, α)`, `q = q_c`, `u = ū(x, β)`: `F₀ < 0` and `F₁ < 0` (the notes: `d/dα F_i(x, α, b(x, α)) <
0` on `[108/95, 89/72]`, then `hs3_central_endpoint`). Status: heavy. -/
theorem hs3_central_alpha {x al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : hs3amin x ≤ al)
    (hal' : al ≤ 89 / 72) :
    hs3F0 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 ∧
      hs3F1 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 := by
  sorry

/-! ### The outer face `q* = 1/7 ≤ q_c` -/

/-- **The enclosing outer domain** (`DISPLACEMENT_OUTER_FACE` §1 (1)-(2); inventory HS-S3 R38): for
`2 ≤ x ≤ 13/6`, `α ≤ x`, `x(x + 2) ≤ 6α²`, `β ≥ x(9x + 8α)/(9x + 8)`, `δ = β/x - 1 ≥ 1/19` and
`α ≥ 1 + (c(x) + 1/23)δ`: `a₀(x) = (100x + 77)/240 ≤ α` and `1/4 ≤ δ/(α - 1) ≤ 115/304`.
Status: stable. -/
theorem hs3_outer_enclose {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hax : al ≤ x)
    (hqc : x * (x + 2) ≤ 6 * al ^ 2) (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be)
    (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al) :
    (100 * x + 77) / 240 ≤ al ∧ 1 / 4 ≤ (be / x - 1) / (al - 1) ∧
      (be / x - 1) / (al - 1) ≤ 115 / 304 := by
  sorry

/-- **The outer incoming ceiling** (`DISPLACEMENT_OUTER_FACE` (3); inventory HS-S3 R39): for
`2 ≤ x ≤ 13/6`, `x ≤ β ≤ x + 5x(x - 1)/13`: `Sec(1, x, β) ≤ ū(x, β)`. Status: stable. -/
theorem hs3_outer_ceiling {x be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hxb : x ≤ be)
    (hb : be ≤ x + 5 * x * (x - 1) / 13) : m2Sec 1 x be ≤ hsUO x be := by
  sorry

/-- **The outer displacement face** (`DISPLACEMENT_OUTER_FACE` (4)-(21), §6; inventory HS-S3
R40-R44): on `2 ≤ x ≤ 13/6`, `(100x + 77)/240 ≤ α ≤ x`, `β = x(1 + g(α - 1))` with
`1/4 ≤ g ≤ 115/304`, at `q = 1/7`, `u = ū(x, β)`: `F₀ < 0` and `F₁ < 0`. Status: heavy. -/
theorem hs3_outer_face {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F0 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 ∧
      hs3F1 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 := by
  sorry

/-! ### Gate S3 -/

namespace HsData

variable (H : HsData)

/-- **Gate S3** (`DISPLACEMENT_HAND_EXCLUSION`; inventory HS-S3 R45): for `2 ≤ x ≤ 13/6`,
`δ < 1/19`.
Proof plan: if `δ ≥ 1/19`: `strong_order`, `upper_order_98`, `hs_quad_order`, `hs3_shape`,
`hs_D_lt_Q`, `u_le_V`, `hs_V_le_Vbar` give the shape bounds; `root_zero`, `w_ge`,
`hs_env_weighted` (`hs3_B_pos`) give `0 ≤ G*_τ`; `hs_phi_eq`, `hs_A2_pos`, `hs_phi_convex_max`,
`hs3_zero_neg`, `q_le_qc`, `q_lt_seventh`, `hs3_tau2_cont` reach `q*`; `hs3_dur`, `hs3_uslope`; then
the central face (`hs_qc_le_iff`, `hs3_central_straight`, `hs3_central_ceiling`, `hs3_beta_mono`,
`hs3_central_alpha`) or the outer face (`hs3_outer_enclose`, `hs3_outer_ceiling`, `hs3_outer_face`)
contradicts.
Status: assembly (to be proved from the leaves above). -/
theorem s3 (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) : H.δ < 1 / 19 := by
  sorry

end HsData

/-- **Gate S3 for the actual window**: given `2 ≤ C/a ≤ 13/6`, `B/C - 1 < 1/19`. -/
theorem M2Short.hs_S3 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6) :
    D.B / D.C - 1 < 1 / 19 := by
  have h := D.toHs.s3 (by rwa [D.toHs_x]) (by rwa [D.toHs_x])
  rwa [D.toHs_δ] at h

end SmoothedOctagon
