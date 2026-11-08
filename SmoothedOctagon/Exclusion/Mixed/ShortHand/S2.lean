module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S2: `x < 13/6`

`MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION`, with `VARIABLE_FLOOR_REDUCTION`,
`CENTRAL_RATIO_HAND_SIGN`, `OUTER_RATIO_HAND_SIGN`; inventory HS-S2 (R1-R25). Assuming
`13/6 ≤ x < 12/5` (the upper end from S0): the variable-floor weight `m = 2 - 7τ/(4T)` gives
`G_τ = R_τ + m(w - 3/4) ≥ 0` at the actual root; the envelope (`hs_env_weighted`,
`hs_B_pos_weighted`), the convex scale polynomial (`hs_A2_pos`, `hs_phi_convex_max`,
`hs2_zero_neg`) and the `τ = 2` continuation (`hs2_tau2_mono`) reach a face `q* = min{q_c, 1/7}`;
the incoming coefficient (`hs2_uslope`) and the face ceilings (`hs2_central_ceiling`,
`hs2_outer_ceiling`) reduce to the face signs `hs2_central_sign`, `hs2_outer_sign_small`,
`hs2_outer_sign_large` (heavy).

## Main API

* `hsUC`, `hsUs`: the face ceilings `u_C`, `u_s`.
* Stable: `hs2_uslope`, `hs2_zero_neg`, `hs2_tau2_mono`, `hs2_central_ceiling`,
  `hs2_outer_ceiling`.
* Heavy: `hs2_central_sign` (`CENTRAL_RATIO_HAND_SIGN` (5)), `hs2_outer_sign_small`,
  `hs2_outer_sign_large` (`OUTER_RATIO_HAND_SIGN` (13), (16), (18)).
* Gate: `HsData.s2`, `M2Short.hs_S2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The central ceiling `u_C(x, β) = 3/4 + (680(x - 1)³ + 3S²(β - x))/(9600S²(β - 1))`
(`RATIO_SIGN_HAND_GAP` (4), `CENTRAL_RATIO_HAND_SIGN` (3)). -/
noncomputable def hsUC (x be : ℝ) : ℝ :=
  3 / 4 + (680 * (x - 1) ^ 3 + 3 * (1 + x) ^ 2 * (be - x)) / (9600 * (1 + x) ^ 2 * (be - 1))

/-- The outer ceiling `u_s(x, β) = 3/4 + (17(x - 1)³/(240S²) + (β - x)/1200)/(β - 1)`
(`OUTER_RATIO_HAND_SIGN` (9)). -/
noncomputable def hsUs (x be : ℝ) : ℝ :=
  3 / 4 + (17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) + (be - x) / 1200) / (be - 1)

/-- **The positive incoming coefficient** (`VARIABLE_FLOOR_REDUCTION` (8)-(9); inventory HS-S2 R15):
for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β`, `α < β`, `0 < D < α(α + β)`, `D < 3α²`, `0 < q ≤ 1/7`,
`2 ≤ τ ≤ T = r_A/q`, the variable-floor face value (weight `m = 2 - 7τq/(4r_A)`) is nondecreasing in
`u` (slope `> 109/140`). Status: stable. -/
theorem hs2_uslope {x be al q τ ℓ u u' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hab : al < be) (hD : 0 < hsDg x be al)
    (hDQ : hsDg x be al < al * (al + be)) (hD3 : hsDg x be al < 3 * al ^ 2) (hq : 0 < q)
    (hq7 : q ≤ 1 / 7) (hτ : 2 ≤ τ) (hτT : τ * q ≤ hsRA al be) (huu : u ≤ u') :
    hsF x be al u q τ ℓ (2 - 7 * τ * q / (4 * hsRA al be)) ≤
      hsF x be al u' q τ ℓ (2 - 7 * τ * q / (4 * hsRA al be)) := by
  sorry

/-- **The zero-scale end** (`VARIABLE_FLOOR_REDUCTION` (13)-(15); inventory HS-S2 R18): for
`13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β ≤ αx`, `r_A < 3/7`, `D < α(α + β)`, `3/4 ≤ u ≤ 61/80`,
`u ≤ U(r_A)` and `0 < p ≤ r_A`: `Φ(0) = C(p) + m/4 < 0`, `m = 2 - 7p/(4r_A)`. Status: stable. -/
theorem hs2_zero_neg {x be al u p : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hbx : be ≤ al * x) (hrA : hsRA al be < 3 / 7)
    (hDQ : hsDg x be al < al * (al + be)) (hu : 3 / 4 ≤ u) (hu' : u ≤ 61 / 80)
    (hurA : u ≤ m2U (hsRA al be)) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    hsPhi x be al u p (2 - 7 * p / (4 * hsRA al be)) 0 < 0 := by
  sorry

/-- **The `τ = 2` continuation** (`VARIABLE_FLOOR_REDUCTION` (16)-(26); inventory HS-S2 R19): for
`13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ x ≤ β`, `D ≥ 0`, `5/17 ≤ r_A ≤ 3/7`, `3/4 ≤ u ≤ 61/80`,
`G₂(q) = R*_2(q) + (2 - 7q/(2r_A))(w_*(q) - 3/4)` is strictly increasing on `(0, 1/7]`.
Status: stable. -/
theorem hs2_tau2_mono {x be al u q₁ q₂ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD : 0 ≤ hsDg x be al) (hrA : 5 / 17 ≤ hsRA al be)
    (hrA' : hsRA al be ≤ 3 / 7) (hu : 3 / 4 ≤ u) (hu' : u ≤ 61 / 80) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    hsF x be al u q₁ 2 (log (2 * q₁ / hsRA al be)) (2 - 7 * q₁ / (2 * hsRA al be)) <
      hsF x be al u q₂ 2 (log (2 * q₂ / hsRA al be)) (2 - 7 * q₂ / (2 * hsRA al be)) := by
  sorry

/-- **The central ceiling** (`RATIO_SIGN_HAND_GAP` (4); inventory HS-S2 R1, R2(a), R21): for
`13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`, `x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`:
`Sec(1, x, β) ≤ u_C(x, β)`. Status: stable. -/
theorem hs2_central_ceiling {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    m2Sec 1 x be ≤ hsUC x be := by
  sorry

/-- **The outer ceiling** (`OUTER_RATIO_HAND_SIGN` (9); inventory HS-S2 R22(a)): for
`13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ 3/2`, `x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`:
`Sec(1, x, β) ≤ u_s(x, β)`. Status: stable. -/
theorem hs2_outer_ceiling {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    m2Sec 1 x be ≤ hsUs x be := by
  sorry

/-! ### Heavy face signs -/

/-- **The central sharp-ratio face** (`CENTRAL_RATIO_HAND_SIGN` (5); inventory HS-S2 R23): for
`13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`, the strip
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `q = q_c`, `u = u_C(x, β)` and
`2 ≤ τ ≤ T = r_A/q_c`: `G_τ = R*_τ + (2 - 7τ/(4T))(w_* - 3/4) < 0`. Status: heavy. -/
theorem hs2_central_sign {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x al ≤ hsRA al be) :
    hsF x be al (hsUC x be) (hsQc x al) τ (log (τ * hsQc x al / hsRA al be))
      (2 - 7 * τ * hsQc x al / (4 * hsRA al be)) < 0 := by
  sorry

/-- **The outer sharp-ratio face, small `α`** (`OUTER_RATIO_HAND_SIGN` §§4-5, (13), (16); inventory
HS-S2 R24): for `13/6 ≤ x ≤ 12/5`, `1 ≤ α ≤ 3/2`, `α ≤ x`, `x(x + 2) ≤ 6α²`, the strip of
`hs2_central_sign`, `q = 1/7`, `u = u_s(x, β)` and `2 ≤ τ ≤ 7r_A`: `G_τ < 0`. Status: heavy. -/
theorem hs2_outer_sign_small {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (hax : al ≤ x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsUs x be) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  sorry

/-- **The outer sharp-ratio face, large `α`** (`OUTER_RATIO_HAND_SIGN` §6, (18); inventory HS-S2
R24): for `13/6 ≤ x ≤ 12/5`, `3/2 ≤ α ≤ x`, the strip of `hs2_central_sign`, `q = 1/7`,
`u = V̄(x)` and `2 ≤ τ ≤ 7r_A`: `G_τ < 0`. Status: heavy. -/
theorem hs2_outer_sign_large {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 3 / 2 ≤ al) (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsVbar x) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  sorry

/-! ### Gate S2 -/

namespace HsData

variable (H : HsData)

/-- **Gate S2** (`SHARP_RATIO_HAND_EXCLUSION`; inventory HS-S2 R25): given S0's `x < 12/5`,
`x < 13/6`.
Proof plan: if `x ≥ 13/6`: `root_zero`, `w_ge`, `hs_env_weighted` with `m = 2 - 7τq/(4r_A)`
(`hs_B_pos_weighted`) give `0 ≤ G*_τ`; `hs_phi_eq`, `hs_A2_pos` (with `u_le_V`, `hs_V_le_Vbar`),
`hs_phi_convex_max`, `hs2_zero_neg` (`hs_D_lt_Q`, `upper_order_98`, `be_le_al_x`, `u_le_rA`) and
`hs2_tau2_mono` reach `G*(q*, τ*) ≥ 0` at `q* = min{q_c, 1/7}`; `hs2_uslope` with
`hs2_central_ceiling` or `hs2_outer_ceiling` / `hs_V_le_Vbar` replaces `u`; the strip is
`strong_order`, `upper_order_98`; contradiction with `hs2_central_sign`, `hs2_outer_sign_small`,
`hs2_outer_sign_large`.
Status: assembly (to be proved from the leaves above). -/
theorem s2 (h0 : H.x < 12 / 5) : H.x < 13 / 6 := by
  sorry

end HsData

/-- **Gate S2 for the actual window**: given `C/a < 12/5`, `C/a < 13/6`. -/
theorem M2Short.hs_S2 (D : M2Short) (h0 : D.C / D.a < 12 / 5) : D.C / D.a < 13 / 6 := by
  have h := D.toHs.s2 (by rwa [D.toHs_x])
  rwa [D.toHs_x] at h

end SmoothedOctagon
