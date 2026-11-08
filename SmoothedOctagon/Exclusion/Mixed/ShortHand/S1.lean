module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S1: `x > 2`

`MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION`; inventory HS-S01 Parts C, D (C1-C24, D-R1-D-R22,
M19). Assuming `1 < x ≤ 2`: the corrected envelope cap `Γ_actual ≥ Γ_* - (7/96)R*_τ`
(`HsData.hs1_cap_env`, from the retained root bound `hs1_root_cap` and the derivative ratio
`hs1_ratio`), the scale motions at fixed `p` and at `τ = 2` (`hs1_scale_dec`, `hs1_tau2_dec`) reach
a face `q = q_c ≤ 1/7` or `q = 1/7 ≤ q_c`, where the terminal face signs (heavy)
`hs1_central_face`, `hs1_outer_face` give `Γ_* - (7/96)R*_τ > 9193/50000`, contradicting `cas_lt`.

## Main API

* `hs1_root_cap` (`SHARP_LOW_RATIO_CORRECTED_CAP` (3)), `hs1_ratio` (`(4)-(15)`),
  `hs1_slope` (`(17)-(19)`), `hs1_scale_dec` (`(20)`), `hs1_tau2_dec` (`(21)-(26)`),
  `hs1_u_ell` (`LOW_RATIO_CENTRAL_HAND_SIGN` (16)-(17)).
* `HsData.hs1_cap_env` (`SHARP_LOW_RATIO_CORRECTED_CAP` (16), `CORRECTED_ENVELOPE_CAP` (8)-(9)).
* Heavy: `hs1_central_face` (`LOW_RATIO_CENTRAL_HAND_SIGN` (6)), `hs1_outer_face`
  (`LOW_RATIO_OUTER_HAND_SIGN` §6).
* Gate: `HsData.s1`, `M2Short.hs_S1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The retained incoming deficit at the actual root** (`SHARP_LOW_RATIO_CORRECTED_CAP` (3);
inventory HS-S01 C10): if `0 < r_A < 1/2`, `τ > 2`, `0 < q`, `τq < r_A`, `u ≤ U(r_A)`,
`w ≤ U(1/τ)` and `E_L = (w - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q + log(τq/r_A)`, then
`E_L ≤ 3q - J_A`, `J_A = (U(r_A) - u)/r_A` (`ss_E_le_three` with the norm `U(r_A)`).
Status: stable. -/
theorem hs1_root_cap {rA τ q u w EL : ℝ} (hrA : 0 < rA) (hrA2 : rA < 1 / 2) (hτ : 2 < τ)
    (hq : 0 < q) (hτq : τ * q < rA) (hu : u ≤ m2U rA) (hw : w ≤ m2U (1 / τ))
    (hEL : EL = (w - 1) * τ + 1 / τ + (u - 1) / rA + rA + 1 - q + log (τ * q / rA)) :
    EL ≤ 3 * q - (m2U rA - u) / rA := by
  sorry

/-- **The derivative ratio is at most `7/96`** (`SHARP_LOW_RATIO_CORRECTED_CAP` (4)-(15); inventory
HS-S01 C11, C13, C14): for `1 < x ≤ 2`, `1 ≤ α < x ≤ β`, `D > 0`, `3/4 ≤ u ≤ u₀(x)`, `u ≤ U(r_A)`,
`ρ > 0`, `q = α²λρ ≤ 1/7`, `2 ≤ τ`, `τq < r_A`, `0 < t ≤ 1/(1 + x)`, `b = λt - d` with
`1 + τb > 0`, and any `E_L ≤ 3q - J_A`: `2ub + E_L ≤ (7/12)(1 - q)²(1 + τb)`, i.e.
`Γ_v/(R_τ)_v = (2ub + E_L)/(8(1 - q)²(1 + τb)) ≤ 7/96`. Status: stable. -/
theorem hs1_ratio {x be al u rho τ t EL : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al < x) (hxb : x ≤ be) (hD : 0 < hsDg x be al) (hu : 3 / 4 ≤ u) (hu0 : u ≤ hsU0 x)
    (hurA : u ≤ m2U (hsRA al be)) (hρ : 0 < rho) (hq7 : hsQ al rho ≤ 1 / 7) (hτ : 2 ≤ τ)
    (hτq : τ * hsQ al rho < hsRA al be) (ht : 0 < t) (htr : t ≤ 1 / (1 + x))
    (hB : 0 < 1 + τ * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al))
    (hEL : EL ≤ 3 * hsQ al rho - (m2U (hsRA al be) - u) / hsRA al be) :
    2 * u * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al) + EL ≤
      7 / 12 * (1 - hsQ al rho) ^ 2 *
        (1 + τ * (hsLam al rho * t - hsLam al rho * rho * hsDg x be al)) := by
  sorry

/-- **The sharper slope** (`SHARP_LOW_RATIO_CORRECTED_CAP` (17)-(19), `CORRECTED_CAP_SCALE` (1)-(7);
inventory HS-S01 C7, C8, C16): for `1 < x ≤ 2`, `1 ≤ α ≤ x`, `β ≥ x + 8x(α - 1)/(9x + 8)`,
`0 < p ≤ α/(α + β)`, `3/4 ≤ u ≤ U(1/S)`: `3α²L(p) > 7J(2S - 1)`, `J = S[U(1/S) - u]`.
Status: stable. -/
theorem hs1_slope {x be al u p : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be) (hp : 0 < p) (hpr : p ≤ hsRA al be)
    (hu : 3 / 4 ≤ u) (huS : u ≤ m2U (1 / (1 + x))) :
    7 * ((1 + x) * (m2U (1 / (1 + x)) - u)) * (2 * (1 + x) - 1) < 3 * al ^ 2 * hsLp x be al u p := by
  sorry

/-- **The fixed-`p` decrease** (`SHARP_LOW_RATIO_CORRECTED_CAP` (20); inventory HS-S01 C9, C17):
under the hypotheses of `hs1_slope`, `q ↦ Γ_*(q) - (7/96)R*_{p/q}(q)` is strictly decreasing on
`(0, 1/7]` (`∂_q Γ_* ≤ J(2S - 1)/(8α²(1 - q)²) < (7/96)L(p)`). Status: stable. -/
theorem hs1_scale_dec {x be al u p q₁ q₂ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be) (hp : 0 < p)
    (hpr : p ≤ hsRA al be) (hu : 3 / 4 ≤ u) (huS : u ≤ m2U (1 / (1 + x))) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    hsGs x al u q₂ - 7 / 96 * hsPhi x be al u p 0 q₂ <
      hsGs x al u q₁ - 7 / 96 * hsPhi x be al u p 0 q₁ := by
  sorry

/-- **The `τ = 2` decrease** (`SHARP_LOW_RATIO_CORRECTED_CAP` (21)-(26); inventory HS-S01 C18, C19):
for `1 < x ≤ 2`, `α ≥ 1`, `β ≥ x`, `3/4 ≤ u ≤ u₀(x)`, `q ↦ Γ_*(q) - (7/96)R*_2(q)` is strictly
decreasing on `(0, 1/7]` (`q·R*_2' > 1/7 ≥ q`). Status: stable. -/
theorem hs1_tau2_dec {x be al u q₁ q₂ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hxb : x ≤ be) (hu : 3 / 4 ≤ u) (hu0 : u ≤ hsU0 x) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 7) :
    hsGs x al u q₂ - 7 / 96 * hsRs x be al u q₂ 2 < hsGs x al u q₁ - 7 / 96 * hsRs x be al u q₁ 2 := by
  sorry

/-- **The β-dependent ceiling** (`LOW_RATIO_CENTRAL_HAND_SIGN` (16)-(17); inventory HS-S01 D-R10):
for `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`:
`ū(x, β) ≤ u_ℓ(x, β)`. Status: stable. -/
theorem hs1_u_ell {x al be : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hal' : al ≤ 6 / 5)
    (hxb : x ≤ be) (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsUbar x be ≤ hsUl x be := by
  sorry

/-! ### Heavy terminal face signs -/

/-- **The central low-ratio face** (`LOW_RATIO_CENTRAL_HAND_SIGN` (6); inventory HS-S01 D-R15): for
`1 < x ≤ 2`, `1 ≤ α`, `6α² ≤ x(x + 2)` (`q_c ≤ 1/7`), the strip
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `3/4 ≤ u ≤ u_ℓ(x, β)` and
every `τ ∈ [2, T]`, `T = r_A/q_c`: `Γ_*(q_c) - (7/96)R*_τ(q_c) > 9193/50000`. Status: heavy. -/
theorem hs1_central_face {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : 3 / 4 ≤ u)
    (hul : u ≤ hsUl x be) (hτ : 2 ≤ τ) (hτT : τ * hsQc x al ≤ hsRA al be) :
    9193 / 50000 < hsGs x al u (hsQc x al) - 7 / 96 * hsRs x be al u (hsQc x al) τ := by
  sorry

/-- **The outer low-ratio face** (`LOW_RATIO_OUTER_HAND_SIGN` §6; inventory HS-S01 D-R22): for
`1 < x ≤ 2`, `1 ≤ α ≤ x`, `x ≤ β ≤ αx`, `x(x + 2) ≤ 6α²` (`q_c ≥ 1/7`), the strip of
`hs1_central_face`, `u_f(x) ≤ u ≤ V̄(x)` with `u ≤ u_ℓ(x, β)` when `x ≥ 3/2` and `α ≤ 6/5`, and every
`τ ∈ [2, 7r_A]`: `Γ_*(1/7) - (7/96)R*_τ(1/7) > 9193/50000`. Status: heavy. -/
theorem hs1_outer_face {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hbx : be ≤ al * x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : hsUf x ≤ u)
    (huv : u ≤ hsVbar x) (hul : 3 / 2 ≤ x → al ≤ 6 / 5 → u ≤ hsUl x be) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    9193 / 50000 < hsGs x al u (1 / 7) - 7 / 96 * hsRs x be al u (1 / 7) τ := by
  sorry

/-! ### Gate S1 -/

namespace HsData

variable (H : HsData)

/-- **The corrected envelope cap** (`SHARP_LOW_RATIO_CORRECTED_CAP` (16), `CORRECTED_ENVELOPE_CAP`
(5)-(9); inventory HS-S01 C1-C4, C15): for actual data with `x ≤ 2`,
`Γ_actual ≥ Γ_*(q) - (7/96)R*_τ(q)` at the actual `q`, `τ`, shape and `u` (two-segment monotonicity
of `Γ - (7/96)R_τ`: the `v`-segment by concavity, the `t`-segment along `v = U(t)`, both from
`hs1_ratio` with `hs1_root_cap`, `hs_B_pos`; endpoint values `root_zero`, `hs_env_scale`).
Status: stable. -/
theorem hs1_cap_env (hx2 : H.x ≤ 2) :
    hsGs H.x H.al H.u H.q - 7 / 96 * hsRs H.x H.be H.al H.u H.q H.τ ≤ H.Γ := by
  sorry

/-- **Gate S1** (`LOWER_RATIO_HAND_EXCLUSION`; inventory HS-S01 M19, C20, C24): `x > 2`.
Proof plan: if `x ≤ 2`: `hs1_cap_env`; with `p = τq` (`q ≤ p/2`, `p < r_A`), raise `q` at fixed `p`
to `min{q_c, 1/7, p/2}` (`hs1_scale_dec`, `hs_phi_eq`; strip from `strong_order`,
`upper_order_98`), then at `τ = 2` to `min{q_c, 1/7}` (`hs1_tau2_dec`; `hs_V_le_U0`, `u_le_V`); on
the central face (`hs_qc_le_iff`) `hs1_central_face` with `u ≤ ū ≤ u_ℓ` (`hs_sec_le_ubar`,
`hs1_u_ell`; `x ≥ 23/14`, `α ≤ 1351/1170`), on the outer face `hs1_outer_face` with
`hs_sec_gt_floor`, `hs_V_le_Vbar`, `hs1_u_ell`; this gives `Γ > 9193/50000`, contradicting
`cas_lt`.
Status: assembly (to be proved from the leaves above). -/
theorem s1 : 2 < H.x := by
  sorry

end HsData

/-- **Gate S1 for the actual window**: `C/a > 2`. -/
theorem M2Short.hs_S1 (D : M2Short) : 2 < D.C / D.a := by
  have h := D.toHs.s1
  rwa [D.toHs_x] at h

end SmoothedOctagon
