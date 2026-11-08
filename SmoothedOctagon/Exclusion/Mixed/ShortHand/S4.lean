module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S4: `α ≤ 1 + 3δ` and `Γ > 1829/10000`

`MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER` (U) and `MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR`
(F) with `SMALL_SHAPE_CASIMIR_FLOOR` §§1-3, `EXTENDED_CASIMIR_DERIVATIVES`; inventory HS-S4
(R1-R23). On `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`: (U) is `hs_small_upper_order`; for (F), the corrected
envelope cap with constant `1/7` (`HsData.hs4_cap_env`), the scale moves (`hs4_scale_dec_p`,
`hs4_tau2_dec`) to the central scale `q_c`, the duration maximum (`hs_dur_max`), the norm
substitution `u ↦ ū` (`hs4_u_dec`) and the central-scale floor `min{Φ, Ψ}(ū) > 1829/10000`
(`hs4_floor_box`, heavy).

## Main API

* `hs4Phi`, `hs4Psi`: `Φ = Γ_*(q_c) - R*_2(q_c)/7`, `Ψ = Φ - (T - 2)(w_*(q_c) - 3/4)/7`
  (`SMALL_SHAPE_CASIMIR_FLOOR` (10)-(11)).
* Stable: `HsData.hs4_cap_env`, `hs4_scale_dec_p`, `hs4_tau2_dec`, `hs4_u_dec`, `hs4_ubar_box`.
* Heavy: `hs4_floor_box` (`EXTENDED_CASIMIR_DERIVATIVES` (4)-(31), `EXTENDED_CASIMIR_FLOOR` (10)).
* Gate: `HsData.s4`, `M2Short.hs_S4`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `Φ = Γ_*(q_c) - R*_2(q_c)/7` (`SMALL_SHAPE_CASIMIR_FLOOR` (10)). -/
noncomputable def hs4Phi (x be al u : ℝ) : ℝ :=
  hsGs x al u (hsQc x al) - hsRs x be al u (hsQc x al) 2 / 7

/-- `Ψ = Φ - (T - 2)(w_*(q_c) - 3/4)/7`, `T = r_A/q_c` (`SMALL_SHAPE_CASIMIR_FLOOR` (11)). -/
noncomputable def hs4Psi (x be al u : ℝ) : ℝ :=
  hs4Phi x be al u - (hsRA al be / hsQc x al - 2) * (hsWs x be al u (hsQc x al) - 3 / 4) / 7

/-- **The fixed-`p` scale move** (`ENVELOPE_SCALE_MONOTONICITY` (5)-(10), `CORRECTED_CAP_SCALE` (1),
(8)-(10); inventory HS-S4 R13, R14, R17(a)): for `x > 1`, `1 ≤ α < x ≤ β`, `0 < p ≤ r_A`,
`3/4 ≤ u ≤ min{U(1/(1 + x)), U(r_A)}`, `q ↦ Γ_*(q) - (C(p) + qL(p))/7` is strictly decreasing on
`(0, 1/6]` (`L > 0`, `∂_q Γ_* < (27/200)L`). Status: stable. -/
theorem hs4_scale_dec_p {x be al u p q₁ q₂ : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al < x)
    (hxb : x ≤ be) (hp : 0 < p) (hpr : p ≤ hsRA al be) (hu : 3 / 4 ≤ u)
    (hur : u ≤ m2U (1 / (1 + x))) (hurA : u ≤ m2U (hsRA al be)) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 6) :
    hsGs x al u q₂ - hsPhi x be al u p 0 q₂ / 7 < hsGs x al u q₁ - hsPhi x be al u p 0 q₁ / 7 := by
  sorry

/-- **The `τ = 2` scale move** (`ROOT_FLOOR_SCALE` (6), (9); `EXTENDED_CASIMIR_FLOOR` §1 (4)-(5);
inventory HS-S4 R15-R17(b)): on `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`,
`3/4 ≤ u ≤ 31/40`, `u ≤ U(1/(1 + x))`: `q ↦ Γ_*(q) - R*_2(q)/7` is strictly decreasing on `(0, 1/6]`
(`(R*_2)' > 1`, `(Γ_*)_q < 11/100`). Status: stable. -/
theorem hs4_tau2_dec {x δ al u q₁ q₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 31 / 40) (hur : u ≤ m2U (1 / (1 + x))) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 6) :
    hsGs x al u q₂ - hsRs x (x * (1 + δ)) al u q₂ 2 / 7 <
      hsGs x al u q₁ - hsRs x (x * (1 + δ)) al u q₁ 2 / 7 := by
  sorry

/-- **`Φ`, `Ψ` decrease in `u`** (`SMALL_SHAPE_CASIMIR_FLOOR` §3, `EXTENDED_CASIMIR_FLOOR` §2;
inventory HS-S4 R19): on the box of `hs4_tau2_dec`, for `3/4 ≤ u ≤ u' ≤ 31/40`:
`Φ(u') ≤ Φ(u)` and `Ψ(u') ≤ Ψ(u)`. Status: stable. -/
theorem hs4_u_dec {x δ al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : 3 / 4 ≤ u) (huu : u ≤ u')
    (hu' : u' ≤ 31 / 40) :
    hs4Phi x (x * (1 + δ)) al u' ≤ hs4Phi x (x * (1 + δ)) al u ∧
      hs4Psi x (x * (1 + δ)) al u' ≤ hs4Psi x (x * (1 + δ)) al u := by
  sorry

/-- **The incoming majorant on the box** (`INCOMING_NORM_BOUND` (2); inventory HS-S4 R9): for
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`: `ū(x, x(1 + δ)) < 31/40`. Status: stable. -/
theorem hs4_ubar_box {x δ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19) :
    hsUbar x (x * (1 + δ)) < 31 / 40 := by
  sorry

/-- **The extended original-Casimir floor at the central scale** (`EXTENDED_CASIMIR_DERIVATIVES`
(4)-(31), `EXTENDED_CASIMIR_FLOOR` (9)-(10); inventory HS-S4 R20-R22): on the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`, with `u = ū(x, β)`:
`Φ > 1829/10000` and `Ψ > 1829/10000`. Status: heavy. -/
theorem hs4_floor_box {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1829 / 10000 < hs4Phi x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) ∧
      1829 / 10000 < hs4Psi x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) := by
  sorry

/-! ### Gate S4 -/

namespace HsData

variable (H : HsData)

/-- **The corrected envelope cap with constant `1/7`** (`CORRECTED_ENVELOPE_CAP` (4)-(9); inventory
HS-S4 R10-R12): for actual data, `Γ_actual ≥ Γ_*(q) - R*_τ(q)/7` at the actual `q`, `τ`, shape and
`u` (ratio `(2ub + E_L)/(8(1 - q)²(1 + τb)) < u/(4τ(1 - q)²) < 1/7` from `E_L ≤ 3q`, `u ≤ 13/16`,
`q < 3/20`; two-segment monotonicity as in `hs1_cap_env`). Status: stable. -/
theorem hs4_cap_env : hsGs H.x H.al H.u H.q - hsRs H.x H.be H.al H.u H.q H.τ / 7 ≤ H.Γ := by
  sorry

/-- **Gate S4** (`SMALL_SHAPE_UPPER_ORDER` (1), `EXTENDED_CASIMIR_FLOOR` (2); inventory HS-S4 R7, R23):
on `2 ≤ x ≤ 13/6`, `δ ≤ 1/19`: `α ≤ 1 + 3δ` and `Γ > 1829/10000`.
Proof plan: (U) `hs_small_upper_order`; (F) `strong_box` and (U) give the box; `hs4_cap_env`;
`p = τq`, `q ≤ q_c` (`q_le_qc`), `q ≤ p/2`; `hs4_scale_dec_p` (`hs_phi_eq`) to `min{q_c, p/2}`, then
`hs4_tau2_dec` to `q_c` (`hsQc ≤ 1/6`); `hs_dur_max` at `q_c` gives `Γ ≥ min{Φ, Ψ}(u)`;
`hs4_u_dec` with `hs_sec_le_ubar`, `hs4_ubar_box`; `hs4_floor_box`.
Status: assembly (to be proved from the leaves above). -/
theorem s4 (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) (h3 : H.δ ≤ 1 / 19) :
    H.al ≤ 1 + 3 * H.δ ∧ 1829 / 10000 < H.Γ := by
  sorry

end HsData

/-- **Gate S4 for the actual window**: given `2 ≤ C/a ≤ 13/6` and `B/C - 1 ≤ 1/19`,
`A/a ≤ 1 + 3(B/C - 1)` and `Γ > 1829/10000`. -/
theorem M2Short.hs_S4 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : D.B / D.C - 1 ≤ 1 / 19) :
    D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1) ∧ 1829 / 10000 < D.Γ := by
  have h := D.toHs.s4 (by rwa [D.toHs_x]) (by rwa [D.toHs_x]) (by rwa [D.toHs_δ])
  rwa [D.toHs_al, D.toHs_δ, D.toHs_Γ] at h

end SmoothedOctagon
