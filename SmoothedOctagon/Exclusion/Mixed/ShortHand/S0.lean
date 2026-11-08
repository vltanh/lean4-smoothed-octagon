module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S0: `x < 12/5`, `D > 0`, `E_L > 0`

`MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION` (1)-(2) and
`MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING` (2); inventory HS-S01 Parts M, A, B (M10-M18,
A1-A23, B1-B10). The large-ratio exclusion: assuming `x ≥ 12/5`, the actual root gives `G*_τ ≥ 0` for
the floor-weighted envelope `G = R_τ + ½(w - 3/4)` (`hs_env_weighted` with `m = 1/2`); the scale
moves (`hs0_endpoint_alt`, `hs0_G_zero_neg`, `hs0_tau_two`) push it to a face `q = q_c ≤ 1/7` or
`q = 1/7 ≤ q_c`; the norm substitution (`hs0_uslope`, `hs_sec_le_ubar`, `hs0_ubar_le_uhat`) and
the three duration tests (`hs_dur_three`) reduce to the face signs `hs0_central_tau_two`,
`hs0_central_duration`, `hs0_outer_tests` (heavy).

## Main API

* Shape leaves: `hs0_al_be` (`α/β < 3/4`), `hs0_DQ_le` (`D/Q ≤ 3(1 + x)²/(7x²)`),
  `hs0_face_alpha`, `hs0_ubar_le_uhat`, `hs0_D_pos`, `hs0_pairing`.
* Scale leaves: `hs0_uslope`, `hs0_endpoint_alt`, `hs0_G_zero_neg`, `hs0_tau_two`.
* Heavy face signs: `hs0_central_tau_two` (`CENTRAL_TAU_TWO_SIGN` (3)), `hs0_central_duration`
  (`CENTRAL_DURATION_FACES` (5)), `hs0_outer_tests` (`OUTER_SCALE_LARGE_RATIO_SIGN` (7)).
* Gate: `HsData.s0`, `M2Short.hs_S0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Shape leaves -/

/-- **`α/β < 3/4`** (`FLOOR_WEIGHTED_ENVELOPE` (5); inventory HS-S01 A7): for `x ≥ 12/5`,
`1 ≤ α < x ≤ β` with equal secants, `4α < 3β` (upper bound of `Sec(α, β, x)` by its value at `α`,
lower bound of `Sec(1, x, β)` by the tangent bound of `1/y²`). Status: stable. -/
theorem hs0_al_be {x al be : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al < x) (hxb : x ≤ be)
    (heq : m2Sec 1 x be = m2Sec al be x) : 4 * al < 3 * be := by
  sorry

/-- **The diagonal ratio** (`FLOOR_WEIGHTED_ENVELOPE` (9); inventory HS-S01 A8): for `x ≥ 12/5`,
`1 ≤ α ≤ x ≤ β`, `4α ≤ 3β`: `D ≤ (3(1 + x)²/(7x²))·α(α + β)`. Status: stable. -/
theorem hs0_DQ_le {x al be : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (h43 : 4 * al ≤ 3 * be) : hsDg x be al ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2) * (al * (al + be)) := by
  sorry

/-- **The face α-bounds** (`LARGE_RATIO_HAND_EXCLUSION` (16), (18); inventory HS-S01 A22, B3, B4):
for `x > 0`, `α ≥ 0`: `6α² ≤ x(x + 2) → α ≤ (5x + 4)/12`; and for `x ≥ 12/5`:
`x(x + 2) ≤ 6α² → (22x + 20)/55 ≤ α`. Status: stable. -/
theorem hs0_face_alpha {x al : ℝ} (hx : 0 < x) (hal : 0 ≤ al) :
    (6 * al ^ 2 ≤ x * (x + 2) → al ≤ (5 * x + 4) / 12) ∧
      (12 / 5 ≤ x → x * (x + 2) ≤ 6 * al ^ 2 → (22 * x + 20) / 55 ≤ al) := by
  sorry

/-- **`ū ≤ û` on the central face domain** (`CENTRAL_TAU_TWO_SIGN` §2 (6)-(7); inventory HS-S01 A4,
B5): for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, `x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`,
`ū(x, β) ≤ û(x, β)` (`P_t(x) > 0`). Status: stable. -/
theorem hs0_ubar_le_uhat {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsUbar x be ≤ hsUhat x be := by
  sorry

/-- **The positive diagonal** (`POSITIVE_DIAGONAL_PAIRING` (7)-(8); inventory HS-S01 M13, route
`D ≥ αD₀`): for `1 < x ≤ 12/5`, `1 ≤ α ≤ x ≤ β ≤ αx`, `D ≥ D₀ = 2 + 4x - 2x² ≥ 2/25`.
Status: stable. -/
theorem hs0_D_pos {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hb : be ≤ al * x) :
    2 + 4 * x - 2 * x ^ 2 ≤ hsDg x be al ∧ 2 / 25 ≤ hsDg x be al := by
  sorry

/-- **The positive pairing sign** (`POSITIVE_DIAGONAL_PAIRING` (9)-(11); inventory HS-S01 M14, affine
route in `ρ`): for `1 < x ≤ 12/5`, `0 ≤ ρ ≤ 1/(1 + x)²`, `D ≥ 2 + 4x - 2x²`, `3/4 ≤ u ≤ u₀(x)`:
`F₂ = E_* - 2ρDu = S(u - 1) + 1/S + ρ(2S - 1) - 2ρDu < 0`. Status: stable. -/
theorem hs0_pairing {x rho D u : ℝ} (hx : 1 < x) (hx2 : x ≤ 12 / 5) (hρ : 0 ≤ rho)
    (hρr : rho ≤ 1 / (1 + x) ^ 2) (hD : 2 + 4 * x - 2 * x ^ 2 ≤ D) (hu : 3 / 4 ≤ u)
    (hu0 : u ≤ hsU0 x) : hsE0 x u + rho * (2 * (1 + x) - 1) - 2 * rho * D * u < 0 := by
  sorry

/-! ### Scale leaves -/

/-- **The incoming coefficient** (`FLOOR_WEIGHTED_ENVELOPE` (10)-(11), `LARGE_RATIO_HAND_EXCLUSION`
(11); inventory HS-S01 A9, B6): for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`, `α < β`, `D < α(α + β)`,
`0 < q ≤ 1/7`, and either `2 ≤ τ ≤ T = r_A/q` or `τ = 2`, the floor-weighted face value is
nondecreasing in `u` (it is affine with slope `1/r_A + λS - 2d + (τ + ½)d(d - λS) > 0`).
Status: stable. -/
theorem hs0_uslope {x be al q τ ℓ u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hab : al < be) (hDQ : hsDg x be al < al * (al + be))
    (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hτ : (2 ≤ τ ∧ τ * q ≤ hsRA al be) ∨ τ = 2) (huu : u ≤ u') :
    hsF x be al u q τ ℓ (1 / 2) ≤ hsF x be al u' q τ ℓ (1 / 2) := by
  sorry

/-- **The endpoint alternative at fixed `p`** (`ROOT_FLOOR_SCALE` (3)-(23); inventory HS-S01
A12-A16): on `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`, `3/4 ≤ u ≤ 13/16`, `0 < p ≤ r_A`, `0 ≤ q_m ≤ p/2`,
the floor-weighted scale polynomial `𝒢(q) = Φ(q)` (`m = 1/2`) satisfies
`𝒢(q) ≤ max{𝒢(0), 𝒢(q_m)}` on `[0, q_m]` (convex if `A₂ ≥ 0`; increasing, slope `> 1/10`, if
`A₂ < 0`). Status: stable. -/
theorem hs0_endpoint_alt {x be al u p qm q : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) (hp : 0 < p)
    (hpr : p ≤ hsRA al be) (hqm : 0 ≤ qm) (hqmp : qm ≤ p / 2) (hq : 0 ≤ q) (hqq : q ≤ qm) :
    hsPhi x be al u p (1 / 2) q ≤
      max (hsPhi x be al u p (1 / 2) 0) (hsPhi x be al u p (1 / 2) qm) := by
  sorry

/-- **The zero-scale endpoint is negative** (`FLOOR_WEIGHTED_ENVELOPE` (12)-(18); inventory HS-S01
A17): for `x ≥ 12/5`, `1 ≤ α ≤ x ≤ β`, `r_A ≤ 3/7`, `D ≤ (3(1 + x)²/(7x²))·α(α + β)`,
`3/4 ≤ u ≤ 13/16`, `u ≤ V̄(x)` and `0 < p ≤ r_A`: `𝒢(0) = C(p) + 1/8 < 0`. Status: stable. -/
theorem hs0_G_zero_neg {x be al u p : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hrA : hsRA al be ≤ 3 / 7)
    (hDQ : hsDg x be al ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2) * (al * (al + be))) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 13 / 16) (huV : u ≤ hsVbar x) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    hsPhi x be al u p (1 / 2) 0 < 0 := by
  sorry

/-- **The `τ = 2` face can be pushed** (`ROOT_FLOOR_TAU_TWO_SCALE` (2)-(21); inventory HS-S01 A18,
A19): for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`, the *actual* `u = Sec(1, x, β) ≤ 13/16` (the uniform
floor `hs_sec_gt_floor` is essential), `G₂(q) = R*_2 + ½(w_* - 3/4)` is strictly increasing on
`(0, 1/7]`. Status: stable. -/
theorem hs0_tau_two {x be al u q₁ q₂ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hu : u = m2Sec 1 x be) (hu' : u ≤ 13 / 16) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    hsF x be al u q₁ 2 (log (2 * q₁ / hsRA al be)) (1 / 2) <
      hsF x be al u q₂ 2 (log (2 * q₂ / hsRA al be)) (1 / 2) := by
  sorry

/-! ### Heavy face signs -/

/-- **The central face, `τ = 2` test** (`CENTRAL_TAU_TWO_SIGN` (3); inventory HS-S01 B7): on
`Dom_c` (`12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, `x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`),
at `q = q_c`, `u = û(x, β)`, `T = r_A/q_c`: `F(2, 5/(2T) - 11/9) < 0` for the floor-weighted face
value. Status: heavy. -/
theorem hs0_central_tau_two {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUhat x be) (hsQc x al) 2
      (5 / (2 * (hsRA al be / hsQc x al)) - 11 / 9) (1 / 2) < 0 := by
  sorry

/-- **The central face, `τ = T` and `τ = 8T/9` tests** (`CENTRAL_DURATION_FACES` (5); inventory
HS-S01 B8): on `Dom_c`, at `q = q_c`, `u = û`, `T = r_A/q_c`: `F(T, 0) < 0` and
`F(8T/9, -1/9) < 0` (no condition `cT ≥ 2`). Status: heavy. -/
theorem hs0_central_duration {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUhat x be) (hsQc x al) (hsRA al be / hsQc x al) 0 (1 / 2) < 0 ∧
      hsF x be al (hsUhat x be) (hsQc x al) (8 * (hsRA al be / hsQc x al) / 9) (-1 / 9) (1 / 2) <
        0 := by
  sorry

/-- **The outer face, three tests** (`OUTER_SCALE_LARGE_RATIO_SIGN` (7); inventory HS-S01 B9): on
`Dom_o` (`12/5 ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ x`,
`x + 4x(α - 1)/(5x + 4) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`), at `q = 1/7`, `u = ū(x, β)`,
`T = 7r_A`: `F(T, 0) < 0`, `F(8T/9, -1/9) < 0`, `F(2, 5/(2T) - 11/9) < 0`. Status: heavy. -/
theorem hs0_outer_tests {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ al) (hax : al ≤ x)
    (hb : x + 4 * x * (al - 1) / (5 * x + 4) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUbar x be) (1 / 7) (7 * hsRA al be) 0 (1 / 2) < 0 ∧
      hsF x be al (hsUbar x be) (1 / 7) (8 * (7 * hsRA al be) / 9) (-1 / 9) (1 / 2) < 0 ∧
      hsF x be al (hsUbar x be) (1 / 7) 2 (5 / (2 * (7 * hsRA al be)) - 11 / 9) (1 / 2) < 0 := by
  sorry

/-! ### Gate S0 -/

namespace HsData

variable (H : HsData)

/-- **Gate S0** (`LARGE_RATIO_HAND_EXCLUSION` (1)-(2), `POSITIVE_DIAGONAL_PAIRING` (2); inventory
HS-S01 M18): `x < 12/5`, `D > 0`, `E_L > 0`.
Proof plan: if `x ≥ 12/5`: `root_zero`, `w_ge` and `hs_env_weighted` (`m = 1/2`, factor positivity
`hs_B_pos_weighted`) give `0 ≤ G*_τ(q)`; `hs0_al_be`, `hs0_DQ_le` give `r_A < 3/7`, `D/Q < 1`; `hs_phi_eq`,
`q_le_qc`, `q_lt_seventh`, `hs0_endpoint_alt`, `hs0_G_zero_neg` (with `u_le_V`, `hs_V_le_Vbar`),
`hs0_tau_two` move to a face; `hs0_uslope` with `hs_sec_le_ubar`, `hs0_ubar_le_uhat`; `hs_dur_three`;
`hs0_face_alpha`, `strong_order`, `upper_order_54` place the shape in `Dom_c`/`Dom_o`; contradiction
with `hs0_central_tau_two`, `hs0_central_duration`, `hs0_outer_tests`. Then `hs0_D_pos` (with
`be_le_al_x`) and `EL_eq`, `hs_E_le_env`, `hs0_pairing` (with `hs_V_le_U0`, `u_le_V`) give
`D > 0`, `E_L = λ(2ρDu - E) > 0`.
Status: assembly (to be proved from the leaves above). -/
theorem s0 : H.x < 12 / 5 ∧ 0 < hsDg H.x H.be H.al ∧ 0 < H.EL := by
  sorry

end HsData

/-- **Gate S0 for the actual window**: `C/a < 12/5`, `D > 0`, `E_L > 0`. -/
theorem M2Short.hs_S0 (D : M2Short) :
    D.C / D.a < 12 / 5 ∧ 0 < hsDg (D.C / D.a) (D.B / D.a) (D.A / D.a) ∧ 0 < D.EL := by
  have h := D.toHs.s0
  rw [D.toHs_x, D.toHs_be, D.toHs_al, D.toHs_EL] at h
  exact h

end SmoothedOctagon
