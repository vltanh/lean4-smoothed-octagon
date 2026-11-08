module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic

/-!
# Hand proof of the smaller-short case: the opposite-turn envelope and the scale form

The comparison machinery shared by gates S0-S5: removing the opposite turn `(t, v)` from the outer
root residual (`MIXED_SMALLER_SHORT_OUTER_ENVELOPE` §§1-3, `FLOOR_WEIGHTED_ENVELOPE` §1,
`VARIABLE_FLOOR_REDUCTION` (3), `DISPLACEMENT_WEIGHT_REDUCTION` §2), and the reparametrization of
the upper envelope by the outer scale `q` (`ENVELOPE_SCALE_MONOTONICITY` (1)-(4)); inventories
HS-S01 A5-A6, A10, C1-C6; HS-S2 R9-R10; HS-S3 R10-R11; HS-S567 E.1-E.4.

## Main API

* `hs_B_pos`: the positive factor `B_τ(s) = 1 + τ(λs - d) > 0` (`OUTER_ENVELOPE` (4)).
* `hs_env_weighted`: for any floor weight `m` with `B_{τ+m} > 0` on `[t₀, t]`,
  `R_τ(t, v) + m(w(t, v) - 3/4) ≤ R_τ(t₀, U(t₀)) + m(w(t₀, U(t₀)) - 3/4)` (`OUTER_ENVELOPE` (1),
  (5)-(6); `FLOOR_WEIGHTED_ENVELOPE` (2)-(4)).
* `hs_scale_coords`, `hs_env_scale`: at `ρ = ρ(q)` and `t₀ = ρS` the envelope values are
  `w_* = hsWs`, `E_{L,*} = hsELs`, `R*_τ = hsRs`, `Γ_* = hsGs` (`ENVELOPE_SCALE_MONOTONICITY`
  (1)-(4)).
* `hs_q_le_qc_iff` (`q ≤ q_c ⟺ ρ ≤ r²`), `hs_qc_le_iff` (`q_c ≤ 1/7 ⟺ 6α² ≤ x(x + 2)`).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The positive factor** (`OUTER_ENVELOPE` (4); inventory HS-S01 C1, HS-S567 E.1): for
`1 ≤ α ≤ x ≤ β`, `x > 1`, `ρ > 0`, `s ≥ t₀ = ρ(1 + x)` and `0 ≤ τ ≤ T = r_A/q`,
`B_τ(s) = 1 + τ(λs - d) > 0` (minimum at `τ = T`: `Q + s/ρ - D ≥ x(β - 1) + β(x - α) > 0`).
Status: stable. -/
theorem hs_B_pos {x be al rho s τ : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hτ : 0 ≤ τ) (hτT : τ * hsQ al rho ≤ hsRA al be) :
    0 < 1 + τ * (hsLam al rho * s - hsLam al rho * rho * hsDg x be al) := by
  sorry

/-- **The weighted opposite-turn envelope** (`OUTER_ENVELOPE` (1), (5)-(6); `FLOOR_WEIGHTED_ENVELOPE`
(2)-(4); `DISPLACEMENT_WEIGHT_REDUCTION` (8)-(12)): with `G = R_τ + m(w - 3/4)`,
`∂_v G = (λ/t)B_{τ+m}(t)` and `d/dt G(t, U(t)) = λ(2t - 1)B_{τ+m}(t)/t`; so if `B_{τ+m} > 0` on
`[t₀, t]`, `t₀ = ρ(1 + x) ≤ t ≤ 1/(1 + x)`, and `v ≤ U(t)`, then `G(t, v) ≤ G(t₀, U(t₀))`.
Status: stable. -/
theorem hs_env_weighted {x be al rho u τ m t v : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hρ : 0 < rho)
    (ht0 : rho * (1 + x) ≤ t) (htr : t ≤ 1 / (1 + x)) (hv : v ≤ m2U t)
    (hB : ∀ s ∈ Icc (rho * (1 + x)) t,
      0 < 1 + (τ + m) * (hsLam al rho * s - hsLam al rho * rho * hsDg x be al)) :
    hsR x be al rho u τ t v + m * (hsW x be al rho u t v - 3 / 4) ≤
      hsR x be al rho u τ (rho * (1 + x)) (m2U (rho * (1 + x))) +
        m * (hsW x be al rho u (rho * (1 + x)) (m2U (rho * (1 + x))) - 3 / 4) := by
  sorry

/-- **The scale coordinates** (`ENVELOPE_SCALE_MONOTONICITY` §1): for `α ≥ 1`, `0 < ρ`,
`q = α²λρ` gives back `ρ = q/(α² - (α² - 1)q)`, `λ = 1 - εq` and `d = λρD = qΔ`
(`ε = 1 - α⁻²`, `Δ = D/α²`). Status: stable. -/
theorem hs_scale_coords {x be al rho : ℝ} (hal : 1 ≤ al) (hρ : 0 < rho) :
    hsRhoOf al (hsQ al rho) = rho ∧ hsLam al rho = 1 - (1 - 1 / al ^ 2) * hsQ al rho ∧
      hsLam al rho * rho * hsDg x be al = hsQ al rho * (hsDg x be al / al ^ 2) := by
  sorry

/-- **The upper envelope in the scale variable** (`OUTER_ENVELOPE` (3), (7);
`ENVELOPE_SCALE_MONOTONICITY` (2)-(4); `CORRECTED_CAP_SCALE` (8)): for `x > 0`, `α ≥ 1`,
`0 < q < 1`, with `ρ = ρ(q)` and `t₀ = ρ(1 + x)`: `w(t₀, U(t₀)) = 1 - qA₁ + q²A₂`,
`E_L(t₀, U(t₀)) = -E₀ + qA₃`, `R_τ(t₀, U(t₀)) = R*_τ(q)` and `Γ(t₀, U(t₀)) = Γ_*(q)`.
Status: stable. -/
theorem hs_env_scale {x be al u q τ : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hq : 0 < q) (hq1 : q < 1) :
    hsW x be al (hsRhoOf al q) u (hsRhoOf al q * (1 + x)) (m2U (hsRhoOf al q * (1 + x))) =
        hsWs x be al u q ∧
      hsEL x be al (hsRhoOf al q) u (hsRhoOf al q * (1 + x)) (m2U (hsRhoOf al q * (1 + x))) =
        hsELs x be al u q ∧
      hsR x be al (hsRhoOf al q) u τ (hsRhoOf al q * (1 + x)) (m2U (hsRhoOf al q * (1 + x))) =
        hsRs x be al u q τ ∧
      hsGam (hsRhoOf al q) u (m2U (hsRhoOf al q * (1 + x)))
          (hsE x (hsRhoOf al q) u (hsRhoOf al q * (1 + x)) (m2U (hsRhoOf al q * (1 + x)))) =
        hsGs x al u q := by
  sorry

/-- **The floor-weighted positive factor** (`FLOOR_WEIGHTED_ENVELOPE` (2)-(3), `VARIABLE_FLOOR_REDUCTION`
(3); inventory HS-S01 A6(b), HS-S2 R9): for `x > 5/3`, `1 ≤ α ≤ x ≤ β`, `ρ > 0`, `s ≥ ρ(1 + x)`,
`T = r_A/q ≥ 2` and `0 ≤ z ≤ T + 1/2`: `B_z(s) = 1 + z(λs - d) > 0`
(`4Q - 5(D - S) = β(10x - 6α) - α² - 5x ≥ x(3x - 5) > 0`). Status: stable. -/
theorem hs_B_pos_weighted {x be al rho s z : ℝ} (hx : 5 / 3 < x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hz : 0 ≤ z)
    (hT : 2 * hsQ al rho ≤ hsRA al be) (hzT : z * hsQ al rho ≤ hsRA al be + hsQ al rho / 2) :
    0 < 1 + z * (hsLam al rho * s - hsLam al rho * rho * hsDg x be al) := by
  sorry

/-- **`D < Q` and `D < 3α²`** (`VARIABLE_FLOOR_REDUCTION` (6)-(7), `DISPLACEMENT_WEIGHT_REDUCTION`
(5); inventory HS-S2 R13, R14, HS-S3 R9(e)): for `x ≥ 2`, `1 ≤ α ≤ x`,
`β ≥ b₀ = x(9x + 8α)/(9x + 8)`: `D < α(α + β)` and `D < 3α²`. Status: stable. -/
theorem hs_D_lt_Q {x be al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hb : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) :
    hsDg x be al < al * (al + be) ∧ hsDg x be al < 3 * al ^ 2 := by
  sorry

/-- **`A₂ > 0`** (`ROOT_FLOOR_SCALE` (6), (9); `VARIABLE_FLOOR_REDUCTION` (10)-(11);
`DISPLACEMENT_WEIGHT_REDUCTION` (16)-(18); `SMALL_SHAPE_ROOT_SHEAR` (9)-(10); inventories HS-S2 R16,
HS-S3 R13, HS-S4 R15, HS-S567 S5.3): for `2 ≤ x ≤ 12/5`, `α ≥ 1`, `3/4 ≤ u ≤ 31/40` and every `β`,
`A₂ > 0` (`A₂ ≥ 𝒜 - K̄²/3` and `K̄² - 3𝒜 < 0`). Status: stable. -/
theorem hs_A2_pos {x be al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 31 / 40) : 0 < hsA2 x be al u := by
  sorry

/-- **Convex endpoint alternative** (`VARIABLE_FLOOR_REDUCTION` (12), `DISPLACEMENT_WEIGHT_REDUCTION`
§4): if `m ≥ 0` and `A₂ ≥ 0`, the scale polynomial `Φ` is convex, so on `[0, q_m]`,
`Φ(q) ≤ max{Φ(0), Φ(q_m)}`. Status: stable. -/
theorem hs_phi_convex_max {x be al u p m qm q : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ hsA2 x be al u)
    (hq : 0 ≤ q) (hqq : q ≤ qm) :
    hsPhi x be al u p m q ≤ max (hsPhi x be al u p m 0) (hsPhi x be al u p m qm) := by
  sorry

/-- **The weighted envelope at fixed `p`** (`ENVELOPE_SCALE_MONOTONICITY` (4), `ROOT_FLOOR_SCALE`
(1)): for `p, q > 0`, `hsF x be al u q (p/q) (log(p/r_A)) m = Φ(q) = C(p) + m/4 + q(L(p) - mA₁) +
mq²A₂`. Status: stable. -/
theorem hs_phi_eq {x be al u p q m : ℝ} (hp : 0 < p) (hq : 0 < q) :
    hsF x be al u q (p / q) (log (p / hsRA al be)) m = hsPhi x be al u p m q := by
  sorry

/-- **Centre stationarity under the opposite-turn envelope** (`POSITIVE_DIAGONAL_PAIRING` (4),
`OUTER_ENVELOPE` (3)): for `x > 1`, `ρ > 0`, `ρ(1 + x) ≤ t ≤ 1/(1 + x)`, `v ≤ U(t)`:
`E(t, v) ≤ E_* = S(u - 1) + 1/S + ρ(2S - 1)` (`log(t/t₀) ≥ 2(t - t₀)` for `t ≤ 1/2`).
Status: stable. -/
theorem hs_E_le_env {x rho u t v : ℝ} (hx : 1 < x) (hρ : 0 < rho) (ht0 : rho * (1 + x) ≤ t)
    (htr : t ≤ 1 / (1 + x)) (hv : v ≤ m2U t) :
    hsE x rho u t v ≤ hsE0 x u + rho * (2 * (1 + x) - 1) := by
  sorry

/-- **The central cap in the scale variable** (`ENVELOPE_SCALE_MONOTONICITY` §3): for `α ≥ 1`,
`x > 0`, `0 < ρ`, `q = α²λρ ≤ q_c ⟺ ρ ≤ 1/(1 + x)²`. Status: stable. -/
theorem hs_q_le_qc_iff {x al rho : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hρ : 0 < rho) :
    hsQ al rho ≤ hsQc x al ↔ rho ≤ 1 / (1 + x) ^ 2 := by
  sorry

/-- The face condition (`LARGE_RATIO_HAND_EXCLUSION` (16), `LOWER_RATIO_HAND_EXCLUSION` (5)):
`q_c ≤ 1/7 ⟺ 6α² ≤ x(x + 2)` for `x > 0`. Status: stable. -/
theorem hs_qc_le_iff {x al : ℝ} (hx : 0 < x) : hsQc x al ≤ 1 / 7 ↔ 6 * al ^ 2 ≤ x * (x + 2) := by
  sorry

end SmoothedOctagon
