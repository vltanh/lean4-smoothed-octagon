module

public import SmoothedOctagon.Exclusion.Mixed.Short.Calc
public import SmoothedOctagon.Exclusion.Mixed.Short.Order
public import SmoothedOctagon.Exclusion.Mixed.Short.Point

/-!
# Hand proof of the smaller-short case (gate H-S): shared scalar functions

Statement skeleton for the hand proof of `M2Short → False`
(`MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION`, `HAND_ONLY_COMPLETION_PLAN` gates S0-S7; inventories
`notes/inventory/HS-S01.md`, `HS-S2.md`, `HS-S3.md`, `HS-S4.md`, `HS-S567.md`). Everything here is
a function of plain real numbers, normalized by the central margin `a`:
`x = C/a`, `be = β = B/a`, `al = α = A/a`, `rho = ρ = a²/(a² + 4)`, `t = a/(a + b)`, `S = 1 + x`,
`r = 1/S`.

## Main API

* Transport data (`MIXED_SMALLER_SHORT_OUTER_ENVELOPE` §1, `SIX_VARIABLE_REDUCTION` (11)):
  `hsLam` (`λ`), `hsDg` (the bridge diagonal `D`), `hsQ` (the outer scale `q = ρ_A = α²λρ`),
  `hsRA` (`r_A`), `hsQc` (the central scale `q_c`), `hsRhoOf` (`ρ` as a function of `q`).
* The opposite-turn functions `hsE`, `hsW`, `hsEL` (`E(t, v)`, `w(t, v)`, `E_L(t, v)`), the outer
  root residual `hsR` (`R_τ(t, v)`) and the Casimir `hsGam`.
* The scale form (`ENVELOPE_SCALE_MONOTONICITY` (1)-(4)): `hsE0`, `hsA1`, `hsA2`, `hsA3`, the
  envelope values `hsWs` (`w_*`), `hsELs` (`E_{L,*}`), `hsGs` (`Γ_*`), and the weighted face value
  `hsF x be al u q τ ℓ m = (w_* - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ + m(w_* - 3/4)`
  (every face test of S0-S5 is a value of `hsF`); `hsRs` (`R*_τ` at scale `q`).
* Incoming-norm majorants and floors (`INCOMING_NORM_BOUND`, `UNIFORM_INCOMING_FLOOR`,
  `GAUSS_INCOMING_CEILING`, `CENTRAL_TAU_TWO_SIGN` (2), `LOW_RATIO_CENTRAL_HAND_SIGN` (16)):
  `hsVbar`, `hsUbar`, `hsUhat`, `hsUf`, `hsUl`, `hsU0`, `hsVG`; the strong-order slope `hsKs`.
* Generic leaves: the quintic `artanh` log bound `hs_log_ge_quintic`, `hs_log_le_cubic_le_one`,
  the tangent `hs_log_le_tangent`, the duration reductions `hs_dur_max`, `hs_dur_three`, the
  first-contact lemma `hs_first_contact`, the secant bounds `hs_u_le_V`, `hs_V_le_Vbar`,
  `hs_V_lt_VG`, `hs_V_le_U0`, `hs_sec_tail_le`, `hs_sec_le_ubar`, `hs_sec_gt_floor`, and the
  reverse-centre scale bound `hs_rev_centre_scale` (`HAND_PROOF_REFINEMENTS` §2).

Leaves carry a tag `Status: stable` (light) or `Status: heavy` (a large polynomial certificate in
the notes, stated at the level its caller needs, to be re-proved by a lighter argument).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Transport data -/

/-- `λ = 1/(1 + ρ(α² - 1)) = (a² + 4)/(A² + 4)` (`OUTER_ENVELOPE` §1). -/
noncomputable def hsLam (al rho : ℝ) : ℝ := 1 / (1 + rho * (al ^ 2 - 1))

/-- The bridge diagonal `D = α² + 2αβ + 1 + 2x - 2βx` (`OUTER_ENVELOPE` §1). -/
noncomputable def hsDg (x be al : ℝ) : ℝ := al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x

/-- The outer scale `q = ρ_A = α²λρ = A²/(A² + 4)` (`OUTER_ENVELOPE` §1). -/
noncomputable def hsQ (al rho : ℝ) : ℝ := al ^ 2 * hsLam al rho * rho

/-- `r_A = α/(α + β) = A/(A + B)`. -/
noncomputable def hsRA (al be : ℝ) : ℝ := al / (al + be)

/-- The central scale `q_c = α²/(x(x + 2) + α²)`, the value of `q` at `ρ = r²`
(`ENVELOPE_SCALE_MONOTONICITY` §3). -/
noncomputable def hsQc (x al : ℝ) : ℝ := al ^ 2 / (x * (x + 2) + al ^ 2)

/-- `ρ` as a function of the outer scale: `ρ = q/(α² - (α² - 1)q)` (`ENVELOPE_SCALE_MONOTONICITY`
§1). -/
noncomputable def hsRhoOf (al q : ℝ) : ℝ := q / (al ^ 2 - (al ^ 2 - 1) * q)

/-! ### The opposite-turn functions and the outer root residual -/

/-- Centre stationarity at `a` as a function of the opposite turn `(t, v)` (`OUTER_ENVELOPE` §1):
`E(t, v) = (u - 1)/r + (v - 1)/t + 1 + r + t - ρ + log(ρ/(rt))`, `r = 1/(1 + x)`. -/
noncomputable def hsE (x rho u t v : ℝ) : ℝ :=
  (u - 1) * (1 + x) + (v - 1) / t + 1 + 1 / (1 + x) + t - rho + log (rho * (1 + x) / t)

/-- The transported outer norm `w(t, v) = λ²v + d²u - dλE(t, v)`, `d = λρD`
(`SIX_VARIABLE_REDUCTION` (11)). -/
noncomputable def hsW (x be al rho u t v : ℝ) : ℝ :=
  hsLam al rho ^ 2 * v + (hsLam al rho * rho * hsDg x be al) ^ 2 * u -
    hsLam al rho * rho * hsDg x be al * hsLam al rho * hsE x rho u t v

/-- The transported outer pairing `E_L(t, v) = 2du - λE(t, v)` (`SIX_VARIABLE_REDUCTION` (11)). -/
noncomputable def hsEL (x be al rho u t v : ℝ) : ℝ :=
  2 * (hsLam al rho * rho * hsDg x be al) * u - hsLam al rho * hsE x rho u t v

/-- **The outer root residual** (`OUTER_ENVELOPE` §1, `CORRECTED_ENVELOPE_CAP` (2)):
`R_τ(t, v) = (w - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_L + log(τq/r_A)` with `w`, `E_L`
transported from `(t, v)`; the actual outer switch is `R_τ = 0` at `τ = (A + P_f)/A`. -/
noncomputable def hsR (x be al rho u τ t v : ℝ) : ℝ :=
  (hsW x be al rho u t v - 1) * τ + 1 / τ + (u - 1) / hsRA al be + hsRA al be + 1 - hsQ al rho -
    hsEL x be al rho u t v + log (τ * hsQ al rho / hsRA al be)

/-- The squared Casimir `Γ = (4uv - E²)/(16(1 - ρ)²)`. -/
noncomputable def hsGam (rho u v E : ℝ) : ℝ := (4 * u * v - E ^ 2) / (16 * (1 - rho) ^ 2)

/-! ### The scale form of the upper envelope (`ENVELOPE_SCALE_MONOTONICITY` (1)-(4)) -/

/-- `E₀ = S(u - 1) + 1/S`. -/
noncomputable def hsE0 (x u : ℝ) : ℝ := (1 + x) * (u - 1) + 1 / (1 + x)

/-- `A₁ = 2ε + n + ΔE₀` with `ε = 1 - α⁻²`, `n = S/α²`, `Δ = D/α²` (`ENVELOPE_SCALE_MONOTONICITY`
(1)). -/
noncomputable def hsA1 (x be al u : ℝ) : ℝ :=
  2 * (1 - 1 / al ^ 2) + (1 + x) / al ^ 2 + hsDg x be al / al ^ 2 * hsE0 x u

/-- `A₂ = ε² + εn + n² + Δ²u + ΔεE₀ - Δ(2S - 1)/α²` (`ENVELOPE_SCALE_MONOTONICITY` (1)). -/
noncomputable def hsA2 (x be al u : ℝ) : ℝ :=
  (1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1 + x) / al ^ 2) + ((1 + x) / al ^ 2) ^ 2 +
    (hsDg x be al / al ^ 2) ^ 2 * u + hsDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * hsE0 x u -
    hsDg x be al / al ^ 2 * (2 * (1 + x) - 1) / al ^ 2

/-- `A₃ = 2Δu + εE₀ - (2S - 1)/α²` (`ENVELOPE_SCALE_MONOTONICITY` (1)). -/
noncomputable def hsA3 (x be al u : ℝ) : ℝ :=
  2 * (hsDg x be al / al ^ 2) * u + (1 - 1 / al ^ 2) * hsE0 x u - (2 * (1 + x) - 1) / al ^ 2

/-- The upper-envelope outer norm at scale `q`: `w_* = 1 - qA₁ + q²A₂`. -/
noncomputable def hsWs (x be al u q : ℝ) : ℝ := 1 - q * hsA1 x be al u + q ^ 2 * hsA2 x be al u

/-- The upper-envelope outer pairing at scale `q`: `E_{L,*} = -E₀ + qA₃`. -/
noncomputable def hsELs (x be al u q : ℝ) : ℝ := -hsE0 x u + q * hsA3 x be al u

/-- **The weighted face value** at scale `q`, duration `τ`, log value `ℓ` and floor weight `m`:
`(w_* - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ + m(w_* - 3/4)`. With
`ℓ = log(τq/r_A)` it is the weighted upper envelope `R*_τ + m(w_* - 3/4)` (`OUTER_ENVELOPE` (7),
`FLOOR_WEIGHTED_ENVELOPE` (4), `VARIABLE_FLOOR_REDUCTION` (2), `DISPLACEMENT_WEIGHT_REDUCTION` (7)); with
`ℓ` a rational log majorant it is a face test (`OUTER_SCALE_LARGE_RATIO_SIGN` (6)). -/
noncomputable def hsF (x be al u q τ ℓ m : ℝ) : ℝ :=
  (hsWs x be al u q - 1) * τ + 1 / τ + (u - 1) / hsRA al be + hsRA al be + 1 - q -
    hsELs x be al u q + ℓ + m * (hsWs x be al u q - 3 / 4)

/-- `R*_τ` at scale `q` (`OUTER_ENVELOPE` (7)). With `p = τq` this is
`𝓡(u; p, q) = C(p) + qL(p)` (`ENVELOPE_SCALE_MONOTONICITY` (4)). -/
noncomputable def hsRs (x be al u q τ : ℝ) : ℝ :=
  hsF x be al u q τ (log (τ * q / hsRA al be)) 0

/-- The upper-envelope Casimir at scale `q`: `Γ_* = (4uU(t₀) - E_*²)/(16(1 - ρ)²)` with
`ρ = ρ(q)`, `t₀ = ρS`, `E_* = E₀ + ρ(2S - 1)` (`CORRECTED_ENVELOPE_CAP` §1,
`CORRECTED_CAP_SCALE` (8)). -/
noncomputable def hsGs (x al u q : ℝ) : ℝ :=
  (4 * u * m2U (hsRhoOf al q * (1 + x)) -
      (hsE0 x u + hsRhoOf al q * (2 * (1 + x) - 1)) ^ 2) / (16 * (1 - hsRhoOf al q) ^ 2)

/-- `C(p) = E₀ + (u - 1)/r_A + r_A + 1 - pA₁ + log(p/r_A)` (`ENVELOPE_SCALE_MONOTONICITY` (4)). -/
noncomputable def hsCp (x be al u p : ℝ) : ℝ :=
  hsE0 x u + (u - 1) / hsRA al be + hsRA al be + 1 - p * hsA1 x be al u + log (p / hsRA al be)

/-- `L(p) = pA₂ + 1/p - 1 - A₃` (`ENVELOPE_SCALE_MONOTONICITY` (4)). -/
noncomputable def hsLp (x be al u p : ℝ) : ℝ := p * hsA2 x be al u + 1 / p - 1 - hsA3 x be al u

/-- **The weighted envelope at fixed normalized duration `p = τq`** as a polynomial in the scale:
`Φ(q) = C(p) + m/4 + q(L(p) - mA₁) + mq²A₂` (`ROOT_FLOOR_SCALE` (1), `VARIABLE_FLOOR_REDUCTION`
(10), `DISPLACEMENT_WEIGHT_REDUCTION` (16)); with `m = 0` it is `𝓡(u; p, q) = C(p) + qL(p)`
(`ENVELOPE_SCALE_MONOTONICITY` (4), `SMALL_SHAPE_ROOT_SHEAR` (7)). For `q > 0` it equals
`hsF x be al u q (p/q) (log(p/r_A)) m` (`hs_phi_eq`). -/
noncomputable def hsPhi (x be al u p m q : ℝ) : ℝ :=
  hsCp x be al u p + m / 4 + q * (hsLp x be al u p - m * hsA1 x be al u) +
    m * q ^ 2 * hsA2 x be al u

/-! ### Angle coordinates and the physical shear (`SHEAR_COST_REDUCTION`) -/

/-- `R = (x - 1)/(x + 1)`. -/
noncomputable def hsRr (x : ℝ) : ℝ := (x - 1) / (x + 1)

/-- The angle coordinate `T_s = (β - α)/(β + α)` (distinct from the duration endpoint `T`). -/
noncomputable def hsTs (al be : ℝ) : ℝ := (be - al) / (be + al)

/-- The anisotropy `A = U₁/U₂ - 1 = (βx - α)(αx - β)/(S²(α² + αβ + β²))` (`SHEAR_COST_REDUCTION`
(4)). -/
noncomputable def hsAn (x be al : ℝ) : ℝ :=
  (be * x - al) * (al * x - be) / ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2))

/-- **The physical shear** (`SHEAR_COST_REDUCTION` (6)):
`h = (√3/3)(βx - α)((x + 2)α + (2x + 1)β)/(S²K_A) - (2√3/3)U₁Q₀ ρ/(1 - ρ)`, `K_A = α² + αβ + β²`,
`U₁ = (x² + x + 1)/S²`, `Q₀ = 2βx - x - αβ` (in the margins, inventory HS-S567 §0.1). -/
noncomputable def hsShear (x be al rho : ℝ) : ℝ :=
  √3 / 3 * ((be * x - al) * ((x + 2) * al + (2 * x + 1) * be) /
      ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2)) -
    2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) * (2 * be * x - x - al * be) * (rho / (1 - rho)))

/-! ### Incoming-norm majorants and floors -/

/-- `u_v = V̄(x) = 3/4 + 2(x - 1)²/((x + 1)(35x + 13))` (`INCOMING_NORM_BOUND` (3)). -/
noncomputable def hsVbar (x : ℝ) : ℝ := 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13))

/-- `ū(x, β) = 3/4 + [2(x - 1)³/((x + 1)(35x + 13)) + (β - x)³/(48x²)]/(β - 1)`
(`INCOMING_NORM_BOUND` (2)). -/
noncomputable def hsUbar (x be : ℝ) : ℝ :=
  3 / 4 + (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (be - x) ^ 3 / (48 * x ^ 2)) / (be - 1)

/-- `û(x, β) = 3/4 + V_g(x - 1 + (β - x)/8)/(β - 1)`, `V_g = 2(x - 1)²/((x + 1)(35x + 13))`
(`CENTRAL_TAU_TWO_SIGN` (2)). -/
noncomputable def hsUhat (x be : ℝ) : ℝ :=
  3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + (be - x) / 8) / (be - 1)

/-- The uniform incoming floor `u_f = 3/4 + (x - 1)²/(28(x + 1)²)` (`UNIFORM_INCOMING_FLOOR`
(1)). -/
noncomputable def hsUf (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (28 * (x + 1) ^ 2)

/-- The β-dependent ceiling `u_ℓ = 3/4 + (x - 1)²(β + 15x - 16)/(8S(35x + 13)(β - 1))`
(`LOW_RATIO_CENTRAL_HAND_SIGN` (16)). -/
noncomputable def hsUl (x be : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (be + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (be - 1))

/-- `u₀ = 3/4 + (x - 1)²/(12(x + 1)²)` (`MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING` (5)). -/
noncomputable def hsU0 (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (12 * (x + 1) ^ 2)

/-- The Gauss ceiling of `V`: `V_G = 3/4 + (x - 1)²(71x² + 48x + 1)/(96x(x + 1)(13x² + 14x + 3))`
(`GAUSS_INCOMING_CEILING` (1) at `β = x`). -/
noncomputable def hsVG (x : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (71 * x ^ 2 + 48 * x + 1) / (96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3))

/-- The strong lower-order slope `k_s(x) = 4(x + 1)/(7x + 1)` (`STRONG_ORDER` (1)). -/
noncomputable def hsKs (x : ℝ) : ℝ := 4 * (x + 1) / (7 * x + 1)

/-! ### Logarithm bounds -/

/-- Three terms of `log z = 2 artanh w`, `w = (z - 1)/(z + 1)`: `2(w + w³/3 + w⁵/5) ≤ log z` for
`z ≥ 1` (`EXTENDED_CASIMIR_FLOOR` (10); derivative of the difference `(z - 1)⁶/(z(z + 1)⁶)`).
Status: stable. -/
theorem hs_log_ge_quintic {z : ℝ} (hz : 1 ≤ z) :
    2 * ((z - 1) / (z + 1) + ((z - 1) / (z + 1)) ^ 3 / 3 + ((z - 1) / (z + 1)) ^ 5 / 5) ≤
      log z := by
  sorry

/-- For `0 < y ≤ 1`, `log y ≤ 2z + (2/3)z³`, `z = (y - 1)/(y + 1)` (`LOWER_RATIO_HAND_EXCLUSION` (7),
`LOW_RATIO_CENTRAL_HAND_SIGN` (24); `ss_log_ge_cubic` at `1/y`). Status: stable. -/
theorem hs_log_le_cubic_le_one {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ 2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3 := by
  sorry

/-- The tangent at `4/5`: `log y ≤ 5y/4 - 11/9` for `y > 0` (`LARGE_RATIO_HAND_EXCLUSION` (14);
`log(5/4) ≥ 2/9`). Status: stable. -/
theorem hs_log_le_tangent {y : ℝ} (hy : 0 < y) : log y ≤ 5 * y / 4 - 11 / 9 := by
  sorry

/-! ### Duration reductions -/

/-- **The duration maximum** (`LOWER_RATIO_HAND_EXCLUSION` (6), `LOW_RATIO_CENTRAL_HAND_SIGN` (7),
`DISPLACEMENT_WEIGHT_REDUCTION` (19)-(21)): for `2 ≤ τ ≤ T`,
`(w - 1)τ + 1/τ + log(τ/T) ≤ max{R₂, R₂ + (T - 2)(w - 3/4)}`, `R₂ = 2w - 3/2 + log(2/T)` (exact
remainder `log(τ/2) - τ/4 + 1/τ ≤ 0`, `ss_log_le_half`). Status: stable. -/
theorem hs_dur_max {w T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    (w - 1) * τ + 1 / τ + log (τ / T) ≤
      max (2 * w - 3 / 2 + log (2 / T)) (2 * w - 3 / 2 + log (2 / T) + (T - 2) * (w - 3 / 4)) := by
  sorry

/-- **The three duration tests** (`LARGE_RATIO_HAND_EXCLUSION` (15), `OUTER_SCALE_LARGE_RATIO_SIGN`
§2): with `F(τ, ℓ) = c₁τ + 1/τ + c₀ + ℓ` and `2 ≤ τ ≤ T`, `F(τ, log(τ/T)) ≤ max{F(2, 5/(2T) - 11/9),
F(8T/9, -1/9), F(T, 0)}` (the two log tangents of `hs_log_le_tangent` and convexity of `1/τ`).
Status: stable. -/
theorem hs_dur_three {c₁ c₀ T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    c₁ * τ + 1 / τ + c₀ + log (τ / T) ≤
      max (c₁ * 2 + 1 / 2 + c₀ + (5 / (2 * T) - 11 / 9))
        (max (c₁ * (8 * T / 9) + 9 / (8 * T) + c₀ - 1 / 9) (c₁ * T + 1 / T + c₀)) := by
  sorry

/-! ### The first-contact lemma -/

/-- **First contact** (`STRONG_ORDER` §5, `GLOBAL_UPPER_ORDER` §5, `SMALL_SHAPE_UPPER_ORDER` §4, in
the barrier form of inventory HS-S4 §5): if `Φ` is continuous on `[a, 1]`, `Φ(1) = 0`, and at every
zero `z ∈ (a, 1]` of `Φ` it has a negative derivative, then `Φ > 0` on `(a, 1)`.
Status: stable. -/
theorem hs_first_contact {Φ : ℝ → ℝ} {a : ℝ} (ha : a < 1) (hc : ContinuousOn Φ (Icc a 1))
    (h1 : Φ 1 = 0)
    (hd : ∀ z ∈ Ioc a 1, Φ z = 0 → ∃ d : ℝ, d < 0 ∧ HasDerivAt Φ d z) :
    ∀ z ∈ Ioo a 1, 0 < Φ z := by
  sorry

/-! ### Secant bounds -/

/-- **`u ≤ V(x)`** (`DISPLACEMENT_WEIGHT_REDUCTION` §1; the step `h3` of `ss_u_le`): for
`1 < x ≤ β` and the forward-switch inequality `g(x/β) ≤ Sec(1, x, β)`,
`Sec(1, x, β) ≤ Sec(1, x, x)`. Status: stable. -/
theorem hs_u_le_V {x be : ℝ} (hx : 1 < x) (hxb : x ≤ be) (hge : m2g x be ≤ m2Sec 1 x be) :
    m2Sec 1 x be ≤ m2Sec 1 x x := by
  sorry

/-- **`V ≤ V̄`** (`INCOMING_NORM_BOUND` (3)-(6)): `Sec(1, x, x) ≤ 3/4 + 2(x - 1)²/((x + 1)(35x + 13))`
for `x > 1` (`log(1 + z) ≥ (z/(1 + z))(1 + z/2 - 4z²/(24 + 11z))`, `z = (x - 1)/(x + 1)`;
`log 2 > 842/1215`). Status: stable. -/
theorem hs_V_le_Vbar {x : ℝ} (hx : 1 < x) : m2Sec 1 x x ≤ hsVbar x := by
  sorry

/-- **The Gauss ceiling at `β = x`** (`GAUSS_INCOMING_CEILING` (1); inventory HS-S2 R2, HS-S3 R8):
`Sec(1, x, x) < V_G(x)` for `x > 1` (`log(1 + w) > w(43w³ + 252w² + 390w + 180)/(12(1 + w)²(w² +
10w + 15))`, derivative of the difference `w⁶/((1 + w)³(w² + 10w + 15)²)`). Status: stable. -/
theorem hs_V_lt_VG {x : ℝ} (hx : 1 < x) : m2Sec 1 x x < hsVG x := by
  sorry

/-- `V ≤ u₀ = 3/4 + (x - 1)²/(12(x + 1)²)` for `x > 1` (`POSITIVE_DIAGONAL_PAIRING` (5),
`CORRECTED_ENVELOPE_CAP` (1); `ss_log_ge_cubic` as in `ss_V_le`). Status: stable. -/
theorem hs_V_le_U0 {x : ℝ} (hx : 1 < x) : m2Sec 1 x x ≤ hsU0 x := by
  sorry

/-- The tail secant (`INCOMING_NORM_BOUND` (8)): `Sec(x, x, β) ≤ 3/4 + (β - x)²/(48x²)` for
`0 < x ≤ β` (`(s + x)² ≥ 4x²` on `[x, β]`). Status: stable. -/
theorem hs_sec_tail_le {x be : ℝ} (hx : 0 < x) (hxb : x ≤ be) :
    m2Sec x x be ≤ 3 / 4 + (be - x) ^ 2 / (48 * x ^ 2) := by
  sorry

/-- **The incoming majorant** (`INCOMING_NORM_BOUND` (2)): `Sec(1, x, β) ≤ ū(x, β)` for
`1 < x ≤ β` (`ss_sec_add` at `x`, `hs_V_le_Vbar`, `hs_sec_tail_le`). Status: stable. -/
theorem hs_sec_le_ubar {x be : ℝ} (hx : 1 < x) (hxb : x ≤ be) : m2Sec 1 x be ≤ hsUbar x be := by
  sorry

/-- **The uniform incoming floor** (`UNIFORM_INCOMING_FLOOR` (1)-(3)): `u_f(x) < Sec(1, x, β)` for
`1 < x ≤ 9`, `x ≤ β` (`2 artanh r < 2r + 2r³/3 + 2r⁵/(5(1 - r²))`, `r = (β - 1)/(β + 2x + 1)`, and the
quartic identity with `F₀, …, F₄`). Status: stable. -/
theorem hs_sec_gt_floor {x be : ℝ} (hx : 1 < x) (hx9 : x ≤ 9) (hxb : x ≤ be) :
    hsUf x < m2Sec 1 x be := by
  sorry

/-! ### The reverse-centre scale bound -/

/-- **`ρ < 1/7` at a reverse centre** (`HAND_PROOF_REFINEMENTS` §2 (8); scope
`HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT`; the scalar core of `nh_a_sq`, inventory HS-S01 M16): if
`0 < r, t < 1/2`, `0 < ρ < rt`, `ρ < 3/20`, `3/4 ≤ u ≤ U(r)`, `3/4 ≤ v ≤ U(t)`,
`E = 1 + r + t - ρ + log(ρ/(rt)) - (1 - u)/r - (1 - v)/t` and `(4uv - E²)/(16(1 - ρ)²) <
9193/50000`, then `ρ < 1/7`. Status: stable. -/
theorem hs_rev_centre_scale {r t ρ u v E : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) (ht : 0 < t)
    (ht2 : t < 1 / 2) (hρ : 0 < ρ) (hρrt : ρ < r * t) (hρ320 : ρ < 3 / 20) (hu : 3 / 4 ≤ u)
    (hur : u ≤ m2U r) (hv : 3 / 4 ≤ v) (hvt : v ≤ m2U t)
    (hE : E = 1 + r + t - ρ + log (ρ / (r * t)) - (1 - u) / r - (1 - v) / t)
    (hΓ : (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) < 9193 / 50000) : ρ < 1 / 7 := by
  sorry

end SmoothedOctagon
