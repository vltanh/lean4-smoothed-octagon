module

public import SmoothedOctagon.Exclusion.Mixed.Short.Calc
public import SmoothedOctagon.Exclusion.Mixed.Short.Order
public import SmoothedOctagon.Exclusion.Mixed.Short.Point
public import SmoothedOctagon.Exclusion.Mixed.Hand.Scale

/-!
# Hand proof of the smaller-short case: shared scalar functions

Shared scalar functions and generic leaves of the hand proof of `M2Short → False` (gates
S0-S7). Everything
here is a function of plain real numbers, normalized by the central margin `a`:
`x = C/a`, `be = β = B/a`, `al = α = A/a`, `rho = ρ = a²/(a² + 4)`, `t = a/(a + b)`, `S = 1 + x`,
`r = 1/S`.

## Main API

* Transport data:
  `hsLam` (`λ`), `hsDg` (the bridge diagonal `D`), `hsQ` (the outer scale `q = ρ_A = α²λρ`),
  `hsRA` (`r_A`), `hsQc` (the central scale `q_c`), `hsRhoOf` (`ρ` as a function of `q`).
* The opposite-turn functions `hsE`, `hsW`, `hsEL` (`E(t, v)`, `w(t, v)`, `E_L(t, v)`), the outer
  root residual `hsR` (`R_τ(t, v)`) and the Casimir `hsGam`.
* The scale form of the upper envelope: `hsE0`, `hsA1`, `hsA2`, `hsA3`, the
  envelope values `hsWs` (`w_*`), `hsELs` (`E_{L,*}`), `hsGs` (`Γ_*`), and the weighted face value
  `hsF x be al u q τ ℓ m = (w_* - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ + m(w_* - 3/4)`
  (every face test of S0-S5 is a value of `hsF`); `hsRs` (`R*_τ` at scale `q`).
* Incoming-norm majorants, ceilings and floors: `hsVbar`, `hsUbar`, `hsUhat`, `hsUf`, `hsUl`,
  `hsU0`, `hsVG`; the strong-order slope `hsKs`.
* Generic leaves: the quintic `artanh` log bound `hs_log_ge_quintic`, `hs_log_le_cubic_le_one`,
  the tangent `hs_log_le_tangent`, the duration reductions `hs_dur_max`, `hs_dur_three`, the
  first-contact lemma `hs_first_contact`, the secant bounds `hs_u_le_V`, `hs_V_le_Vbar`,
  `hs_V_lt_VG`, `hs_V_le_U0`, `hs_sec_tail_le`, `hs_sec_le_ubar`, `hs_sec_gt_floor`, and the
  reverse-centre scale bound `hs_rev_centre_scale`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Transport data -/

/-- `λ = 1/(1 + ρ(α² - 1)) = (a² + 4)/(A² + 4)`. -/
noncomputable def hsLam (al rho : ℝ) : ℝ := 1 / (1 + rho * (al ^ 2 - 1))

/-- The bridge diagonal `D = α² + 2αβ + 1 + 2x - 2βx`. -/
noncomputable def hsDg (x be al : ℝ) : ℝ := al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x

/-- The outer scale `q = ρ_A = α²λρ = A²/(A² + 4)`. -/
noncomputable def hsQ (al rho : ℝ) : ℝ := al ^ 2 * hsLam al rho * rho

/-- `r_A = α/(α + β) = A/(A + B)`. -/
noncomputable def hsRA (al be : ℝ) : ℝ := al / (al + be)

/-- The central scale `q_c = α²/(x(x + 2) + α²)`, the value of `q` at `ρ = r²`. -/
noncomputable def hsQc (x al : ℝ) : ℝ := al ^ 2 / (x * (x + 2) + al ^ 2)

/-- `ρ` as a function of the outer scale: `ρ = q/(α² - (α² - 1)q)`. -/
noncomputable def hsRhoOf (al q : ℝ) : ℝ := q / (al ^ 2 - (al ^ 2 - 1) * q)

/-! ### The opposite-turn functions and the outer root residual -/

/-- Centre stationarity at `a` as a function of the opposite turn `(t, v)`:
`E(t, v) = (u - 1)/r + (v - 1)/t + 1 + r + t - ρ + log(ρ/(rt))`, `r = 1/(1 + x)`. -/
noncomputable def hsE (x rho u t v : ℝ) : ℝ :=
  (u - 1) * (1 + x) + (v - 1) / t + 1 + 1 / (1 + x) + t - rho + log (rho * (1 + x) / t)

/-- The transported outer norm `w(t, v) = λ²v + d²u - dλE(t, v)`, `d = λρD`
(the same-lift transport from `a` to the outer centre). -/
noncomputable def hsW (x be al rho u t v : ℝ) : ℝ :=
  hsLam al rho ^ 2 * v + (hsLam al rho * rho * hsDg x be al) ^ 2 * u -
    hsLam al rho * rho * hsDg x be al * hsLam al rho * hsE x rho u t v

/-- The transported outer pairing `E_L(t, v) = 2du - λE(t, v)`. -/
noncomputable def hsEL (x be al rho u t v : ℝ) : ℝ :=
  2 * (hsLam al rho * rho * hsDg x be al) * u - hsLam al rho * hsE x rho u t v

/-- **The outer root residual**:
`R_τ(t, v) = (w - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_L + log(τq/r_A)` with `w`, `E_L`
transported from `(t, v)`; the actual outer switch is `R_τ = 0` at `τ = (A + P_f)/A`. -/
noncomputable def hsR (x be al rho u τ t v : ℝ) : ℝ :=
  (hsW x be al rho u t v - 1) * τ + 1 / τ + (u - 1) / hsRA al be + hsRA al be + 1 - hsQ al rho -
    hsEL x be al rho u t v + log (τ * hsQ al rho / hsRA al be)

/-- The squared Casimir `Γ = (4uv - E²)/(16(1 - ρ)²)`. -/
noncomputable def hsGam (rho u v E : ℝ) : ℝ := (4 * u * v - E ^ 2) / (16 * (1 - rho) ^ 2)

/-! ### The scale form of the upper envelope -/

/-- `E₀ = S(u - 1) + 1/S`. -/
noncomputable def hsE0 (x u : ℝ) : ℝ := (1 + x) * (u - 1) + 1 / (1 + x)

/-- `A₁ = 2ε + n + ΔE₀` with `ε = 1 - α⁻²`, `n = S/α²`, `Δ = D/α²`. -/
noncomputable def hsA1 (x be al u : ℝ) : ℝ :=
  2 * (1 - 1 / al ^ 2) + (1 + x) / al ^ 2 + hsDg x be al / al ^ 2 * hsE0 x u

/-- `A₂ = ε² + εn + n² + Δ²u + ΔεE₀ - Δ(2S - 1)/α²`. -/
noncomputable def hsA2 (x be al u : ℝ) : ℝ :=
  (1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1 + x) / al ^ 2) + ((1 + x) / al ^ 2) ^ 2 +
    (hsDg x be al / al ^ 2) ^ 2 * u + hsDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * hsE0 x u -
    hsDg x be al / al ^ 2 * (2 * (1 + x) - 1) / al ^ 2

/-- `A₃ = 2Δu + εE₀ - (2S - 1)/α²`. -/
noncomputable def hsA3 (x be al u : ℝ) : ℝ :=
  2 * (hsDg x be al / al ^ 2) * u + (1 - 1 / al ^ 2) * hsE0 x u - (2 * (1 + x) - 1) / al ^ 2

/-- The upper-envelope outer norm at scale `q`: `w_* = 1 - qA₁ + q²A₂`. -/
noncomputable def hsWs (x be al u q : ℝ) : ℝ := 1 - q * hsA1 x be al u + q ^ 2 * hsA2 x be al u

/-- The upper-envelope outer pairing at scale `q`: `E_{L,*} = -E₀ + qA₃`. -/
noncomputable def hsELs (x be al u q : ℝ) : ℝ := -hsE0 x u + q * hsA3 x be al u

/-- **The weighted face value** at scale `q`, duration `τ`, log value `ℓ` and floor weight `m`:
`(w_* - 1)τ + 1/τ + (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ + m(w_* - 3/4)`. With
`ℓ = log(τq/r_A)` it is the weighted upper envelope `R*_τ + m(w_* - 3/4)`; with
`ℓ` a rational log majorant it is a face test. -/
noncomputable def hsF (x be al u q τ ℓ m : ℝ) : ℝ :=
  (hsWs x be al u q - 1) * τ + 1 / τ + (u - 1) / hsRA al be + hsRA al be + 1 - q -
    hsELs x be al u q + ℓ + m * (hsWs x be al u q - 3 / 4)

/-- `R*_τ` at scale `q`. With `p = τq` this is `𝓡(u; p, q) = C(p) + qL(p)`. -/
noncomputable def hsRs (x be al u q τ : ℝ) : ℝ :=
  hsF x be al u q τ (log (τ * q / hsRA al be)) 0

/-- The upper-envelope Casimir at scale `q`: `Γ_* = (4uU(t₀) - E_*²)/(16(1 - ρ)²)` with
`ρ = ρ(q)`, `t₀ = ρS`, `E_* = E₀ + ρ(2S - 1)`. -/
noncomputable def hsGs (x al u q : ℝ) : ℝ :=
  (4 * u * m2U (hsRhoOf al q * (1 + x)) -
      (hsE0 x u + hsRhoOf al q * (2 * (1 + x) - 1)) ^ 2) / (16 * (1 - hsRhoOf al q) ^ 2)

/-- `C(p) = E₀ + (u - 1)/r_A + r_A + 1 - pA₁ + log(p/r_A)`. -/
noncomputable def hsCp (x be al u p : ℝ) : ℝ :=
  hsE0 x u + (u - 1) / hsRA al be + hsRA al be + 1 - p * hsA1 x be al u + log (p / hsRA al be)

/-- `L(p) = pA₂ + 1/p - 1 - A₃`. -/
noncomputable def hsLp (x be al u p : ℝ) : ℝ := p * hsA2 x be al u + 1 / p - 1 - hsA3 x be al u

/-- **The weighted envelope at fixed normalized duration `p = τq`** as a polynomial in the scale:
`Φ(q) = C(p) + m/4 + q(L(p) - mA₁) + mq²A₂`; with `m = 0` it is `𝓡(u; p, q) = C(p) + qL(p)`.
For `q > 0` it equals
`hsF x be al u q (p/q) (log(p/r_A)) m` (`hs_phi_eq`). -/
noncomputable def hsPhi (x be al u p m q : ℝ) : ℝ :=
  hsCp x be al u p + m / 4 + q * (hsLp x be al u p - m * hsA1 x be al u) +
    m * q ^ 2 * hsA2 x be al u

/-! ### Angle coordinates and the physical shear -/

/-- `R = (x - 1)/(x + 1)`. -/
noncomputable def hsRr (x : ℝ) : ℝ := (x - 1) / (x + 1)

/-- The angle coordinate `T_s = (β - α)/(β + α)` (distinct from the duration endpoint `T`). -/
noncomputable def hsTs (al be : ℝ) : ℝ := (be - al) / (be + al)

/-- The anisotropy `A = U₁/U₂ - 1 = (βx - α)(αx - β)/(S²(α² + αβ + β²))`. -/
noncomputable def hsAn (x be al : ℝ) : ℝ :=
  (be * x - al) * (al * x - be) / ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2))

/-- **The physical shear**:
`h = (√3/3)(βx - α)((x + 2)α + (2x + 1)β)/(S²K_A) - (2√3/3)U₁Q₀ ρ/(1 - ρ)`, `K_A = α² + αβ + β²`,
`U₁ = (x² + x + 1)/S²`, `Q₀ = 2βx - x - αβ`, all in the normalized margins. -/
noncomputable def hsShear (x be al rho : ℝ) : ℝ :=
  √3 / 3 * ((be * x - al) * ((x + 2) * al + (2 * x + 1) * be) /
      ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2)) -
    2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) * (2 * be * x - x - al * be) * (rho / (1 - rho)))

/-! ### Incoming-norm majorants and floors -/

/-- `u_v = V̄(x) = 3/4 + 2(x - 1)²/((x + 1)(35x + 13))`. -/
noncomputable def hsVbar (x : ℝ) : ℝ := 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13))

/-- `ū(x, β) = 3/4 + [2(x - 1)³/((x + 1)(35x + 13)) + (β - x)³/(48x²)]/(β - 1)`. -/
noncomputable def hsUbar (x be : ℝ) : ℝ :=
  3 / 4 + (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (be - x) ^ 3 / (48 * x ^ 2)) / (be - 1)

/-- `û(x, β) = 3/4 + V_g(x - 1 + (β - x)/8)/(β - 1)`, `V_g = 2(x - 1)²/((x + 1)(35x + 13))`. -/
noncomputable def hsUhat (x be : ℝ) : ℝ :=
  3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + (be - x) / 8) / (be - 1)

/-- The uniform incoming floor `u_f = 3/4 + (x - 1)²/(28(x + 1)²)`. -/
noncomputable def hsUf (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (28 * (x + 1) ^ 2)

/-- The β-dependent ceiling `u_ℓ = 3/4 + (x - 1)²(β + 15x - 16)/(8S(35x + 13)(β - 1))`. -/
noncomputable def hsUl (x be : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (be + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (be - 1))

/-- `u₀ = 3/4 + (x - 1)²/(12(x + 1)²)`. -/
noncomputable def hsU0 (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (12 * (x + 1) ^ 2)

/-- The Gauss ceiling of `V`: `V_G = 3/4 + (x - 1)²(71x² + 48x + 1)/(96x(x + 1)(13x² + 14x + 3))`
(the Gauss ceiling of `Sec(1, x, β)` at `β = x`). -/
noncomputable def hsVG (x : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (71 * x ^ 2 + 48 * x + 1) / (96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3))

/-- The strong lower-order slope `k_s(x) = 4(x + 1)/(7x + 1)`. -/
noncomputable def hsKs (x : ℝ) : ℝ := 4 * (x + 1) / (7 * x + 1)

/-! ### Logarithm bounds -/

/-- Three terms of `log z = 2 artanh w`, `w = (z - 1)/(z + 1)`: `2(w + w³/3 + w⁵/5) ≤ log z` for
`z ≥ 1` (derivative of the difference `(z - 1)⁶/(z(z + 1)⁶)`). -/
theorem hs_log_ge_quintic {z : ℝ} (hz : 1 ≤ z) :
    2 * ((z - 1) / (z + 1) + ((z - 1) / (z + 1)) ^ 3 / 3 + ((z - 1) / (z + 1)) ^ 5 / 5) ≤
      log z := by
  rcases eq_or_lt_of_le hz with h | h
  · subst h; norm_num
  · have := nh_log_one_add_gt3 (x := z - 1) (by linarith)
    rw [show z - 1 + 2 = z + 1 by ring, show 1 + (z - 1) = z by ring] at this
    linarith

/-- For `0 < y ≤ 1`, `log y ≤ 2z + (2/3)z³`, `z = (y - 1)/(y + 1)`
(`ss_log_ge_cubic` at `1/y`). -/
theorem hs_log_le_cubic_le_one {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ 2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3 := by
  have h := ss_log_ge_cubic (z := y⁻¹) ((one_le_inv₀ hy).2 hy1)
  have e : (y⁻¹ - 1) / (y⁻¹ + 1) = -((y - 1) / (y + 1)) := by
    field_simp; ring
  rw [e, Real.log_inv] at h
  have e3 : (-((y - 1) / (y + 1))) ^ 3 = -((y - 1) / (y + 1)) ^ 3 := by ring
  rw [e3] at h
  linarith

/-- The tangent at `4/5`: `log y ≤ 5y/4 - 11/9` for `y > 0`
(`log(5/4) ≥ 2/9`). -/
theorem hs_log_le_tangent {y : ℝ} (hy : 0 < y) : log y ≤ 5 * y / 4 - 11 / 9 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 5 / 4 * y by positivity)
  rw [Real.log_mul (by norm_num) hy.ne'] at h1
  have h2 := ss_log_ge_pade (z := 5 / 4) (by norm_num)
  norm_num at h2
  linarith

/-! ### Duration reductions -/

/-- **The duration maximum**: for `2 ≤ τ ≤ T`,
`(w - 1)τ + 1/τ + log(τ/T) ≤ max{R₂, R₂ + (T - 2)(w - 3/4)}`, `R₂ = 2w - 3/2 + log(2/T)` (exact
remainder `log(τ/2) - τ/4 + 1/τ ≤ 0`, `ss_log_le_half`). -/
theorem hs_dur_max {w T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    (w - 1) * τ + 1 / τ + log (τ / T) ≤
      max (2 * w - 3 / 2 + log (2 / T)) (2 * w - 3 / 2 + log (2 / T) + (T - 2) * (w - 3 / 4)) := by
  have hτ0 : 0 < τ := by linarith
  have hT0 : 0 < T := by linarith
  have hsplit : log (τ / T) = log (τ / 2) + log (2 / T) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hh := ss_log_le_half (z := τ / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have e : (τ / 2 - (τ / 2)⁻¹) / 2 = τ / 4 - 1 / τ := by field_simp; ring
  rw [e] at hh
  have key : (w - 1) * τ + 1 / τ + log (τ / T) ≤
      2 * w - 3 / 2 + log (2 / T) + (τ - 2) * (w - 3 / 4) := by
    rw [hsplit]; linarith
  refine key.trans ?_
  rcases le_total (w - 3 / 4) 0 with hw | hw
  · exact le_max_of_le_left (by
      linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ τ - 2) hw])
  · exact le_max_of_le_right (by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - τ) hw])

/-- The chord bound for `cτ + 1/τ + e` on `[a, b] ⊂ (0, ∞)` (`1/τ ≤ (a + b - τ)/(ab)`, then an
affine function is at most its larger endpoint value). -/
private theorem hsb_chord {c e a b τ : ℝ} (ha : 0 < a) (haτ : a ≤ τ) (hτb : τ ≤ b) :
    c * τ + 1 / τ + e ≤ max (c * a + 1 / a + e) (c * b + 1 / b + e) := by
  have hτ : 0 < τ := lt_of_lt_of_le ha haτ
  have hb : 0 < b := lt_of_lt_of_le hτ hτb
  have hchord : 1 / τ ≤ (a + b - τ) / (a * b) := by
    rw [div_le_div_iff₀ hτ (by positivity)]
    linarith [mul_nonneg (sub_nonneg.2 haτ) (sub_nonneg.2 hτb)]
  set k := c - 1 / (a * b) with hk
  have hA : c * τ + (a + b - τ) / (a * b) + e = c * a + 1 / a + e + k * (τ - a) := by
    rw [hk]; field_simp; ring
  have hB : c * b + 1 / b + e = c * a + 1 / a + e + k * (b - a) := by
    rw [hk]; field_simp; ring
  rcases le_total k 0 with hk0 | hk0
  · refine le_max_of_le_left ?_
    linarith [mul_nonpos_of_nonpos_of_nonneg hk0 (sub_nonneg.2 haτ)]
  · refine le_max_of_le_right ?_
    rw [hB]
    linarith [mul_le_mul_of_nonneg_left (sub_le_sub_right hτb a) hk0]

/-- **The three duration tests**: with `F(τ, ℓ) = c₁τ + 1/τ + c₀ + ℓ` and `2 ≤ τ ≤ T`,
`F(τ, log(τ/T)) ≤ max{F(2, 5/(2T) - 11/9), F(8T/9, -1/9), F(T, 0)}` (the two log tangents of
`hs_log_le_tangent` and convexity of `1/τ`). -/
theorem hs_dur_three {c₁ c₀ T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    c₁ * τ + 1 / τ + c₀ + log (τ / T) ≤
      max (c₁ * 2 + 1 / 2 + c₀ + (5 / (2 * T) - 11 / 9))
        (max (c₁ * (8 * T / 9) + 9 / (8 * T) + c₀ - 1 / 9) (c₁ * T + 1 / T + c₀)) := by
  have hτ0 : 0 < τ := by linarith
  have hT0 : 0 < T := by linarith
  rcases le_total τ (8 * T / 9) with h8 | h8
  · have hl := hs_log_le_tangent (show 0 < τ / T by positivity)
    have hc := hsb_chord (c := c₁ + 5 / (4 * T)) (e := c₀ - 11 / 9) (by norm_num : (0 : ℝ) < 2)
      h2 h8
    have e1 : (c₁ + 5 / (4 * T)) * τ + 1 / τ + (c₀ - 11 / 9) =
        c₁ * τ + 1 / τ + c₀ + (5 * (τ / T) / 4 - 11 / 9) := by field_simp; ring
    have e2 : (c₁ + 5 / (4 * T)) * 2 + 1 / 2 + (c₀ - 11 / 9) =
        c₁ * 2 + 1 / 2 + c₀ + (5 / (2 * T) - 11 / 9) := by field_simp; ring
    have e3 : (c₁ + 5 / (4 * T)) * (8 * T / 9) + 1 / (8 * T / 9) + (c₀ - 11 / 9) =
        c₁ * (8 * T / 9) + 9 / (8 * T) + c₀ - 1 / 9 := by field_simp; ring
    rw [e1, e2, e3] at hc
    have := le_trans (show c₁ * τ + 1 / τ + c₀ + log (τ / T) ≤
      c₁ * τ + 1 / τ + c₀ + (5 * (τ / T) / 4 - 11 / 9) by linarith) hc
    exact this.trans (max_le_max le_rfl (le_max_left _ _))
  · have hl := Real.log_le_sub_one_of_pos (show 0 < τ / T by positivity)
    have hc := hsb_chord (c := c₁ + 1 / T) (e := c₀ - 1) (by positivity : (0 : ℝ) < 8 * T / 9) h8 hτ
    have e1 : (c₁ + 1 / T) * τ + 1 / τ + (c₀ - 1) = c₁ * τ + 1 / τ + c₀ + (τ / T - 1) := by
      field_simp; ring
    have e3 : (c₁ + 1 / T) * (8 * T / 9) + 1 / (8 * T / 9) + (c₀ - 1) =
        c₁ * (8 * T / 9) + 9 / (8 * T) + c₀ - 1 / 9 := by field_simp; ring
    have e4 : (c₁ + 1 / T) * T + 1 / T + (c₀ - 1) = c₁ * T + 1 / T + c₀ := by field_simp; ring
    rw [e1, e3, e4] at hc
    have := le_trans (show c₁ * τ + 1 / τ + c₀ + log (τ / T) ≤
      c₁ * τ + 1 / τ + c₀ + (τ / T - 1) by linarith) hc
    exact this.trans (le_max_right _ _)

/-! ### The first-contact lemma -/

/-- **First contact** (the barrier form used by the order bounds): if `Φ` is continuous on `[a, 1]`,
`Φ(1) = 0`, and at every zero `z ∈ (a, 1]` of `Φ` it has a negative derivative, then `Φ > 0` on
`(a, 1)`. -/
theorem hs_first_contact {Φ : ℝ → ℝ} {a : ℝ} (ha : a < 1) (hc : ContinuousOn Φ (Icc a 1))
    (h1 : Φ 1 = 0)
    (hd : ∀ z ∈ Ioc a 1, Φ z = 0 → ∃ d : ℝ, d < 0 ∧ HasDerivAt Φ d z) :
    ∀ z ∈ Ioo a 1, 0 < Φ z := by
  have hside : ∀ z ∈ Ioc a 1, Φ z = 0 →
      (∃ l < z, ∀ y ∈ Ioo l z, 0 < Φ y) ∧ (∃ l > z, ∀ y ∈ Ioo z l, Φ y < 0) := by
    intro z hz hz0
    obtain ⟨d, hd0, hder⟩ := hd z hz hz0
    have hs := (hasDerivAt_iff_tendsto_slope.1 hder).eventually_lt_const hd0
    constructor
    · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (nhdsLT_le_nhdsNE z hs)
      refine ⟨l, hl, fun y hy => ?_⟩
      have h : slope Φ z y < 0 := hsub hy
      rw [slope_def_field, hz0, sub_zero] at h
      rcases div_neg_iff.1 h with h' | h'
      · exact h'.1
      · linarith [h'.2, hy.2]
    · obtain ⟨l, hl, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (nhdsGT_le_nhdsNE z hs)
      refine ⟨l, hl, fun y hy => ?_⟩
      have h : slope Φ z y < 0 := hsub hy
      rw [slope_def_field, hz0, sub_zero] at h
      rcases div_neg_iff.1 h with h' | h'
      · linarith [h'.2, hy.1]
      · exact h'.1
  intro z₀ hz₀
  by_contra hneg
  push Not at hneg
  obtain ⟨⟨l, hl, hpos⟩, -⟩ := hside 1 ⟨ha, le_rfl⟩ h1
  set c := (max z₀ l + 1) / 2 with hcdef
  have hm1 : max z₀ l < 1 := max_lt hz₀.2 hl
  have hzc : z₀ < c := by have := le_max_left z₀ l; linarith
  have hlc : l < c := by have := le_max_right z₀ l; linarith
  have hc1 : c < 1 := by linarith
  have hΦc : 0 < Φ c := hpos c ⟨hlc, hc1⟩
  have hcont : ContinuousOn Φ (Icc z₀ c) := hc.mono (Icc_subset_Icc hz₀.1.le hc1.le)
  set K := Icc z₀ c ∩ Φ ⁻¹' (Iic 0) with hKdef
  have hKc : IsClosed K := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hKne : K.Nonempty := ⟨z₀, ⟨le_rfl, hzc.le⟩, hneg⟩
  have hKbdd : BddAbove K := ⟨c, fun y hy => hy.1.2⟩
  have hmK : sSup K ∈ K := hKc.csSup_mem hKne hKbdd
  set m := sSup K with hmdef
  have hm_le : ∀ y ∈ K, y ≤ m := fun y hy => le_csSup hKbdd hy
  have hmc : m < c := by
    refine lt_of_le_of_ne hmK.1.2 fun h => ?_
    have h2 : Φ m ≤ 0 := hmK.2
    rw [h] at h2; linarith
  have hΦm : Φ m = 0 := by
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hmc.le
      (hcont.mono (Icc_subset_Icc hmK.1.1 le_rfl)) ⟨hmK.2, hΦc.le⟩
    have hyK : y ∈ K := ⟨⟨hmK.1.1.trans hy.1, hy.2⟩, show Φ y ≤ 0 from hy0.le⟩
    have hym : y = m := le_antisymm (hm_le y hyK) hy.1
    rw [← hym]; exact hy0
  obtain ⟨-, ⟨l', hl', hneg'⟩⟩ := hside m ⟨by linarith [hz₀.1, hmK.1.1], by linarith⟩ hΦm
  set y := (m + min l' c) / 2 with hydef
  have hmin : m < min l' c := lt_min hl' hmc
  have hy1 : m < y := by linarith
  have hy2 : y < l' := by have := min_le_left l' c; linarith
  have hy3 : y < c := by have := min_le_right l' c; linarith
  have hΦy : Φ y < 0 := hneg' y ⟨hy1, hy2⟩
  have hyK : y ∈ K := ⟨⟨by linarith [hmK.1.1], hy3.le⟩, show Φ y ≤ 0 from hΦy.le⟩
  linarith [hm_le y hyK]

/-! ### Secant bounds -/

/-- **`u ≤ V(x)`** (the step `h3` of `ss_u_le`): for
`1 < x ≤ β` and the forward-switch inequality `g(x/β) ≤ Sec(1, x, β)`,
`Sec(1, x, β) ≤ Sec(1, x, x)`. -/
theorem hs_u_le_V {x be : ℝ} (hx : 1 < x) (hxb : x ≤ be) (hge : m2g x be ≤ m2Sec 1 x be) :
    m2Sec 1 x be ≤ m2Sec 1 x x := by
  have hx0 : 0 < x := by linarith
  have hb : 0 < be := by linarith
  have hadd := ss_sec_add one_pos hx0 hx0 hb
  have h1 := ss_sec_le_right hx0 hxb
  rw [← ss_m2g_eq (by linarith), m2g_comm] at h1
  have h2 := mul_le_mul_of_nonneg_left (h1.trans hge) (by linarith : (0 : ℝ) ≤ be - x)
  have h3 : (x - 1) * m2Sec 1 x be ≤ (x - 1) * m2Sec 1 x x := by linarith
  exact le_of_mul_le_mul_left h3 (by linarith)

/-- The Gauss logarithm bound
`log(1 + z) > z(43z³ + 252z² + 390z + 180)/(12(1 + z)²(z² + 10z + 15))` for `z > 0`
(derivative of the difference `z⁶/((1 + z)³(z² + 10z + 15)²)`). -/
private theorem hsb_log_gauss {z : ℝ} (hz : 0 < z) :
    z * (43 * z ^ 3 + 252 * z ^ 2 + 390 * z + 180) / (12 * (1 + z) ^ 2 * (z ^ 2 + 10 * z + 15)) <
      log (1 + z) := by
  have h := ss_lt_of_deriv (x := 0) (y := z)
    (f := fun s => log (1 + s) - s * (43 * s ^ 3 + 252 * s ^ 2 + 390 * s + 180) /
      (12 * (1 + s) ^ 2 * (s ^ 2 + 10 * s + 15)))
    (f' := fun s => s ^ 6 / ((1 + s) ^ 3 * (s ^ 2 + 10 * s + 15) ^ 2)) hz (fun s hs => ?_)
    (fun s hs => by have := hs.1; positivity)
  · simp only [add_zero, log_one, zero_mul, zero_div, sub_zero] at h
    linarith
  have hs0 : 0 ≤ s := hs.1
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have hN : HasDerivAt (fun s : ℝ => s * (43 * s ^ 3 + 252 * s ^ 2 + 390 * s + 180))
      (172 * s ^ 3 + 756 * s ^ 2 + 780 * s + 180) s := by
    have hp : HasDerivAt (fun s : ℝ => 43 * s ^ 3 + 252 * s ^ 2 + 390 * s + 180)
        (43 * (3 * s ^ 2) + 252 * (2 * s) + 390) s := by
      have := (((((hasDerivAt_id' s).pow 3).const_mul (43 : ℝ)).add
        (((hasDerivAt_id' s).pow 2).const_mul (252 : ℝ))).add
        ((hasDerivAt_id' s).const_mul (390 : ℝ))).add_const (180 : ℝ)
      refine this.congr_deriv ?_
      push_cast; ring
    refine ((hasDerivAt_id' s).mul hp).congr_deriv ?_
    ring
  have hD : HasDerivAt (fun s : ℝ => 12 * (1 + s) ^ 2 * (s ^ 2 + 10 * s + 15))
      (12 * (2 * (1 + s)) * (s ^ 2 + 10 * s + 15) + 12 * (1 + s) ^ 2 * (2 * s + 10)) s := by
    have hq : HasDerivAt (fun s : ℝ => s ^ 2 + 10 * s + 15) (2 * s + 10) s := by
      have := ((((hasDerivAt_id' s).pow 2).add
        ((hasDerivAt_id' s).const_mul (10 : ℝ))).add_const (15 : ℝ))
      refine this.congr_deriv ?_
      push_cast; ring
    have := ((h1.pow 2).const_mul (12 : ℝ)).mul hq
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]; push_cast; ring
  have hDpos : 12 * (1 + s) ^ 2 * (s ^ 2 + 10 * s + 15) ≠ 0 := by positivity
  have := (h1.log (by positivity)).sub (hN.div hD hDpos)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `V(x) < V_G(x)`: `hsb_log_gauss` at `z = (x - 1)/(x + 1)`, `1 + z = 2x/(x + 1)`, and
`V_G - V = (x/(x - 1))(log(1 + z) - [Gauss bound])`. -/
private theorem hsb_V_lt_VG {x : ℝ} (hx : 1 < x) : m2Sec 1 x x < hsVG x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hz0 : 0 < (x - 1) / (x + 1) := div_pos hx1 (by linarith)
  have hl := hsb_log_gauss hz0
  have e1 : 1 + (x - 1) / (x + 1) = (x + x) / (1 + x) := by field_simp; ring
  rw [e1] at hl
  rw [m2Sec_of_ne hx.ne]
  have key : hsVG x = 1 + x ^ 2 / ((1 + x) * (x + x)) - x / (x - 1) *
      ((x - 1) / (x + 1) * (43 * ((x - 1) / (x + 1)) ^ 3 + 252 * ((x - 1) / (x + 1)) ^ 2 +
        390 * ((x - 1) / (x + 1)) + 180) / (12 * ((x + x) / (1 + x)) ^ 2 *
        (((x - 1) / (x + 1)) ^ 2 + 10 * ((x - 1) / (x + 1)) + 15))) := by
    unfold hsVG
    have h1 : x + 1 ≠ 0 := by linarith
    have h2 : x - 1 ≠ 0 := by linarith
    have h3 : 13 * x ^ 2 + 14 * x + 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [key]
  have := mul_lt_mul_of_pos_left hl (div_pos hx0 hx1)
  linarith

/-- **`V ≤ V̄`**: `Sec(1, x, x) ≤ 3/4 + 2(x - 1)²/((x + 1)(35x + 13))`
for `x > 1`, from `V < V_G` (`hs_V_lt_VG`) and
`V̄ - V_G = (x - 1)³(11x² + 96x + 13)/(96x(x + 1)(35x + 13)(13x² + 14x + 3)) ≥ 0`. -/
theorem hs_V_le_Vbar {x : ℝ} (hx : 1 < x) : m2Sec 1 x x ≤ hsVbar x := by
  refine (hsb_V_lt_VG hx).le.trans ?_
  have hx0 : 0 < x := by linarith
  have e : hsVbar x - hsVG x = (x - 1) ^ 3 * (11 * x ^ 2 + 96 * x + 13) /
      (96 * x * (x + 1) * (35 * x + 13) * (13 * x ^ 2 + 14 * x + 3)) := by
    unfold hsVbar hsVG
    field_simp
    ring
  have : 0 ≤ (x - 1) ^ 3 * (11 * x ^ 2 + 96 * x + 13) /
      (96 * x * (x + 1) * (35 * x + 13) * (13 * x ^ 2 + 14 * x + 3)) := by
    have : 0 ≤ x - 1 := by linarith
    positivity
  linarith

/-- **The Gauss ceiling at `β = x`**:
`Sec(1, x, x) < V_G(x)` for `x > 1` (`log(1 + w) > w(43w³ + 252w² + 390w + 180)/(12(1 + w)²(w² +
10w + 15))`, derivative of the difference `w⁶/((1 + w)³(w² + 10w + 15)²)`). -/
theorem hs_V_lt_VG {x : ℝ} (hx : 1 < x) : m2Sec 1 x x < hsVG x := by
  exact hsb_V_lt_VG hx

/-- `V ≤ u₀ = 3/4 + (x - 1)²/(12(x + 1)²)` for `x > 1`, from `V < V_G` (`hs_V_lt_VG`) and
`u₀ - V_G = (x - 1)³(33x² + 26x + 1)/(96x(x + 1)²(13x² + 14x + 3)) ≥ 0`. -/
theorem hs_V_le_U0 {x : ℝ} (hx : 1 < x) : m2Sec 1 x x ≤ hsU0 x := by
  refine (hsb_V_lt_VG hx).le.trans ?_
  have hx0 : 0 < x := by linarith
  have e : hsU0 x - hsVG x = (x - 1) ^ 3 * (33 * x ^ 2 + 26 * x + 1) /
      (96 * x * (x + 1) ^ 2 * (13 * x ^ 2 + 14 * x + 3)) := by
    unfold hsU0 hsVG
    field_simp
    ring
  have : 0 ≤ (x - 1) ^ 3 * (33 * x ^ 2 + 26 * x + 1) /
      (96 * x * (x + 1) ^ 2 * (13 * x ^ 2 + 14 * x + 3)) := by
    have : 0 ≤ x - 1 := by linarith
    positivity
  linarith

/-- The tail secant: `Sec(x, x, β) ≤ 3/4 + (β - x)²/(48x²)` for
`0 < x ≤ β` (`(s + x)² ≥ 4x²` on `[x, β]`). -/
theorem hs_sec_tail_le {x be : ℝ} (hx : 0 < x) (hxb : x ≤ be) :
    m2Sec x x be ≤ 3 / 4 + (be - x) ^ 2 / (48 * x ^ 2) := by
  rcases eq_or_lt_of_le hxb with h | h
  · subst h
    rw [m2Sec_self]; unfold m2g
    rw [sub_self]
    have : x + x ≠ 0 := by positivity
    field_simp; ring_nf; norm_num
  have hb : 0 < be := by linarith
  have hm := ss_le_of_deriv (x := x) (y := be)
    (f := fun s => 3 / 4 * s + (s - x) ^ 3 / (48 * x ^ 2) - ss_FB x s)
    (f' := fun s => 3 / 4 + (s - x) ^ 2 / (16 * x ^ 2) - ss_gB x s) hxb
    (fun s hs => by
      have hs0 : 0 < s := lt_of_lt_of_le hx hs.1
      have h3 : HasDerivAt (fun s : ℝ => (s - x) ^ 3 / (48 * x ^ 2))
          ((s - x) ^ 2 / (16 * x ^ 2)) s := by
        have := (((hasDerivAt_id' s).sub_const x).pow 3).div_const (48 * x ^ 2)
        refine this.congr_deriv ?_
        push_cast; field_simp; ring
      have := ((((hasDerivAt_id' s).const_mul (3 / 4 : ℝ))).add h3).sub (ss_FB_hasDerivAt hx hs0)
      refine this.congr_deriv ?_
      ring)
    (fun s hs => by
      have hs0 : 0 < s := lt_trans hx hs.1
      unfold ss_gB
      have e : 3 / 4 + (s - x) ^ 2 / (16 * x ^ 2) - (1 - x * s / (x + s) ^ 2) =
          (s - x) ^ 2 * ((s - x) * (s + 3 * x)) / (16 * x ^ 2 * (x + s) ^ 2) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ s - x := by linarith [hs.1]
      positivity)
  have e := ss_sec_mul hx hx hb
  have hbx : 0 < be - x := by linarith
  have h1 : (be - x) * m2Sec x x be ≤ (be - x) * (3 / 4 + (be - x) ^ 2 / (48 * x ^ 2)) := by
    rw [e]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero] at hm
    have : (be - x) * (3 / 4 + (be - x) ^ 2 / (48 * x ^ 2)) =
        3 / 4 * be + (be - x) ^ 3 / (48 * x ^ 2) - 3 / 4 * x := by field_simp; ring
    linarith
  exact le_of_mul_le_mul_left h1 hbx

/-- **The incoming majorant**: `Sec(1, x, β) ≤ ū(x, β)` for
`1 < x ≤ β` (`ss_sec_add` at `x`, `hs_V_le_Vbar`, `hs_sec_tail_le`). -/
theorem hs_sec_le_ubar {x be : ℝ} (hx : 1 < x) (hxb : x ≤ be) : m2Sec 1 x be ≤ hsUbar x be := by
  have hx0 : 0 < x := by linarith
  have hb : 0 < be := by linarith
  have hb1 : 0 < be - 1 := by linarith
  have hadd := ss_sec_add one_pos hx0 hx0 hb
  have hV := hs_V_le_Vbar hx
  have hT := hs_sec_tail_le hx0 hxb
  have h1 : (be - 1) * m2Sec 1 x be ≤ (be - 1) * hsUbar x be := by
    rw [hadd]
    have k1 := mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ x - 1)
    have k2 := mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℝ) ≤ be - x)
    have e : (be - 1) * hsUbar x be = (x - 1) * hsVbar x +
        (be - x) * (3 / 4 + (be - x) ^ 2 / (48 * x ^ 2)) := by
      unfold hsUbar hsVbar
      field_simp
      ring
    linarith
  exact le_of_mul_le_mul_left h1 hb1

/-- The atanh upper bound with tail denominators lowered to `5`:
`log y ≤ (y - 1)(3y⁴ + 68y³ + 98y² + 68y + 3)/(30y(y + 1)³) = 2r + 2r³/3 + 2r⁵/(5(1 - r²))`,
`r = (y - 1)/(y + 1)`, for `y ≥ 1` (derivative of the difference `(y - 1)⁶/(10y²(y + 1)⁴)`). -/
private theorem hsb_log_le_atanh5 {y : ℝ} (hy : 1 ≤ y) :
    log y ≤ (y - 1) * (3 * y ^ 4 + 68 * y ^ 3 + 98 * y ^ 2 + 68 * y + 3) /
      (30 * y * (y + 1) ^ 3) := by
  have h := ss_le_of_deriv (x := 1) (y := y)
    (f := fun s => (s - 1) * (3 * s ^ 4 + 68 * s ^ 3 + 98 * s ^ 2 + 68 * s + 3) /
      (30 * s * (s + 1) ^ 3) - log s)
    (f' := fun s => (s - 1) ^ 6 / (10 * s ^ 2 * (s + 1) ^ 4)) hy (fun s hs => ?_)
    (fun s hs => by positivity)
  · simp only [sub_self, zero_mul, zero_div, log_one] at h
    linarith
  have hs0 : 0 < s := by linarith [hs.1]
  have hN : HasDerivAt (fun s : ℝ => (s - 1) * (3 * s ^ 4 + 68 * s ^ 3 + 98 * s ^ 2 + 68 * s + 3))
      (15 * s ^ 4 + 260 * s ^ 3 + 90 * s ^ 2 - 60 * s - 65) s := by
    have hp : HasDerivAt (fun s : ℝ => 3 * s ^ 4 + 68 * s ^ 3 + 98 * s ^ 2 + 68 * s + 3)
        (3 * (4 * s ^ 3) + 68 * (3 * s ^ 2) + 98 * (2 * s) + 68) s := by
      have := ((((((hasDerivAt_id' s).pow 4).const_mul (3 : ℝ)).add
        (((hasDerivAt_id' s).pow 3).const_mul (68 : ℝ))).add
        (((hasDerivAt_id' s).pow 2).const_mul (98 : ℝ))).add
        ((hasDerivAt_id' s).const_mul (68 : ℝ))).add_const (3 : ℝ)
      refine this.congr_deriv ?_
      push_cast; ring
    refine (((hasDerivAt_id' s).sub_const 1).mul hp).congr_deriv ?_
    ring
  have hD : HasDerivAt (fun s : ℝ => 30 * s * (s + 1) ^ 3)
      (30 * (s + 1) ^ 3 + 30 * s * (3 * (s + 1) ^ 2)) s := by
    have := ((hasDerivAt_id' s).const_mul (30 : ℝ)).mul (((hasDerivAt_id' s).add_const 1).pow 3)
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]; push_cast; ring
  have := (hN.div hD (by positivity)).sub (Real.hasDerivAt_log hs0.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- Positivity of `z⁴F₄ + z³F₃ + z²F₂ + zF₁ + F₀` for `0 < z ≤ 8`, `t ≥ 0`. -/
private theorem hsb_floor_poly {z t : ℝ} (hz : 0 < z) (hz8 : z ≤ 8) (ht : 0 ≤ t) :
    0 < z ^ 4 * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
      z ^ 3 * (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) +
      z ^ 2 * (4 * (42 * t ^ 4 + 413 * t ^ 3 + 537 * t ^ 2 - 1077 * t + 917)) +
      z * (80 * (14 * t ^ 3 + 49 * t ^ 2 - 64 * t + 45)) + 320 * (7 * t ^ 2 - 7 * t + 4) := by
  have hF0 : 0 < 320 * (7 * t ^ 2 - 7 * t + 4) := by linarith [sq_nonneg (t - 1 / 2)]
  have hF1 : 0 < 80 * (14 * t ^ 3 + 49 * t ^ 2 - 64 * t + 45) := by
    linarith [sq_nonneg (t - 32 / 49), pow_nonneg ht 3]
  have hF2 : 0 < 4 * (42 * t ^ 4 + 413 * t ^ 3 + 537 * t ^ 2 - 1077 * t + 917) := by
    linarith [sq_nonneg (t - 1077 / 1074), pow_nonneg ht 3, pow_nonneg ht 4]
  -- `F₃ = 728(t - 1)²(t + 2) + 147t⁴ + 202t² + 512t + 131`
  have hF3 : 0 < 147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587 := by
    linarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0 : ℝ) ≤ t + 2), pow_nonneg ht 4,
      sq_nonneg t]
  -- `8F₄ + F₃ = 339(t - 1)⁴ + 2572(t - 1)²t + 2264(t - 1)² - 672(t - 1) + 224`
  have hP8 : 0 < 339 * t ^ 4 + 1216 * t ^ 3 - 846 * t ^ 2 - 3984 * t + 3499 := by
    linarith [sq_nonneg ((t - 1) ^ 2), mul_nonneg (sq_nonneg (t - 1)) ht,
      sq_nonneg (t - 1 - 42 / 283)]
  have hlin : 0 < z * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
      (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) := by
    have e : z * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
        (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) =
        z / 8 * (339 * t ^ 4 + 1216 * t ^ 3 - 846 * t ^ 2 - 3984 * t + 3499) +
        (1 - z / 8) * (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) := by ring
    rw [e]
    have h1 : 0 < z / 8 * (339 * t ^ 4 + 1216 * t ^ 3 - 846 * t ^ 2 - 3984 * t + 3499) :=
      mul_pos (by positivity) hP8
    have h2 : 0 ≤ (1 - z / 8) * (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) :=
      mul_nonneg (by linarith) hF3.le
    linarith
  have e : z ^ 4 * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
      z ^ 3 * (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) =
      z ^ 3 * (z * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
      (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587)) := by ring
  rw [e]
  have := mul_pos (pow_pos hz 3) hlin
  have := mul_pos (pow_pos hz 2) hF2
  have := mul_pos hz hF1
  linarith

/-- **The uniform incoming floor**: `u_f(x) < Sec(1, x, β)` for `1 < x ≤ 9`, `x ≤ β`
(`2 artanh r < 2r + 2r³/3 + 2r⁵/(5(1 - r²))`, `r = (β - 1)/(β + 2x + 1)`, and the quartic identity
with `F₀, …, F₄`). -/
theorem hs_sec_gt_floor {x be : ℝ} (hx : 1 < x) (hx9 : x ≤ 9) (hxb : x ≤ be) :
    hsUf x < m2Sec 1 x be := by
  have hx0 : 0 < x := by linarith
  have hb1 : 0 < be - 1 := by linarith
  rw [m2Sec_of_ne (by linarith : (1 : ℝ) ≠ be)]
  have hy : 1 ≤ (be + x) / (1 + x) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hl := mul_le_mul_of_nonneg_left (hsb_log_le_atanh5 hy) (div_pos hx0 hb1).le
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ be = x + (x - 1) * t :=
    ⟨(be - x) / (x - 1), div_nonneg (by linarith) (by linarith), by
      field_simp [show x - 1 ≠ 0 by linarith]; ring⟩
  have hP := hsb_floor_poly (z := x - 1) (t := t) (by linarith) (by linarith) ht
  set P := (x - 1) ^ 4 * (24 * t ^ 4 + 61 * t ^ 3 - 131 * t ^ 2 - 289 * t + 239) +
      (x - 1) ^ 3 * (147 * t ^ 4 + 728 * t ^ 3 + 202 * t ^ 2 - 1672 * t + 1587) +
      (x - 1) ^ 2 * (4 * (42 * t ^ 4 + 413 * t ^ 3 + 537 * t ^ 2 - 1077 * t + 917)) +
      (x - 1) * (80 * (14 * t ^ 3 + 49 * t ^ 2 - 64 * t + 45)) + 320 * (7 * t ^ 2 - 7 * t + 4)
    with hPdef
  have hS : 0 < x + (x - 1) * t + x := by nlinarith
  have hR : 0 < x + (x - 1) * t + 2 * x + 1 := by nlinarith
  have key : 1 + x ^ 2 / ((1 + x) * (x + (x - 1) * t + x)) - x / (x + (x - 1) * t - 1) *
      (((x + (x - 1) * t + x) / (1 + x) - 1) * (3 * ((x + (x - 1) * t + x) / (1 + x)) ^ 4 +
        68 * ((x + (x - 1) * t + x) / (1 + x)) ^ 3 + 98 * ((x + (x - 1) * t + x) / (1 + x)) ^ 2 +
        68 * ((x + (x - 1) * t + x) / (1 + x)) + 3) /
        (30 * ((x + (x - 1) * t + x) / (1 + x)) * ((x + (x - 1) * t + x) / (1 + x) + 1) ^ 3)) -
      hsUf x = (x - 1) ^ 2 * P /
        (210 * (x + (x - 1) * t + x) * (x + 1) ^ 2 * (x + (x - 1) * t + 2 * x + 1) ^ 3) := by
    rw [hPdef]
    unfold hsUf
    have h1 : x + (x - 1) * t - 1 ≠ 0 := by linarith
    have h2 : 1 + x ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 < (x - 1) ^ 2 * P /
      (210 * (x + (x - 1) * t + x) * (x + 1) ^ 2 * (x + (x - 1) * t + 2 * x + 1) ^ 3) := by
    have : 0 < x - 1 := by linarith
    positivity
  linarith

/-! ### The reverse-centre scale bound -/

/-- **`ρ < 1/7` at a reverse centre** (the scalar core of `nh_a_sq`): if
`0 < r, t < 1/2`, `0 < ρ < rt`, `ρ < 3/20`, `3/4 ≤ u ≤ U(r)`, `3/4 ≤ v ≤ U(t)`,
`E = 1 + r + t - ρ + log(ρ/(rt)) - (1 - u)/r - (1 - v)/t` and `(4uv - E²)/(16(1 - ρ)²) <
9193/50000`, then `ρ < 1/7`. -/
theorem hs_rev_centre_scale {r t ρ u v E : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) (ht : 0 < t)
    (ht2 : t < 1 / 2) (hρ : 0 < ρ) (hρrt : ρ < r * t) (hρ320 : ρ < 3 / 20) (hu : 3 / 4 ≤ u)
    (hur : u ≤ m2U r) (hv : 3 / 4 ≤ v) (hvt : v ≤ m2U t)
    (hE : E = 1 + r + t - ρ + log (ρ / (r * t)) - (1 - u) / r - (1 - v) / t)
    (hΓ : (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) < 9193 / 50000) : ρ < 1 / 7 := by
  by_contra hcon
  push Not at hcon
  unfold m2U at hur hvt
  -- the diagonal bound `E < -1 + 2r + 2t - rt`
  have hEb : E < -1 + 2 * r + 2 * t - r * t := by
    have hℓ1 : -ρ + log (ρ / (r * t)) < -(r * t) := by
      set y := ρ / (r * t) with hy
      have hy0 : 0 < y := by positivity
      have hl := Real.log_le_sub_one_of_pos hy0
      have hy1 : y < 1 := (div_lt_one (by positivity)).2 hρrt
      have hrt1 : r * t < 1 := by
        have := mul_lt_mul'' hr2 ht2 hr.le ht.le; linarith only [this]
      have e : ρ = y * (r * t) := by rw [hy]; field_simp
      have e2 : (1 - y) * (1 - r * t) = 1 - r * t - y + ρ := by rw [e]; ring
      have : 0 < (1 - y) * (1 - r * t) :=
        mul_pos (by linarith only [hy1]) (by linarith only [hrt1])
      linarith only [hl, e2, this]
    have hur' : 1 - r ≤ (1 - u) / r := by
      rw [le_div_iff₀ hr]; linarith only [hur, show (1 - r) * r = r - r ^ 2 by ring]
    have hvt' : 1 - t ≤ (1 - v) / t := by
      rw [le_div_iff₀ ht]; linarith only [hvt, show (1 - t) * t = t - t ^ 2 by ring]
    rw [hE]
    linarith only [hℓ1, hur', hvt']
  -- lower the norms to `3/4`
  set E0 := 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ with hE0
  have hEE0 : E = E0 + (u - 3 / 4) / r + (v - 3 / 4) / t := by
    rw [hE, hE0]; field_simp; ring
  have hEr : E ≤ 2 * (3 / 4) * r := by
    have : (2 - r) * (t - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith only [hr2])
      (by linarith only [ht2])
    linarith only [hEb, this,
      show (2 - r) * (t - 1 / 2) = -1 + 2 * r + 2 * t - r * t - 3 / 2 * r by ring]
  have hEt : E ≤ 2 * (3 / 4) * t := by
    have : (2 - t) * (r - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith only [ht2])
      (by linarith only [hr2])
    linarith only [hEb, this,
      show (2 - t) * (r - 1 / 2) = -1 + 2 * r + 2 * t - r * t - 3 / 2 * t by ring]
  have hlow := nh_lower_norms hr ht hu hv hEr hEt hEE0
  have hρ14 : ρ < 1 / 4 := by linarith only [hρ320]
  have hE0pos : 0 < E0 := by
    have := nh_E0_lower hr ht hr2 ht2 hρ hρrt hρ14
    have h8 : 1 / (8 * ρ) ≤ 7 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith only [hcon]
    linarith only [this, h8, hcon, hE0]
  -- raise the ratios to `1/2`
  have hE0B : E0 ≤ 1 - ρ + Real.log (4 * ρ) := by
    have h1 := nh_phi34_mono hr hr2.le
    have h2 := nh_phi34_mono ht ht2.le
    have hφ : (1 / 2 : ℝ) - 1 / 4 * (1 / 2)⁻¹ - Real.log (1 / 2) = Real.log 2 := by
      rw [one_div, Real.log_inv]; norm_num
    rw [hφ] at h1 h2
    have e1 : E0 = 1 - ρ + Real.log ρ + (r - 1 / 4 * r⁻¹ - Real.log r) +
        (t - 1 / 4 * t⁻¹ - Real.log t) := by
      rw [hE0, Real.log_div hρ.ne' (by positivity), Real.log_mul hr.ne' ht.ne']; ring
    have e2 : Real.log (4 * ρ) = 2 * Real.log 2 + Real.log ρ := by
      rw [Real.log_mul (by norm_num) hρ.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e1, e2]; linarith only [h1, h2]
  -- the comparison function is increasing on `[1/7, 3/20]` and positive at `1/7`
  have hl35 : Real.log (4 * (3 / 20)) ≤ -(1 / 2) := by
    have := nh_log_five_thirds
    rw [show (4 : ℝ) * (3 / 20) = (5 / 3)⁻¹ by norm_num, Real.log_inv]; linarith only [this]
  have hphi := nh_phi_mono (C := 9 / 4) (D := 16 * (9193 / 50000)) (κ := 1) (lam := 4)
    (ρ0 := 1 / 7) (ρ1 := 3 / 20) (Bmax := 7 / 20) (ρ := ρ) (by norm_num) (by norm_num)
    (by norm_num) hcon hρ320.le (by norm_num) (by linarith only [hl35]) (by norm_num)
  have hl74 : (450606 / 805255 : ℝ) < Real.log (7 / 4) := by
    have := nh_log_one_add_gt3 (x := 3 / 4) (by norm_num)
    norm_num at this ⊢; linarith only [this]
  have hl74' : Real.log (7 / 4) ≤ 3 / 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 4 by norm_num); linarith only [this]
  have hB7 : 1 - 1 / 7 + Real.log (4 * (1 / 7)) = 6 / 7 - Real.log (7 / 4) := by
    rw [show (4 : ℝ) * (1 / 7) = (7 / 4)⁻¹ by norm_num, Real.log_inv]; ring
  rw [hB7] at hphi
  have hB7sq : (6 / 7 - Real.log (7 / 4)) ^ 2 ≤ (6 / 7 - 450606 / 805255) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hl74']) (by linarith only [hl74]) 2
  have hphi0 : 0 < 9 / 4 - (6 / 7 - Real.log (7 / 4)) ^ 2 -
      16 * (9193 / 50000) * (1 - 1 / 7) ^ 2 := by
    have : (0 : ℝ) < 9 / 4 - (6 / 7 - 450606 / 805255) ^ 2 -
        16 * (9193 / 50000) * (1 - 1 / 7) ^ 2 := by
      norm_num
    linarith only [this, hB7sq]
  -- conclude `Γ ≥ cap`
  have hE0sq : E0 ^ 2 ≤ (1 - ρ + Real.log (4 * ρ)) ^ 2 := pow_le_pow_left₀ hE0pos.le hE0B 2
  have h1ρ : 0 < 1 - ρ := by linarith only [hρ320]
  have hge : 16 * (9193 / 50000) * (1 - ρ) ^ 2 < 4 * u * v - E ^ 2 := by
    linarith only [hlow, hE0sq, hphi, hphi0]
  have : 9193 / 50000 < (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; linarith only [hge]
  linarith only [this, hΓ]

end SmoothedOctagon
