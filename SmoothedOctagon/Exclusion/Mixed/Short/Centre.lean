module

public import SmoothedOctagon.Exclusion.Mixed.Short.Calc

/-!
# Case M2, smaller-short side: scalar consequences of reverse-centre stationarity

`MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION` §§3-4, `MIXED_GENERAL_SHORT_DEFECT_INTERFACE` (H),
(O), (10)-(11), `MIXED_GLOBAL_SHORT_BRIDGE_NONPOSITIVE_SCALE` (3), `MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE`
§2 (inventory E1 R9-R11, R18-R20, R23). At a reverse centre with neighbour ratios `x`, `y`
(`x = a/(a + n)`, `y = a/(a + p)`), incident norms `u_x`, `u_y`, scale `ρ = a²/(a² + 4) ≤ xy`
(positive reverse factor) and centre stationarity
`E = 1 + x + y - ρ + log(ρ/(xy)) - (1 - u_x)/x - (1 - u_y)/y`:

* `ss_E_le_three`: `E ≤ 3ρ` when `u_x ≤ U(x)`, `u_y ≤ U(y)`, `x, y ≤ 1/2` (R11, R23);
* `ss_gap_nonneg`: `(1 - ρ - u_y)x² + ρ(E - 1 + ρ)x + ρ(1 - ρ - u_x) = ρx(E - E_min) ≥ 0`
  when `u_y ≤ U(y)`, `y ≤ 1/2` (R18(a), R19 (O));
* `ss_E_upper`: `x²E ≤ x(u_x + u_y - 2) + 2x³ - ρx² + ρ` when `y ≤ x` (R20 (11));
* `ss_v_floor`: `x²(1 - u_y) - ρx + ρ² ≥ 0`, i.e. `u_y ≤ U(ρ/x)` (R20 (8));
* `ss_Rbar`: the convex-chord bound `R̄ ≥ 0` of the outer root (R9-R10), with `T = x/ρ`,
  `T_B = 1/x`, `τ = 1/y ∈ [2, T]` and `3/4 ≤ u_y ≤ U(y)`.

Here `U(s) = 1 - s + s²`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **`E ≤ 3ρ`** (`MIXED_GLOBAL_SHORT_BRIDGE_NONPOSITIVE_SCALE` (3), SIX_VARIABLE (10)). -/
theorem ss_E_le_three {x y ρ ux uy E : ℝ} (hx : 0 < x) (hx2 : x ≤ 1 / 2) (hy : 0 < y)
    (hy2 : y ≤ 1 / 2) (hρ : 0 < ρ) (hρxy : ρ ≤ x * y) (hux : ux ≤ 1 - x + x ^ 2)
    (huy : uy ≤ 1 - y + y ^ 2)
    (hE : E = 1 + x + y - ρ + Real.log (ρ / (x * y)) - (1 - ux) / x - (1 - uy) / y) :
    E ≤ 3 * ρ := by
  have h1 : -(1 - ux) / x ≤ x - 1 := by
    have : 1 - x ≤ (1 - ux) / x := by rw [le_div_iff₀ hx]; nlinarith
    rw [neg_div]; linarith
  have h2 : -(1 - uy) / y ≤ y - 1 := by
    have : 1 - y ≤ (1 - uy) / y := by rw [le_div_iff₀ hy]; nlinarith
    rw [neg_div]; linarith
  have hz : 0 < x * y := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hρ hz)
  have h3 : -1 + 2 * x + 2 * y ≤ 4 * (x * y) := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * x) (by linarith : (0 : ℝ) ≤ 1 - 2 * y)]
  have h4 : 4 * (x * y) + ρ / (x * y) - 1 - 4 * ρ = (4 * (x * y) - 1) * (x * y - ρ) / (x * y) := by
    field_simp
    ring
  have h5 : (4 * (x * y) - 1) * (x * y - ρ) / (x * y) ≤ 0 := by
    have : x * y ≤ 1 / 4 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) hz.le
  rw [hE]
  have : -(1 - ux) / x = -((1 - ux) / x) := neg_div _ _
  have : -(1 - uy) / y = -((1 - uy) / y) := neg_div _ _
  linarith

/-- **The central omitted-control filter** (`MIXED_GENERAL_SHORT_DEFECT_INTERFACE` (H), (O)):
`(1 - ρ - u_y)x² + ρ(E - 1 + ρ)x + ρ(1 - ρ - u_x) = ρx(E - E_min) ≥ 0`, since `E = 𝓔(y)` and
`𝓔' = (U(t) - u_y)/t² ≥ 0` on `[ρ/x, y]`; here via `log Y ≤ (Y - 1/Y)/2`, `Y = xy/ρ`. -/
theorem ss_gap_nonneg {x y ρ ux uy E : ℝ} (hx : 0 < x) (hy : 0 < y) (hy2 : y ≤ 1 / 2)
    (hρ : 0 < ρ) (hρxy : ρ ≤ x * y) (huy : uy ≤ 1 - y + y ^ 2)
    (hE : E = 1 + x + y - ρ + Real.log (ρ / (x * y)) - (1 - ux) / x - (1 - uy) / y) :
    0 ≤ (1 - ρ - uy) * x ^ 2 + ρ * (E - 1 + ρ) * x + ρ * (1 - ρ - ux) := by
  set Emin := (ux - 1) / x + (uy - 1) * x / ρ + 1 + x + ρ / x - ρ with hEmin
  have hid : (1 - ρ - uy) * x ^ 2 + ρ * (E - 1 + ρ) * x + ρ * (1 - ρ - ux) =
      ρ * x * (E - Emin) := by
    rw [hEmin]; field_simp; ring
  rw [hid]
  have hY : 1 ≤ x * y / ρ := by rw [le_div_iff₀ hρ]; linarith
  have hlog := ss_log_le_half hY
  have hl : Real.log (ρ / (x * y)) = -Real.log (x * y / ρ) := by
    rw [← Real.log_inv, inv_div]
  -- `E - E_min ≥ (Y - 1)(1 - y + t₀) - (Y - 1/Y)/2 ≥ 0`, `t₀ = ρ/x`
  have k1 : (1 - uy) * (x / ρ - 1 / y) ≥ (y - y ^ 2) * (x / ρ - 1 / y) := by
    have : 0 ≤ x / ρ - 1 / y := by
      rw [sub_nonneg, div_le_div_iff₀ hy hρ]; linarith
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have e1 : E - Emin = (1 - uy) * (x / ρ - 1 / y) + (y - ρ / x) - Real.log (x * y / ρ) := by
    rw [hE, hEmin, hl]; field_simp; ring
  have e2 : (y - y ^ 2) * (x / ρ - 1 / y) + (y - ρ / x) - (x * y / ρ - (x * y / ρ)⁻¹) / 2 =
      (x * y / ρ - 1) * ((1 / 2 - y) * (1 - ρ / (x * y))) := by
    field_simp; ring
  have e3 : 0 ≤ (x * y / ρ - 1) * ((1 / 2 - y) * (1 - ρ / (x * y))) := by
    have : 0 ≤ 1 - ρ / (x * y) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hρxy
    have : 0 ≤ x * y / ρ - 1 := by linarith
    have : 0 ≤ 1 / 2 - y := by linarith
    positivity
  have : 0 ≤ E - Emin := by linarith
  positivity

/-- **The rational upper pairing** (`MIXED_GENERAL_SHORT_DEFECT_INTERFACE` (11)): for `y ≤ x`,
`x²E ≤ x(u_x + u_y - 2) + 2x³ - ρx² + ρ`. -/
theorem ss_E_upper {x y ρ ux uy E : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hρ : 0 < ρ)
    (hρxy : ρ ≤ x * y) (huy : uy ≤ 1 - y + y ^ 2)
    (hE : E = 1 + x + y - ρ + Real.log (ρ / (x * y)) - (1 - ux) / x - (1 - uy) / y) :
    x ^ 2 * E ≤ x * (ux + uy - 2) + 2 * x ^ 3 - ρ * x ^ 2 + ρ := by
  have hx : 0 < x := by linarith
  have hz : 0 < x * y := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hρ hz)
  have hE1 : E ≤ x + y - ρ + ρ / (x * y) - (1 - ux) / x - (1 - uy) / y := by rw [hE]; linarith
  have hB : x + y - ρ + ρ / (x * y) - (1 - ux) / x - (1 - uy) / y ≤
      (x * (ux + uy - 2) + 2 * x ^ 3 - ρ * x ^ 2 + ρ) / x ^ 2 := by
    have e : (x * (ux + uy - 2) + 2 * x ^ 3 - ρ * x ^ 2 + ρ) / x ^ 2 -
        (x + y - ρ + ρ / (x * y) - (1 - ux) / x - (1 - uy) / y) =
        (x - y) * (x * y + 1 - uy - ρ / x) / (x * y) := by
      field_simp; ring
    have : 0 ≤ (x - y) * (x * y + 1 - uy - ρ / x) / (x * y) := by
      have h1 : ρ / x ≤ y := by rw [div_le_iff₀ hx]; linarith
      have h2 : 0 ≤ x * y + 1 - uy - ρ / x := by nlinarith
      have h3 : 0 ≤ x - y := by linarith
      positivity
    linarith
  have := le_trans hE1 hB
  rw [le_div_iff₀ (by positivity)] at this
  linarith

/-- **The opposite-norm floor** (SIX_VARIABLE (8)): `u_y ≤ U(y)`, `ρ/x ≤ y ≤ 1/2` give
`x²(1 - u_y) - ρx + ρ² ≥ 0`. -/
theorem ss_v_floor {x y ρ uy : ℝ} (hx : 0 < x) (hy2 : y ≤ 1 / 2) (hρxy : ρ ≤ x * y)
    (huy : uy ≤ 1 - y + y ^ 2) : 0 ≤ x ^ 2 * (1 - uy) - ρ * x + ρ ^ 2 := by
  have e : x ^ 2 * (y - y ^ 2) - ρ * x + ρ ^ 2 = (x * y - ρ) * (x * (1 - y) - ρ) := by ring
  have h1 : 0 ≤ x * y - ρ := by linarith
  have h2 : 0 ≤ x * (1 - y) - ρ := by nlinarith
  have : x ^ 2 * (y - y ^ 2) ≤ x ^ 2 * (1 - uy) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [mul_nonneg h1 h2]

private lemma ss_Rbar_alg1 {T τ : ℝ} (hT : 0 < T) (hτ : 0 < τ) :
    2 * (T / τ - 1) / (T / τ + 1) - 1 + 2 / T - 1 / τ + (1 - (1 - 1 / T + 1 / T ^ 2)) * τ =
      (T - τ) ^ 2 * (τ * T - T - τ) / (τ * T ^ 2 * (T + τ)) := by
  field_simp
  ring

private lemma ss_Rbar_alg2 {T : ℝ} (hT : 0 < T) :
    (2 * (1 + (T - 2) / (T + 2)) + 2 / 3 * ((T - 2) / (T + 2)) * (1 + (T - 2) / (T + 2)) ^ 2) *
        ((1 - 1 / T + 1 / T ^ 2) - 3 / 4) - 2 * ((T - 2) / (T + 2)) -
      2 / 3 * ((T - 2) / (T + 2)) ^ 3 = -1 + 2 / T := by
  field_simp
  ring

/-- **The outer-root chord bound** (`MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE` (2)-(3),
SIX_VARIABLE (13), inventory E1 R9-R10). At a reverse centre with `x = 1/T_B`, `y = 1/τ`,
`2 ≤ τ ≤ T = x/ρ`, `3/4 ≤ u_y ≤ U(y)` and stationarity `E`, the rational upper bound of the outer
residual is nonnegative:
`m₀(u_y - 3/4) + (u_x - 1)/x + 1 + x - ρ - E - 2ζ - (2/3)ζ³ ≥ 0`, `ζ = (1 - 2ρ/x)/(1 + 2ρ/x)`,
`m₀ = 2(1 + ζ) + (2/3)ζ(1 + ζ)²`.

Route: the residual is affine in `u_y`, so it suffices to check `u_y = 3/4`
(`log(T/2) ≥ 2ζ + (2/3)ζ³`, `log(τ/2) ≤ τ/4 - 1/τ`) and `u_y = U(1/T)` (where it is
`φ(T) - φ(τ) ≥ 0` for the concave `φ(t) = (u_y - 1)t + 1/t + log t`); this replaces the Legendre
transform of the notes. -/
theorem ss_Rbar {x y ρ ux uy E : ℝ} (hx : 0 < x) (hy : 0 < y) (hy2 : y ≤ 1 / 2) (hρ : 0 < ρ)
    (hρxy : ρ ≤ x * y) (huy1 : 3 / 4 ≤ uy) (huy2 : uy ≤ 1 - y + y ^ 2)
    (hE : E = 1 + x + y - ρ + Real.log (ρ / (x * y)) - (1 - ux) / x - (1 - uy) / y) :
    0 ≤ (2 * (1 + (1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x))) + 2 / 3 * ((1 - 2 * (ρ / x)) /
        (1 + 2 * (ρ / x))) * (1 + (1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x))) ^ 2) * (uy - 3 / 4) +
      (ux - 1) / x + 1 + x - ρ - E - 2 * ((1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x))) -
      2 / 3 * ((1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x))) * ((1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x))) ^ 2 := by
  -- `T = x/ρ`, `τ = 1/y`
  obtain ⟨T, hT⟩ : ∃ T, T = x / ρ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = 1 / y := ⟨_, rfl⟩
  have hτ2 : 2 ≤ τ := by rw [hτ, le_div_iff₀ hy]; linarith
  have hτT : τ ≤ T := by
    rw [hτ, hT, div_le_div_iff₀ hy hρ]; linarith
  have hT0 : 0 < T := by linarith
  have hτ0 : 0 < τ := by linarith
  have hρx : ρ / x = 1 / T := by rw [hT]; field_simp
  have hy' : y = 1 / τ := by rw [hτ]; field_simp
  have hlogE : Real.log (ρ / (x * y)) = -Real.log (T / τ) := by
    rw [← Real.log_inv, inv_div, hT, hτ]
    congr 1
    field_simp
  -- the residual in `(T, τ, uy)`
  set ζ := (T - 2) / (T + 2) with hζ
  have hζ' : (1 - 2 * (ρ / x)) / (1 + 2 * (ρ / x)) = ζ := by
    rw [hρx, hζ]; field_simp
  rw [hζ']
  set m0 := 2 * (1 + ζ) + 2 / 3 * ζ * (1 + ζ) ^ 2 with hm0
  have hres : m0 * (uy - 3 / 4) + (ux - 1) / x + 1 + x - ρ - E - 2 * ζ - 2 / 3 * ζ * ζ ^ 2 =
      m0 * (uy - 3 / 4) - 2 * ζ - 2 / 3 * ζ ^ 3 - 1 / τ + Real.log (T / τ) + (1 - uy) * τ := by
    rw [hE, hlogE, hy']
    field_simp
    ring
  rw [hres]
  have hlogsplit : Real.log (T / τ) = Real.log (T / 2) - Real.log (τ / 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rcases le_or_gt τ m0 with hm | hm
  · -- the residual increases with `uy`: evaluate at `uy = 3/4`
    have hc := ss_log_ge_cubic (z := T / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
    have hcz : (T / 2 - 1) / (T / 2 + 1) = ζ := by rw [hζ]; field_simp
    rw [hcz] at hc
    have hh := ss_log_le_half (z := τ / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
    have hh' : (τ / 2 - (τ / 2)⁻¹) / 2 = τ / 4 - 1 / τ := by field_simp; ring
    rw [hh'] at hh
    have : 0 ≤ (m0 - τ) * (uy - 3 / 4) := mul_nonneg (by linarith) (by linarith)
    have e : m0 * (uy - 3 / 4) + (1 - uy) * τ = (m0 - τ) * (uy - 3 / 4) + τ / 4 := by ring
    linarith
  · -- the residual decreases with `uy`: evaluate at `uy = U(1/T) ≥ U(y)`
    set w1 := 1 - 1 / T + 1 / T ^ 2 with hw1
    have hUU : uy ≤ w1 := by
      have : 1 - y + y ^ 2 ≤ w1 := by
        rw [hw1, hy']
        have e : 1 - 1 / T + 1 / T ^ 2 - (1 - 1 / τ + (1 / τ) ^ 2) =
            (1 / τ - 1 / T) * (1 - 1 / T - 1 / τ) := by ring
        have h1 : 0 ≤ 1 / τ - 1 / T := by
          rw [sub_nonneg, div_le_div_iff₀ hT0 hτ0]; linarith
        have h2 : 0 ≤ 1 - 1 / T - 1 / τ := by
          have : 1 / T ≤ 1 / 2 := by rw [div_le_div_iff₀ hT0 (by norm_num)]; linarith
          have : 1 / τ ≤ 1 / 2 := by rw [div_le_div_iff₀ hτ0 (by norm_num)]; linarith
          linarith
        nlinarith [mul_nonneg h1 h2]
      linarith
    have hmono : m0 * (w1 - 3 / 4) + (1 - w1) * τ ≤ m0 * (uy - 3 / 4) + (1 - uy) * τ := by
      have := mul_nonneg_of_nonpos_of_nonpos (by linarith : m0 - τ ≤ 0) (by linarith : uy - w1 ≤ 0)
      have e : m0 * (uy - 3 / 4) + (1 - uy) * τ - (m0 * (w1 - 3 / 4) + (1 - w1) * τ) =
          (m0 - τ) * (uy - w1) := by ring
      linarith
    have hid : m0 * (w1 - 3 / 4) - 2 * ζ - 2 / 3 * ζ ^ 3 = -1 + 2 / T := by
      rw [hm0, hw1, hζ]; exact ss_Rbar_alg2 hT0
    -- `log(T/τ) ≥ 2(Y - 1)/(Y + 1)`, `Y = T/τ`
    have hY : 1 ≤ T / τ := by rw [le_div_iff₀ hτ0]; linarith
    have hp := ss_log_ge_pade hY
    have key : 0 ≤ 2 * (T / τ - 1) / (T / τ + 1) - 1 + 2 / T - 1 / τ + (1 - w1) * τ := by
      rw [hw1, ss_Rbar_alg1 hT0 hτ0]
      have : 0 ≤ τ * T - T - τ := by
        have e : τ * T - T - τ = (τ - 2) * (T - 2) + (τ - 2) + (T - 2) := by ring
        rw [e]
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ τ - 2) (by linarith : (0 : ℝ) ≤ T - 2)
        linarith
      positivity
    linarith

end SmoothedOctagon
