module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.IncomingNorm

/-!
# Smaller-short window, Casimir floor: the Casimir part of the ratio derivative

With `S = 1 + x`, `X = x(x + 2)`, `M = S²(S² - S + 1)`, `E = S³(u - 1) + 3S - 1`, the Casimir
`Γ = (4Mu - E²)/(16X²)` has the partial derivatives

`Γ_x = ((4M_x u - 2EE_x)X - 4S(4Mu - E²))/(16X³)`, `Γ_u = (2M - ES³)/(8X²)`

(`cas_w3_G_deriv` gives the total derivative along a norm curve). On `2 ≤ x ≤ 13/6`,
`757/1000 ≤ u ≤ 19/25`:

* `Γ_x ≤ -17/2000`: `16X³(Γ_x + 17/2000) = -g₁(h)/625 + (2/25)(u - 19/25)G₁(h)
  - 2S⁵(X - 2)(u - 19/25)²`, where `G₁ = 200X³Γ_xu(x, 19/25)` is a polynomial in `h` and
  `g₁ = 72h⁷ + 1427h⁶ + 11862h⁵ + 51380h⁴ + 119190h³ + 138936h² + 63616h + 256`
  `= 10000X³(-Γ_x(x, 19/25) - 17/2000)`, `h = x - 2`, all coefficients positive;
* `0 ≤ Γ_u ≤ 41/200`: `8X²Γ_u = 32X²/25 + P_Γ(h)/25 + (19/25 - u)S⁶` with a polynomial
  `P_Γ` in `h`, and
  `8X²(41/200 - Γ_u) = g₂(h)/1000 + (u - 757/1000)S⁶`,
  `g₂ = 17813 - 73854h - 148965h² - 98540h³ - 30165h⁴ - 4374h⁵ - 243h⁶ > 0` for `h ≤ 1/6`.

Both bounds are one-variable signs in `h`: `g₁` gives the uniform bound `Γ_x ≤ -17/2000`, and
`g₂` bounds `Γ_u` at `u = 757/1000`.

## Main API

* `casW3Gx`, `casW3Gu`, `cas_w3_G_deriv`, `cas_w3_Gx_le`, `cas_w3_Gu_bounds`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `Γ_x = ((4M_x u - 2EE_x)X - 4S(4Mu - E²))/(16X³)`. -/
noncomputable def casW3Gx (x u : ℝ) : ℝ :=
  ((4 * (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) * u -
        2 * casClosedP x u * (3 * (1 + x) ^ 2 * (u - 1) + 3)) * (x * (x + 2)) -
      4 * (1 + x) * (4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) * u - casClosedP x u ^ 2)) /
    (16 * (x * (x + 2)) ^ 3)

/-- `Γ_u = (2M - ES³)/(8X²)`. -/
noncomputable def casW3Gu (x u : ℝ) : ℝ :=
  (2 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - casClosedP x u * (1 + x) ^ 3) /
    (8 * (x * (x + 2)) ^ 2)

/-- The total derivative of `Γ` along a norm curve `u = U(x)`. -/
theorem cas_w3_G_deriv {U : ℝ → ℝ} {U' x : ℝ} (hU : HasDerivAt U U' x) (hx : 0 < x) :
    HasDerivAt (fun x => casClosedG x (U x)) (casW3Gx x (U x) + casW3Gu x (U x) * U') x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hP := (((hS.fun_pow 3).fun_mul (hU.sub_const 1)).fun_add (hS.const_mul 3)).sub_const 1
  have hN := (((hU.const_mul 4).fun_mul (hS.fun_pow 2)).fun_mul
    (((hS.fun_pow 2).fun_sub hS).add_const 1)).fun_sub (hP.fun_pow 2)
  have hD := ((hasDerivAt_pow 2 x).const_mul 16).fun_mul
    (((hasDerivAt_id' x).add_const 2).fun_pow 2)
  have h2 : x + 2 ≠ 0 := by positivity
  have hx0 : x ≠ 0 := hx.ne'
  have := hN.fun_div hD (by positivity)
  refine this.congr_deriv ?_
  unfold casW3Gx casW3Gu casClosedP
  push_cast
  field_simp
  ring

/-- `Γ_x ≤ -17/2000` on `2 ≤ x`, `u ≤ 19/25`. -/
theorem cas_w3_Gx_le {x u : ℝ} (hx : 2 ≤ x) (hu' : u ≤ 19 / 25) :
    casW3Gx x u ≤ -17 / 2000 := by
  have h0 : 0 ≤ x - 2 := by linarith
  have e : ((4 * (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) * u -
        2 * casClosedP x u * (3 * (1 + x) ^ 2 * (u - 1) + 3)) * (x * (x + 2)) -
      4 * (1 + x) * (4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) * u - casClosedP x u ^ 2)) +
      17 / 125 * (x * (x + 2)) ^ 3 =
      -(72 * (x - 2) ^ 7 + 1427 * (x - 2) ^ 6 + 11862 * (x - 2) ^ 5 + 51380 * (x - 2) ^ 4 +
          119190 * (x - 2) ^ 3 + 138936 * (x - 2) ^ 2 + 63616 * (x - 2) + 256) / 625 +
        (u - 19 / 25) * (2 / 25) *
          (12 * (x - 2) ^ 7 + 252 * (x - 2) ^ 6 + 2232 * (x - 2) ^ 5 + 10825 * (x - 2) ^ 4 +
            31080 * (x - 2) ^ 3 + 52941 * (x - 2) ^ 2 + 49706 * (x - 2) + 19896) -
        2 * (1 + x) ^ 5 * (x * (x + 2) - 2) * (u - 19 / 25) ^ 2 := by
    unfold casClosedP
    ring
  have g1 : 0 ≤ 72 * (x - 2) ^ 7 + 1427 * (x - 2) ^ 6 + 11862 * (x - 2) ^ 5 + 51380 * (x - 2) ^ 4 +
      119190 * (x - 2) ^ 3 + 138936 * (x - 2) ^ 2 + 63616 * (x - 2) + 256 := by
    have := pow_nonneg h0 7; have := pow_nonneg h0 6; have := pow_nonneg h0 5
    have := pow_nonneg h0 4; have := pow_nonneg h0 3; have := pow_nonneg h0 2
    linarith
  have G1 : 0 ≤ 12 * (x - 2) ^ 7 + 252 * (x - 2) ^ 6 + 2232 * (x - 2) ^ 5 + 10825 * (x - 2) ^ 4 +
      31080 * (x - 2) ^ 3 + 52941 * (x - 2) ^ 2 + 49706 * (x - 2) + 19896 := by
    have := pow_nonneg h0 7; have := pow_nonneg h0 6; have := pow_nonneg h0 5
    have := pow_nonneg h0 4; have := pow_nonneg h0 3; have := pow_nonneg h0 2
    linarith
  have t1 : (u - 19 / 25) * (2 / 25) *
      (12 * (x - 2) ^ 7 + 252 * (x - 2) ^ 6 + 2232 * (x - 2) ^ 5 + 10825 * (x - 2) ^ 4 +
        31080 * (x - 2) ^ 3 + 52941 * (x - 2) ^ 2 + 49706 * (x - 2) + 19896) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) G1
  have t2 : 0 ≤ 2 * (1 + x) ^ 5 * (x * (x + 2) - 2) * (u - 19 / 25) ^ 2 := by
    have : 0 ≤ x * (x + 2) - 2 := by nlinarith
    have : 0 ≤ (1 + x) ^ 5 := by positivity
    positivity
  unfold casW3Gx
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `0 ≤ Γ_u ≤ 41/200` on `2 ≤ x ≤ 13/6`, `757/1000 ≤ u ≤ 19/25`. -/
theorem cas_w3_Gu_bounds {x u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hu : 757 / 1000 ≤ u)
    (hu' : u ≤ 19 / 25) : 0 ≤ casW3Gu x u ∧ casW3Gu x u ≤ 41 / 200 := by
  have h0 : 0 ≤ x - 2 := by linarith
  have h6 : x - 2 ≤ 1 / 6 := by linarith
  have eu : 41 / 200 * (8 * (x * (x + 2)) ^ 2) -
      (2 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - casClosedP x u * (1 + x) ^ 3) =
      (-243 * (x - 2) ^ 6 - 4374 * (x - 2) ^ 5 - 30165 * (x - 2) ^ 4 - 98540 * (x - 2) ^ 3 -
        148965 * (x - 2) ^ 2 - 73854 * (x - 2) + 17813) / 1000 +
        (u - 757 / 1000) * (1 + x) ^ 6 := by
    unfold casClosedP
    ring
  have el : 2 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - casClosedP x u * (1 + x) ^ 3 =
      32 / 25 * (x * (x + 2)) ^ 2 +
        (6 * (x - 2) ^ 6 + 108 * (x - 2) ^ 5 + 753 * (x - 2) ^ 4 + 2531 * (x - 2) ^ 3 +
          4101 * (x - 2) ^ 2 + 2601 * (x - 2) + 76) / 25 + (19 / 25 - u) * (1 + x) ^ 6 := by
    unfold casClosedP
    ring
  have g2 : 0 ≤ -243 * (x - 2) ^ 6 - 4374 * (x - 2) ^ 5 - 30165 * (x - 2) ^ 4 -
      98540 * (x - 2) ^ 3 - 148965 * (x - 2) ^ 2 - 73854 * (x - 2) + 17813 := by
    nlinarith [pow_le_pow_left₀ h0 h6 6, pow_le_pow_left₀ h0 h6 5, pow_le_pow_left₀ h0 h6 4,
      pow_le_pow_left₀ h0 h6 3, pow_le_pow_left₀ h0 h6 2]
  have pg : 0 ≤ 6 * (x - 2) ^ 6 + 108 * (x - 2) ^ 5 + 753 * (x - 2) ^ 4 + 2531 * (x - 2) ^ 3 +
      4101 * (x - 2) ^ 2 + 2601 * (x - 2) + 76 := by
    have := pow_nonneg h0 6; have := pow_nonneg h0 5
    have := pow_nonneg h0 4; have := pow_nonneg h0 3; have := pow_nonneg h0 2
    linarith
  have s6 : 0 ≤ (1 + x) ^ 6 := by positivity
  have t1 : 0 ≤ (u - 757 / 1000) * (1 + x) ^ 6 := mul_nonneg (by linarith) s6
  have t2 : 0 ≤ (19 / 25 - u) * (1 + x) ^ 6 := mul_nonneg (by linarith) s6
  have hX : 0 < 8 * (x * (x + 2)) ^ 2 := by positivity
  unfold casW3Gu
  refine ⟨div_nonneg ?_ hX.le, ?_⟩
  · rw [el]
    have : 0 ≤ 32 / 25 * (x * (x + 2)) ^ 2 := by positivity
    linarith
  · rw [div_le_iff₀ hX]
    linarith

end SmoothedOctagon
