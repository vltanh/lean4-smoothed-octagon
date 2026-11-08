module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandDefs

/-!
# Gate S4, hand proof W3 (a): the incoming norm on the shape curve and its `x`-slope

`archive/lighter-proofs/SHORT_CASIMIR_RATIO_DERIVATIVE.md` §1, (2)-(3). For fixed `d`, the incoming
upper norm on the shape curve `b = x(1 + d)` is

`U(x) = ū(x, x(1 + d)) = 3/4 + H₀/B₀ + xd³/(48B₀)`, `H₀ = 2(x - 1)³/(S(35x + 13))`,
`B₀ = x(1 + d) - 1`,

with `x`-slope `u_x = H₀'/B₀ - H₀(1 + d)/B₀² - d³/(48B₀²)` (`hl46_w3_U_deriv`). By note (3),
`u_x` decreases in `d` (`xH₀' ≥ 3H₀` and `B₀ ≥ 1`), so on `2 ≤ x ≤ 13/6`, `0 ≤ d ≤ 1/19`

`9/1000 ≤ u_x(x, 1/19) ≤ u_x ≤ u_x(x, 0) ≤ 1/100`

(`1/100 - u_x(x, 0) = I(h)/(100S²(35x + 13)²)` with the note's `I`, and
`u_x(x, 1/19) - 9/1000 = I₋(h)/(114000S²(20x - 19)²(35x + 13)²)` with the `I₋` of
`SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md` §1 (2), `h = x - 2`). Integrating from `x = 2` gives the
lower norm `U ≥ v = 379/500 + 9(x - 2)/1000 - 9d/500`, and `757/1000 ≤ U ≤ 19/25`.

Route: at `x = 2` the bound `U(2) ≥ v(2, d)` is the direct one-variable inequality
`(4 - 9d)(1 + 2d)/500 ≤ 2/249 + d³/24` (instead of integrating `u_d > -9/500`), and
`U ≤ 19/25` is the direct bound `H₀ + xd³/48 ≤ (x - 1)/100`.

## Main API

* `hl46W3H0`, `hl46W3H0p`, `hl46W3UX` (`u_x`), `hl46W3UXD` (`u_{xd}`), `hl46W3v` (`v`).
* `hl46_w3_U_deriv`, `hl46_w3_v_deriv`, `hl46_w3_UX_bounds`, `hl46_w3_U_ge_v`, `hl46_w3_U_le`,
  `hl46_w3_U_ge`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- `H₀ = 2(x - 1)³/(S(35x + 13))`. -/
noncomputable def hl46W3H0 (x : ℝ) : ℝ := 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))

/-- `H₀' = 2(x - 1)²(35x² + 166x + 87)/(S(35x + 13))²`. -/
noncomputable def hl46W3H0p (x : ℝ) : ℝ :=
  2 * (x - 1) ^ 2 * (35 * x ^ 2 + 166 * x + 87) / ((x + 1) * (35 * x + 13)) ^ 2

/-- `u_x = H₀'/B₀ - H₀(1 + d)/B₀² - d³/(48B₀²)`, `B₀ = x(1 + d) - 1`. -/
noncomputable def hl46W3UX (x d : ℝ) : ℝ :=
  hl46W3H0p x / (x * (1 + d) - 1) - hl46W3H0 x * (1 + d) / (x * (1 + d) - 1) ^ 2 -
    d ^ 3 / (48 * (x * (1 + d) - 1) ^ 2)

/-- `u_{xd}`, note (3), with `(1 + d)x + 1 = B₀ + 2`. -/
noncomputable def hl46W3UXD (x d : ℝ) : ℝ :=
  (-(x * hl46W3H0p x * (x * (1 + d) - 1)) + hl46W3H0 x * (x * (1 + d) - 1 + 2)) /
      (x * (1 + d) - 1) ^ 3 - d ^ 2 * (3 * (x - 1) + x * d) / (48 * (x * (1 + d) - 1) ^ 3)

/-- The affine lower norm `v = 379/500 + 9(x - 2)/1000 - 9d/500` of note (2). -/
noncomputable def hl46W3v (x d : ℝ) : ℝ := 379 / 500 + 9 / 1000 * (x - 2) - 9 / 500 * d

theorem hl46_w3_H0_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt hl46W3H0 (hl46W3H0p x) x := by
  have h1 : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
  have h2 : x + 1 ≠ 0 := by positivity
  have h3 : 35 * x + 13 ≠ 0 := by positivity
  have := ((((hasDerivAt_id' x).sub_const 1).fun_pow 3).const_mul 2).fun_div
    (((hasDerivAt_id' x).add_const 1).fun_mul (((hasDerivAt_id' x).const_mul 35).add_const 13)) h1
  refine this.congr_deriv ?_
  unfold hl46W3H0p
  push_cast
  field_simp
  ring

theorem hl46_w3_v_deriv (x d : ℝ) : HasDerivAt (fun x => hl46W3v x d) (9 / 1000) x := by
  have := ((((hasDerivAt_id' x).sub_const 2).const_mul (9 / 1000)).const_add (379 / 500)).sub_const
    (9 / 500 * d)
  refine this.congr_deriv ?_
  ring

/-- The `x`-slope of the incoming norm on the shape curve. -/
theorem hl46_w3_U_deriv {x d : ℝ} (hx : 2 ≤ x) (hd : 0 ≤ d) :
    HasDerivAt (fun x => hsUbar x (x * (1 + d))) (hl46W3UX x d) x := by
  have hx0 : 0 < x := by linarith
  have hx0' : x ≠ 0 := hx0.ne'
  have hB : x * (1 + d) - 1 ≠ 0 := by nlinarith
  have h2 : 48 * x ^ 2 ≠ 0 := by positivity
  have hH := hl46_w3_H0_deriv hx0
  have hW := ((((hasDerivAt_id' x).mul_const (1 + d)).fun_sub (hasDerivAt_id' x)).fun_pow 3).fun_div
    ((hasDerivAt_pow 2 x).const_mul 48) h2
  have hB' := ((hasDerivAt_id' x).mul_const (1 + d)).sub_const 1
  have := ((hH.fun_add hW).fun_div hB' hB).const_add (3 / 4)
  refine this.congr_deriv ?_
  unfold hl46W3UX
  push_cast
  field_simp
  ring

/-- The `d`-derivative of `u_x`. -/
theorem hl46_w3_UX_deriv_d {x d : ℝ} (hx : 2 ≤ x) (hd : 0 ≤ d) :
    HasDerivAt (fun d => hl46W3UX x d) (hl46W3UXD x d) d := by
  have hB : x * (1 + d) - 1 ≠ 0 := by nlinarith
  have hB0 : HasDerivAt (fun d => x * (1 + d) - 1) x d := by
    have := (((hasDerivAt_id' d).const_add 1).const_mul x).sub_const 1
    refine this.congr_deriv ?_
    ring
  have h1 := (hasDerivAt_const d (hl46W3H0p x)).fun_div hB0 hB
  have h2 := (((hasDerivAt_id' d).const_add 1).const_mul (hl46W3H0 x)).fun_div (hB0.fun_pow 2)
    (pow_ne_zero 2 hB)
  have h3 := (hasDerivAt_pow 3 d).fun_div ((hB0.fun_pow 2).const_mul 48)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hB))
  have := (h1.fun_sub h2).fun_sub h3
  refine this.congr_deriv ?_
  unfold hl46W3UXD
  push_cast
  field_simp
  ring

/-- `xH₀' ≥ 3H₀` on `[2, 13/6]` (note (3): `xH₀'/H₀ > 3`). -/
theorem hl46_w3_xH0p {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) :
    3 * hl46W3H0 x ≤ x * hl46W3H0p x := by
  have h2 : x + 1 ≠ 0 := by positivity
  have h3 : 35 * x + 13 ≠ 0 := by positivity
  have e : x * hl46W3H0p x - 3 * hl46W3H0 x =
      2 * (x - 1) ^ 2 * (-70 * x ^ 3 + 127 * x ^ 2 + 192 * x + 39) /
        ((x + 1) * (35 * x + 13)) ^ 2 := by
    unfold hl46W3H0 hl46W3H0p
    field_simp
    ring
  have hc : 0 ≤ -70 * x ^ 3 + 127 * x ^ 2 + 192 * x + 39 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 13 / 6 - x),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 13 / 6 - x))
        (by linarith : (0 : ℝ) ≤ x)]
  have : 0 ≤ x * hl46W3H0p x - 3 * hl46W3H0 x := by
    rw [e]
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hc
  linarith

/-- Note (3): `u_{xd} ≤ 0`. -/
theorem hl46_w3_UXD_nonpos {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) :
    hl46W3UXD x d ≤ 0 := by
  have hB : 1 ≤ x * (1 + d) - 1 := by nlinarith
  have hH0 : 0 ≤ hl46W3H0 x := by
    unfold hl46W3H0
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)) (by positivity)
  have key := hl46_w3_xH0p hx hx'
  unfold hl46W3UXD
  have hB3 : 0 < (x * (1 + d) - 1) ^ 3 := by positivity
  have t1 : (-(x * hl46W3H0p x * (x * (1 + d) - 1)) + hl46W3H0 x * (x * (1 + d) - 1 + 2)) /
      (x * (1 + d) - 1) ^ 3 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hB3.le
    nlinarith [mul_le_mul_of_nonneg_right key (by linarith : (0 : ℝ) ≤ x * (1 + d) - 1),
      mul_nonneg hH0 (by linarith : (0 : ℝ) ≤ x * (1 + d) - 1 - 1)]
  have t2 : 0 ≤ d ^ 2 * (3 * (x - 1) + x * d) / (48 * (x * (1 + d) - 1) ^ 3) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (sq_nonneg d) (by nlinarith)
  linarith

/-- `u_x(x, 0) ≤ 1/100`: `1/100 - u_x(x, 0) = I(h)/(100S²(35x + 13)²)`, all coefficients of `I`
positive (note §1). -/
theorem hl46_w3_UX0 {x : ℝ} (hx : 2 ≤ x) : hl46W3UX x 0 ≤ 1 / 100 := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h2 : x + 1 ≠ 0 := by linarith
  have h3 : 35 * x + 13 ≠ 0 := by linarith
  have e : 1 / 100 - hl46W3UX x 0 =
      (1225 * (x - 2) ^ 4 + 13160 * (x - 2) ^ 3 + 29174 * (x - 2) ^ 2 + 8024 * (x - 2) + 1) /
        (100 * (x + 1) ^ 2 * (35 * x + 13) ^ 2) := by
    unfold hl46W3UX hl46W3H0 hl46W3H0p
    simp only [add_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, sub_zero]
    field_simp
    ring
  have h0 : 0 ≤ x - 2 := by linarith
  have : 0 ≤ (1225 * (x - 2) ^ 4 + 13160 * (x - 2) ^ 3 + 29174 * (x - 2) ^ 2 + 8024 * (x - 2) + 1) /
      (100 * (x + 1) ^ 2 * (35 * x + 13) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith [pow_nonneg h0 4, pow_nonneg h0 3, pow_nonneg h0 2]
  linarith

/-- `u_x(x, 1/19) ≥ 9/1000`: the boundary curve slope, with the polynomial `I₋` of
`SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md` §1 (2). -/
theorem hl46_w3_UX19 {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) : 9 / 1000 ≤ hl46W3UX x (1 / 19) := by
  have h1 : x * (1 + 1 / 19) - 1 ≠ 0 := by nlinarith
  have h1' : 20 * x - 19 ≠ 0 := by linarith
  have h2 : x + 1 ≠ 0 := by linarith
  have h3 : 35 * x + 13 ≠ 0 := by linarith
  have e : hl46W3UX x (1 / 19) - 9 / 1000 =
      (-502740000 * (x - 2) ^ 6 - 6456618000 * (x - 2) ^ 5 - 23179547975 * (x - 2) ^ 4 -
        30704339320 * (x - 2) ^ 3 - 13549003994 * (x - 2) ^ 2 + 1159166376 * (x - 2) +
        1218893409) / (114000 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2) := by
    unfold hl46W3UX hl46W3H0 hl46W3H0p
    rw [show x * (1 + 1 / 19) - 1 = (20 * x - 19) / 19 by ring]
    have : x * 20 - 19 ≠ 0 := by linarith
    field_simp
    ring
  have h0 : 0 ≤ x - 2 := by linarith
  have h6 : x - 2 ≤ 1 / 6 := by linarith
  have : 0 ≤ (-502740000 * (x - 2) ^ 6 - 6456618000 * (x - 2) ^ 5 - 23179547975 * (x - 2) ^ 4 -
        30704339320 * (x - 2) ^ 3 - 13549003994 * (x - 2) ^ 2 + 1159166376 * (x - 2) +
        1218893409) / (114000 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith [pow_le_pow_left₀ h0 h6 6, pow_le_pow_left₀ h0 h6 5, pow_le_pow_left₀ h0 h6 4,
      pow_le_pow_left₀ h0 h6 3, pow_le_pow_left₀ h0 h6 2]
  linarith

/-- Note (2): `9/1000 ≤ u_x ≤ 1/100` on the full rectangle. -/
theorem hl46_w3_UX_bounds {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) : 9 / 1000 ≤ hl46W3UX x d ∧ hl46W3UX x d ≤ 1 / 100 := by
  have anti : ∀ {d₁ d₂ : ℝ}, 0 ≤ d₁ → d₁ ≤ d₂ → d₂ ≤ 1 / 19 → hl46W3UX x d₂ ≤ hl46W3UX x d₁ :=
    fun h1 h12 h2 => hl46_anti_of (f := fun d => hl46W3UX x d) (a := 0) (b := 1 / 19)
      (fun _ hd => hl46_w3_UX_deriv_d hx hd.1) (fun _ hd => hl46_w3_UXD_nonpos hx hx' hd.1)
      h1 h12 h2
  exact ⟨(hl46_w3_UX19 hx hx').trans (anti hd hd' le_rfl), (anti le_rfl hd hd').trans
    (hl46_w3_UX0 hx)⟩

/-- Note (2): the incoming norm dominates the affine lower norm `v`. -/
theorem hl46_w3_U_ge_v {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) : hl46W3v x d ≤ hsUbar x (x * (1 + d)) := by
  have hmono := hl46_mono_of (f := fun x => hsUbar x (x * (1 + d)) - hl46W3v x d)
    (f₁ := fun x => hl46W3UX x d - 9 / 1000) (a := 2) (b := 13 / 6)
    (fun y hy => (hl46_w3_U_deriv hy.1 hd).fun_sub (hl46_w3_v_deriv y d))
    (fun y hy => by linarith [(hl46_w3_UX_bounds hy.1 hy.2 hd hd').1]) le_rfl hx hx'
  have hd2 : 1 + 2 * d ≠ 0 := by linarith
  have key : hsUbar 2 (2 * (1 + d)) = 3 / 4 + (2 / 249 + d ^ 3 / 24) / (1 + 2 * d) := by
    unfold hsUbar
    have : 2 * (1 + d) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h2 : 4 / 500 - 9 * d / 500 ≤ (2 / 249 + d ^ 3 / 24) / (1 + 2 * d) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg hd 3]
  have hv2 : hl46W3v 2 d = 379 / 500 - 9 * d / 500 := by unfold hl46W3v; ring
  linarith

/-- `U ≤ 19/25`: `H₀ + xd³/48 ≤ (x - 1)/100 ≤ B₀/100`. -/
theorem hl46_w3_U_le {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    hsUbar x (x * (1 + d)) ≤ 19 / 25 := by
  have hx0 : x ≠ 0 := by linarith
  have hB : 1 ≤ x * (1 + d) - 1 := by nlinarith
  have e : (x * (1 + d) - x) ^ 3 / (48 * x ^ 2) = x * d ^ 3 / 48 := by
    field_simp
    ring
  have hH : 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) ≤ 97 / 10000 * (x - 1) := by
    rw [div_le_iff₀ (by positivity)]
    have hq : 16605 * x ^ 2 - 44656 * x + 18739 ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 13 / 6 - x)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) (by linarith : (0 : ℝ) ≤
      -(16605 * x ^ 2 - 44656 * x + 18739))]
  have hd3 : d ^ 3 ≤ (1 / 19) ^ 3 := pow_le_pow_left₀ hd hd' 3
  have hW : x * d ^ 3 / 48 ≤ 3 / 10000 * (x - 1) := by
    have : x * d ^ 3 ≤ 13 / 6 * (1 / 19) ^ 3 :=
      mul_le_mul hx' hd3 (pow_nonneg hd 3) (by norm_num)
    linarith
  unfold hsUbar
  rw [e]
  have : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + x * d ^ 3 / 48) / (x * (1 + d) - 1) ≤
      1 / 100 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `757/1000 ≤ U`, from `U ≥ v`. -/
theorem hl46_w3_U_ge {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    757 / 1000 ≤ hsUbar x (x * (1 + d)) := by
  have := hl46_w3_U_ge_v hx hx' hd hd'
  unfold hl46W3v at this
  linarith

end SmoothedOctagon
