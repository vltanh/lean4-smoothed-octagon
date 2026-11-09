module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandDefs

/-!
# Gate S4, hand proof W4: the incoming curve and the uniform Casimir slope

At `d = 1/19` the incoming curve is `U(x) = ū(x, 20x/19)`. With explicit numerators `I₋`, `I₊`:
`U' - 9/1000 = I₋(h)/(114000S²(20x - 19)²(35x + 13)²)`, `1/100 - U' = I₊(h)/(22800 …)`, so
`9/1000 < U' < 1/100`, hence `U > v = 757/1000 + 9(x - 2)/1000` and `U < 19/25`,
`U ≤ 7581/10000` for `x ≤ 25/12`.

For `Γ = (4Mu - E²)/(16X²)` the monotonicities follow from the exact expansions
in `u - 19/25` (`Γ` is quadratic in `u`):
`Γ_xu = G₁(h)/(200x³(x+2)³) - (u - 19/25)S⁵(X - 2)/(4X³)`,
`Γ_xx = -G₃(h)/(5000x⁴(x+2)⁴) + (u - 19/25)G₂(h)/(100x⁴(x+2)⁴) - (u - 19/25)²S⁴q(x)/(8X⁴)`,
`q = x⁴ + 4x³ + 2x² - 4x + 12`, with explicit positive polynomials `G₁, G₂, G₃`. So for `u ≤ 19/25`,
`Γ_xu > 0` and `Γ_xx < 0`; `Γ_u` is affine decreasing in `u`. With the four scalar values and the
single split `x = 25/12` this gives the uniform slope `Γ_x + Γ_u U' < -7/1000`.

## Main API

* `hl46W4Im`, `hl46W4Ip`, `hl46W4U1`, `hl46W4_U_deriv`, `hl46W4_U1_bounds`,
  `hl46W4_U_bounds`.
* `hl46W4Gx`, `hl46W4Gu`, `hl46W4Gxu`, `hl46W4Gxx`, `hl46W4G1`, `hl46W4G2`, `hl46W4G3`;
  `hl46W4_G_deriv` (chain rule for `Γ(x, φ(x))`), `hl46W4_Gx_deriv`, `hl46W4_Gu_deriv`,
  `hl46W4_Gx_sub`, `hl46W4_Gu_sub`, `hl46W4_Gxu_pos`, `hl46W4_Gxx_neg`.
* `hl46W4_Gamma_slope`: `Γ_x + Γ_u U' < -7/1000`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### The incoming curve -/

/-- `I₋(h)`. -/
noncomputable def hl46W4Im (h : ℝ) : ℝ :=
  -502740000 * h ^ 6 - 6456618000 * h ^ 5 - 23179547975 * h ^ 4 - 30704339320 * h ^ 3 -
    13549003994 * h ^ 2 + 1159166376 * h + 1218893409

/-- `I₊(h)`. -/
noncomputable def hl46W4Ip (h : ℝ) : ℝ :=
  111720000 * h ^ 6 + 1434804000 * h ^ 5 + 5381565925 * h ^ 4 + 8137767560 * h ^ 3 +
    5598968782 * h ^ 2 + 1896980472 * h + 379628973

/-- `U'(x) = 9/1000 + I₋(x - 2)/(114000 S²(20x - 19)²(35x + 13)²)`. -/
noncomputable def hl46W4U1 (x : ℝ) : ℝ :=
  9 / 1000 + hl46W4Im (x - 2) / (114000 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2)

/-- The derivative of the incoming curve `U(x) = ū(x, 20x/19)`. -/
theorem hl46W4_U_deriv {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun x => hsUbar x (x * (1 + 1 / 19))) (hl46W4U1 x) x := by
  have h1 : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
  have h2 : 48 * x ^ 2 ≠ 0 := by positivity
  have h3 : x * (1 + 1 / 19) - 1 ≠ 0 := by nlinarith
  have hb : HasDerivAt (fun x : ℝ => x * (1 + 1 / 19)) (1 + 1 / 19) x := by
    have := (hasDerivAt_id' x).mul_const (1 + 1 / 19)
    refine this.congr_deriv ?_; ring
  have hJ := ((((hasDerivAt_id' x).sub_const 1).fun_pow 3).const_mul 2).fun_div
    (((hasDerivAt_id' x).add_const 1).fun_mul (((hasDerivAt_id' x).const_mul 35).add_const 13)) h1
  have hT := ((hb.fun_sub (hasDerivAt_id' x)).fun_pow 3).fun_div
    ((hasDerivAt_pow 2 x).const_mul 48) h2
  have := ((hJ.fun_add hT).fun_div (hb.sub_const 1) h3).const_add (3 / 4)
  refine this.congr_deriv ?_
  unfold hl46W4U1 hl46W4Im
  have h4 : (20 * x - 19) ≠ 0 := by nlinarith
  have h4' : (x * 20 - 19) ≠ 0 := by nlinarith
  have h5 : (x + 1) ≠ 0 := by positivity
  have h6 : (35 * x + 13) ≠ 0 := by positivity
  have h7 : x ≠ 0 := by positivity
  push_cast
  rw [show x * (1 + 1 / 19) = 20 * x / 19 by ring]
  field_simp
  ring

/-- `9/1000 < U' < 1/100`. -/
theorem hl46W4_U1_bounds {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) :
    9 / 1000 < hl46W4U1 x ∧ hl46W4U1 x < 1 / 100 := by
  have hh : 0 ≤ x - 2 := by linarith
  have hh' : x - 2 ≤ 1 / 6 := by linarith
  have hden : 0 < 114000 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2 := by
    have : 0 < 20 * x - 19 := by linarith
    positivity
  have hIm : 0 < hl46W4Im (x - 2) := by
    unfold hl46W4Im
    linarith [pow_le_pow_left₀ hh hh' 2, pow_le_pow_left₀ hh hh' 3, pow_le_pow_left₀ hh hh' 4,
      pow_le_pow_left₀ hh hh' 5, pow_le_pow_left₀ hh hh' 6]
  have hIp : 0 < hl46W4Ip (x - 2) := by unfold hl46W4Ip; positivity
  have e : 1 / 100 - hl46W4U1 x =
      hl46W4Ip (x - 2) / (22800 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2) := by
    have : 20 * x - 19 ≠ 0 := by nlinarith
    have : x * 20 - 19 ≠ 0 := by nlinarith
    unfold hl46W4U1 hl46W4Im hl46W4Ip
    field_simp
    ring
  have h2 : 0 < hl46W4Ip (x - 2) /
      (22800 * (x + 1) ^ 2 * (20 * x - 19) ^ 2 * (35 * x + 13) ^ 2) := by
    have : 0 < 20 * x - 19 := by linarith
    positivity
  constructor
  · unfold hl46W4U1
    have := div_pos hIm hden
    linarith
  · linarith

/-- `v < U < 19/25`, and `U < 7581/10000` for `x ≤ 25/12`. -/
theorem hl46W4_U_bounds {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) :
    757 / 1000 + 9 / 1000 * (x - 2) < hsUbar x (x * (1 + 1 / 19)) ∧
      hsUbar x (x * (1 + 1 / 19)) < 19 / 25 ∧
      (x ≤ 25 / 12 → hsUbar x (x * (1 + 1 / 19)) < 7581 / 10000) := by
  have hd : ∀ y ∈ Icc (2 : ℝ) (13 / 6), HasDerivAt (fun x => hsUbar x (x * (1 + 1 / 19)))
      (hl46W4U1 y) y := fun y hy => hl46W4_U_deriv hy.1
  have mono : ∀ y z : ℝ, 2 ≤ y → y ≤ z → z ≤ 13 / 6 →
      hsUbar y (y * (1 + 1 / 19)) ≤ hsUbar z (z * (1 + 1 / 19)) :=
    fun y z hy hyz hz => hl46_mono_of hd
      (fun w hw => (by linarith [(hl46W4_U1_bounds hw.1 hw.2).1])) hy hyz hz
  have hv : ∀ y ∈ Icc (2 : ℝ) (13 / 6), HasDerivAt
      (fun x => hsUbar x (x * (1 + 1 / 19)) - (757 / 1000 + 9 / 1000 * (x - 2)))
      (hl46W4U1 y - 9 / 1000) y := fun y hy => by
    have := (hl46W4_U_deriv hy.1).fun_sub
      ((((hasDerivAt_id' y).sub_const 2).const_mul (9 / 1000)).const_add (757 / 1000))
    refine this.congr_deriv (by ring)
  have m2 := hl46_mono_of hv (fun w hw => (by linarith [(hl46W4_U1_bounds hw.1 hw.2).1]))
    (le_refl 2) hx hx'
  have u2 : 757 / 1000 < hsUbar 2 (2 * (1 + 1 / 19)) := by norm_num [hsUbar]
  have u3 : hsUbar (13 / 6) (13 / 6 * (1 + 1 / 19)) < 19 / 25 := by norm_num [hsUbar]
  have u4 : hsUbar (25 / 12) (25 / 12 * (1 + 1 / 19)) < 7581 / 10000 := by norm_num [hsUbar]
  refine ⟨?_, ?_, fun h => ?_⟩
  · linarith
  · linarith [mono x (13 / 6) hx hx' le_rfl]
  · linarith [mono x (25 / 12) hx h (by norm_num)]

/-! ### The Casimir slope -/

/-- `Γ_u = (2M - ES³)/(8X²)`. -/
noncomputable def hl46W4Gu (x u : ℝ) : ℝ :=
  (2 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - hh46S4P x u * (1 + x) ^ 3) /
    (8 * (x * (x + 2)) ^ 2)

/-- `Γ_x` (the quotient rule applied to `Γ = (4Mu - E²)/(16X²)`). -/
noncomputable def hl46W4Gx (x u : ℝ) : ℝ :=
  ((4 * u * (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) -
      2 * hh46S4P x u * (3 * (1 + x) ^ 2 * (u - 1) + 3)) * (x * (x + 2)) -
    2 * (2 * x + 2) * (4 * u * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - hh46S4P x u ^ 2)) /
    (16 * (x * (x + 2)) ^ 3)

/-- `G₁(h)`. -/
noncomputable def hl46W4G1 (h : ℝ) : ℝ :=
  12 * h ^ 7 + 252 * h ^ 6 + 2232 * h ^ 5 + 10825 * h ^ 4 + 31080 * h ^ 3 + 52941 * h ^ 2 +
    49706 * h + 19896

/-- `G₂(h)`. -/
noncomputable def hl46W4G2 (h : ℝ) : ℝ :=
  6 * h ^ 8 + 144 * h ^ 7 + 1488 * h ^ 6 + 8615 * h ^ 5 + 30495 * h ^ 4 + 67318 * h ^ 3 +
    89872 * h ^ 2 + 65604 * h + 19760

/-- `G₃(h)`. -/
noncomputable def hl46W4G3 (h : ℝ) : ℝ :=
  36 * h ^ 8 + 864 * h ^ 7 + 8928 * h ^ 6 + 54040 * h ^ 5 + 212595 * h ^ 4 + 544208 * h ^ 3 +
    854432 * h ^ 2 + 729024 * h + 252160

/-- `Γ_xu = Γ_xu(x, 19/25) + (u - 19/25)Γ_xuu`. -/
noncomputable def hl46W4Gxu (x u : ℝ) : ℝ :=
  hl46W4G1 (x - 2) / (200 * x ^ 3 * (x + 2) ^ 3) -
    (u - 19 / 25) * ((1 + x) ^ 5 * (x * (x + 2) - 2)) / (4 * (x * (x + 2)) ^ 3)

/-- `Γ_xx` in powers of `u - 19/25`. -/
noncomputable def hl46W4Gxx (x u : ℝ) : ℝ :=
  -hl46W4G3 (x - 2) / (5000 * x ^ 4 * (x + 2) ^ 4) +
    (u - 19 / 25) * hl46W4G2 (x - 2) / (100 * x ^ 4 * (x + 2) ^ 4) -
    (u - 19 / 25) ^ 2 * ((1 + x) ^ 4 * (x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 - 4 * x + 12)) /
      (8 * (x * (x + 2)) ^ 4)

/-- The chain rule `d/dx Γ(x, φ(x)) = Γ_x + Γ_u φ'`. -/
theorem hl46W4_G_deriv {φ : ℝ → ℝ} {φ' x : ℝ} (hx : 0 < x) (hφ : HasDerivAt φ φ' x) :
    HasDerivAt (fun x => hh46S4G x (φ x)) (hl46W4Gx x (φ x) + hl46W4Gu x (φ x) * φ') x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hP : HasDerivAt (fun x => hh46S4P x (φ x))
      (3 * (1 + x) ^ 2 * (φ x - 1) + (1 + x) ^ 3 * φ' + 3) x := by
    have := (((hS.fun_pow 3).fun_mul (hφ.sub_const 1)).fun_add (hS.const_mul 3)).sub_const 1
    refine this.congr_deriv ?_
    push_cast; ring
  have hN := ((((hφ.const_mul 4).fun_mul (hS.fun_pow 2)).fun_mul
    (((hS.fun_pow 2).fun_sub hS).add_const 1))).fun_sub (hP.fun_pow 2)
  have hD := (((hasDerivAt_pow 2 x).const_mul 16).fun_mul
    (((hasDerivAt_id' x).add_const 2).fun_pow 2))
  have := hN.fun_div hD (by positivity)
  refine this.congr_deriv ?_
  unfold hl46W4Gx hl46W4Gu
  push_cast
  field_simp
  ring

/-- `∂_x Γ_u = Γ_xu`. -/
theorem hl46W4_Gu_deriv (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => hl46W4Gu x u) (hl46W4Gxu x u) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hX : HasDerivAt (fun x : ℝ => x * (x + 2)) (2 * x + 2) x := by
    have := (hasDerivAt_id' x).fun_mul ((hasDerivAt_id' x).add_const 2)
    refine this.congr_deriv ?_; ring
  have hP : HasDerivAt (fun x => hh46S4P x u) (3 * (1 + x) ^ 2 * (u - 1) + 3) x := by
    have := (((hS.fun_pow 3).mul_const (u - 1)).fun_add (hS.const_mul 3)).sub_const 1
    refine this.congr_deriv ?_
    push_cast; ring
  have := ((((hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)).const_mul 2).fun_sub
    (hP.fun_mul (hS.fun_pow 3))).fun_div ((hX.fun_pow 2).const_mul 8) (by positivity)
  refine this.congr_deriv ?_
  unfold hl46W4Gxu hl46W4G1 hh46S4P
  push_cast
  field_simp
  ring

/-- `∂_x Γ_x = Γ_xx`. -/
theorem hl46W4_Gx_deriv (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => hl46W4Gx x u) (hl46W4Gxx x u) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have hX : HasDerivAt (fun x : ℝ => x * (x + 2)) (2 * x + 2) x := by
    have := (hasDerivAt_id' x).fun_mul ((hasDerivAt_id' x).add_const 2)
    refine this.congr_deriv ?_; ring
  have hP : HasDerivAt (fun x => hh46S4P x u) (3 * (1 + x) ^ 2 * (u - 1) + 3) x := by
    have := (((hS.fun_pow 3).mul_const (u - 1)).fun_add (hS.const_mul 3)).sub_const 1
    refine this.congr_deriv ?_
    push_cast; ring
  have hPx : HasDerivAt (fun x : ℝ => 3 * (1 + x) ^ 2 * (u - 1) + 3) (6 * (1 + x) * (u - 1)) x := by
    have := (((hS.fun_pow 2).const_mul 3).mul_const (u - 1)).add_const 3
    refine this.congr_deriv ?_
    push_cast; ring
  have hMx : HasDerivAt (fun x : ℝ => 4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x))
      (12 * (1 + x) ^ 2 - 6 * (1 + x) + 2) x := by
    have := (((hS.fun_pow 3).const_mul 4).fun_sub ((hS.fun_pow 2).const_mul 3)).fun_add
      (hS.const_mul 2)
    refine this.congr_deriv ?_
    push_cast; ring
  have hM : HasDerivAt (fun x : ℝ => (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))
      (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) x := by
    have := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
    refine this.congr_deriv ?_
    push_cast; ring
  have hN := ((((hMx.const_mul (4 * u)).fun_sub ((hP.const_mul 2).fun_mul hPx)).fun_mul hX).fun_sub
    ((((hasDerivAt_id' x).const_mul 2).add_const 2).const_mul 2 |>.fun_mul
      ((hM.const_mul (4 * u)).fun_sub (hP.fun_pow 2))))
  have := hN.fun_div ((hX.fun_pow 3).const_mul 16) (by positivity)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold hl46W4Gxx hl46W4G2 hl46W4G3 hh46S4P
    push_cast
    field_simp
    ring
  · unfold hl46W4Gx; ring

/-- `Γ_x` is quadratic in `u`: its increment is `Γ_xu` at the midpoint. -/
theorem hl46W4_Gx_sub {x : ℝ} (hx : 0 < x) (u₁ u₂ : ℝ) :
    hl46W4Gx x u₂ - hl46W4Gx x u₁ = (u₂ - u₁) * hl46W4Gxu x ((u₁ + u₂) / 2) := by
  unfold hl46W4Gx hl46W4Gxu hl46W4G1 hh46S4P
  field_simp
  ring

/-- `Γ_uu = -S⁶/(8X²)`. -/
theorem hl46W4_Gu_sub {x : ℝ} (hx : 0 < x) (u₁ u₂ : ℝ) :
    hl46W4Gu x u₂ - hl46W4Gu x u₁ = -((u₂ - u₁) * (1 + x) ^ 6 / (8 * (x * (x + 2)) ^ 2)) := by
  unfold hl46W4Gu hh46S4P
  field_simp
  ring

/-- `Γ_xu > 0` for `u ≤ 19/25`. -/
theorem hl46W4_Gxu_pos {x u : ℝ} (hx : 2 ≤ x) (hu : u ≤ 19 / 25) : 0 < hl46W4Gxu x u := by
  have hh : 0 ≤ x - 2 := by linarith
  have h1 : 0 < hl46W4G1 (x - 2) / (200 * x ^ 3 * (x + 2) ^ 3) := by
    unfold hl46W4G1; have : 0 < x := by linarith
    positivity
  have h2 : 0 ≤ (19 / 25 - u) * ((1 + x) ^ 5 * (x * (x + 2) - 2)) / (4 * (x * (x + 2)) ^ 3) := by
    have : 0 ≤ x * (x + 2) - 2 := by nlinarith
    have : 0 ≤ 19 / 25 - u := by linarith
    have : 0 < x := by linarith
    positivity
  unfold hl46W4Gxu
  have e : (u - 19 / 25) * ((1 + x) ^ 5 * (x * (x + 2) - 2)) / (4 * (x * (x + 2)) ^ 3) =
      -((19 / 25 - u) * ((1 + x) ^ 5 * (x * (x + 2) - 2)) / (4 * (x * (x + 2)) ^ 3)) := by ring
  rw [e]
  linarith

/-- `Γ_xx < 0` for `u ≤ 19/25`. -/
theorem hl46W4_Gxx_neg {x u : ℝ} (hx : 2 ≤ x) (hu : u ≤ 19 / 25) : hl46W4Gxx x u < 0 := by
  have hh : 0 ≤ x - 2 := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : 0 < hl46W4G3 (x - 2) / (5000 * x ^ 4 * (x + 2) ^ 4) := by
    unfold hl46W4G3; positivity
  have h2 : 0 ≤ (19 / 25 - u) * hl46W4G2 (x - 2) / (100 * x ^ 4 * (x + 2) ^ 4) := by
    have : 0 ≤ 19 / 25 - u := by linarith
    unfold hl46W4G2; positivity
  have h3 : 0 ≤ (u - 19 / 25) ^ 2 * ((1 + x) ^ 4 * (x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 - 4 * x + 12)) /
      (8 * (x * (x + 2)) ^ 4) := by
    have : 0 ≤ x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 - 4 * x + 12 := by nlinarith
    positivity
  unfold hl46W4Gxx
  have e : (u - 19 / 25) * hl46W4G2 (x - 2) / (100 * x ^ 4 * (x + 2) ^ 4) =
      -((19 / 25 - u) * hl46W4G2 (x - 2) / (100 * x ^ 4 * (x + 2) ^ 4)) := by ring
  rw [e, neg_div]
  linarith

/-- `Γ_x` increases in `u` below `19/25`. -/
theorem hl46W4_Gx_mono_u {x u v : ℝ} (hx : 2 ≤ x) (huv : u ≤ v) (hv : v ≤ 19 / 25) :
    hl46W4Gx x u ≤ hl46W4Gx x v := by
  have := hl46W4_Gx_sub (by linarith : (0 : ℝ) < x) u v
  have h := hl46W4_Gxu_pos (u := (u + v) / 2) hx (by linarith)
  nlinarith

/-- `Γ_x` decreases in `x` at fixed `u ≤ 19/25`. -/
theorem hl46W4_Gx_anti_x {u : ℝ} (hu : u ≤ 19 / 25) {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 13 / 6) : hl46W4Gx y u ≤ hl46W4Gx x u :=
  hl46_anti_of (a := 2) (b := 13 / 6) (fun z hz => hl46W4_Gx_deriv u (by linarith [hz.1]))
    (fun z hz => (hl46W4_Gxx_neg hz.1 hu).le) hx hxy hy

/-- `Γ_u` increases in `x` at fixed `u ≤ 19/25`. -/
theorem hl46W4_Gu_mono_x {u : ℝ} (hu : u ≤ 19 / 25) {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 13 / 6) : hl46W4Gu x u ≤ hl46W4Gu y u :=
  hl46_mono_of (a := 2) (b := 13 / 6) (fun z hz => hl46W4_Gu_deriv u (by linarith [hz.1]))
    (fun z hz => (hl46W4_Gxu_pos hz.1 hu).le) hx hxy hy

/-- `Γ_u` decreases in `u`. -/
theorem hl46W4_Gu_anti_u {x u v : ℝ} (hx : 0 < x) (huv : u ≤ v) : hl46W4Gu x v ≤ hl46W4Gu x u := by
  have := hl46W4_Gu_sub hx u v
  have : 0 ≤ (v - u) * (1 + x) ^ 6 / (8 * (x * (x + 2)) ^ 2) := by
    have : 0 ≤ v - u := by linarith
    positivity
  linarith

/-- **The uniform Casimir slope** `Γ_x + Γ_u p < -7/1000`, in abstract curve variables
`u = U(x)`, `p = U'`. -/
theorem hl46W4_Gamma_slope {x u p : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hu : 757 / 1000 ≤ u)
    (hu' : u ≤ 19 / 25) (hs : x ≤ 25 / 12 → u ≤ 7581 / 10000) (hp : 0 ≤ p) (hp' : p ≤ 1 / 100) :
    hl46W4Gx x u + hl46W4Gu x u * p < -7 / 1000 := by
  have hx0 : 0 < x := by linarith
  have g0 : 0 < hl46W4Gu 2 (19 / 25) := by norm_num [hl46W4Gu, hh46S4P]
  have gpos : 0 < hl46W4Gu x u := by
    have := hl46W4_Gu_anti_u hx0 hu'
    have := hl46W4_Gu_mono_x (u := 19 / 25) le_rfl (le_refl 2) hx hx'
    linarith
  have b1 : hl46W4Gu x u ≤ hl46W4Gu x (757 / 1000) := hl46W4_Gu_anti_u hx0 hu
  rcases le_total x (25 / 12) with h | h
  · have a1 := hl46W4_Gx_mono_u hx (hs h) (by norm_num)
    have a2 := hl46W4_Gx_anti_x (u := 7581 / 10000) (by norm_num) (le_refl 2) hx hx'
    have a3 : hl46W4Gx 2 (7581 / 10000) < -89 / 10000 := by norm_num [hl46W4Gx, hh46S4P]
    have b2 := hl46W4_Gu_mono_x (u := 757 / 1000) (by norm_num) hx h (by norm_num)
    have b3 : hl46W4Gu (25 / 12) (757 / 1000) < 187 / 1000 := by norm_num [hl46W4Gu, hh46S4P]
    have : hl46W4Gu x u * p ≤ 187 / 1000 * p := mul_le_mul_of_nonneg_right (by linarith) hp
    linarith
  · have a1 := hl46W4_Gx_mono_u hx hu' le_rfl
    have a2 := hl46W4_Gx_anti_x (u := 19 / 25) le_rfl (by norm_num : (2 : ℝ) ≤ 25 / 12) h hx'
    have a3 : hl46W4Gx (25 / 12) (19 / 25) < -19 / 2000 := by norm_num [hl46W4Gx, hh46S4P]
    have b2 := hl46W4_Gu_mono_x (u := 757 / 1000) (by norm_num) hx hx' le_rfl
    have b3 : hl46W4Gu (13 / 6) (757 / 1000) < 41 / 200 := by norm_num [hl46W4Gu, hh46S4P]
    have : hl46W4Gu x u * p ≤ 41 / 200 * p := mul_le_mul_of_nonneg_right (by linarith) hp
    linarith

end SmoothedOctagon
