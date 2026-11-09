module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Defs

/-!
# Smaller-short window, upper ratio: the central x comparison, incoming norm and speed

Along `b = b_+(x, a)` the incoming norm `u = u_C(x, b)` has the representation
`u = 3/4 + v - (a - 1)W`, with
`v = 17(x - 1)²/(240S²)`, `L_β = b - 1 = x - 1 + c(a - 1)`, `c = (24x + 51)/128`,
`W = c(v - 1/3200)/L_β`, and its total x-derivative is `u_x = v_x - (a - 1)W_x`,
`W_x - 1/400 = Φ(L_β)/L_β²`. On the rectangle `13/6 ≤ x ≤ 12/5`, `1 ≤ a ≤ 4/3`:
`u ≤ U` and `u_x ≤ V`.

For `u ≤ U`, `L_β(W - 1/200) = c(v - 1/3200) - L_β/200` is affine and decreasing in `a`, and its
value at `a = 4/3` is a cubic in `X = x - 13/6` with positive coefficients. For the speed bound,
`Φ` is a concave quadratic in `L`, and its values at the two ends of the range of `L_β` are
explicit quintics in `x - 2`.

## Main API

* `urcxv`, `urcxvx`, `urcxLb`, `urcxW`, `urcxPhi`, `urcxup`.
* `urcx_bp_deriv`: `b_+` has x-derivative `ℓ`.
* `urcx_uC_eq`: the representation `u = 3/4 + v - (a - 1)W`. `urcx_uC_deriv`: `u_x = urcxup`.
* `urcx_u_le`, `urcx_up_le`: `u ≤ U`, `u_x ≤ V`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `v = 17(x - 1)²/(240S²)`. -/
noncomputable def urcxv (x : ℝ) : ℝ := 17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2)

/-- `v_x = 17(x - 1)/(60S³)`. -/
noncomputable def urcxvx (x : ℝ) : ℝ := 17 * (x - 1) / (60 * (1 + x) ^ 3)

/-- `L_β = b_+ - 1 = x - 1 + c(a - 1)`, `c = (24x + 51)/128`. -/
noncomputable def urcxLb (x a : ℝ) : ℝ := x - 1 + (24 * x + 51) / 128 * (a - 1)

/-- `W = c(v - 1/3200)/L_β`. -/
noncomputable def urcxW (x a : ℝ) : ℝ :=
  (24 * x + 51) / 128 * (urcxv x - 1 / 3200) / urcxLb x a

/-- `Φ(L) = c v_x L - (75/128)(v - 1/3200) - L²/400`. -/
noncomputable def urcxPhi (x L : ℝ) : ℝ :=
  (24 * x + 51) / 128 * urcxvx x * L - 75 / 128 * (urcxv x - 1 / 3200) - L ^ 2 / 400

/-- The incoming speed `u_x = v_x - (a - 1)W_x`, `W_x = 1/400 + Φ(L_β)/L_β²`. -/
noncomputable def urcxup (x a : ℝ) : ℝ :=
  urcxvx x - (a - 1) * (1 / 400 + urcxPhi x (urcxLb x a) / urcxLb x a ^ 2)

/-- `b_+(x, a)` has x-derivative `ℓ = (3a + 13)/16`. -/
theorem urcx_bp_deriv (a y : ℝ) : HasDerivAt (fun z => urcbp z a) (urcxl a) y := by
  have h := (hasDerivAt_id' y).fun_add ((((hasDerivAt_id' y).const_mul (24 : ℝ)).add_const
    (51 : ℝ)).mul_const (a - 1) |>.div_const (128 : ℝ))
  convert h using 1
  · rfl
  · unfold urcxl
    ring

theorem urcx_bp_sub (x a : ℝ) : urcbp x a - 1 = urcxLb x a := by
  unfold urcbp urcxLb
  ring

theorem urcx_bp_subx (x a : ℝ) : urcbp x a - x = (24 * x + 51) * (a - 1) / 128 := by
  unfold urcbp
  ring

/-- **The representation** `u = 3/4 + v - (a - 1)W`. -/
theorem urcx_uC_eq {x a : ℝ} (hS : 1 + x ≠ 0) (hL : urcxLb x a ≠ 0) :
    ssUC x (urcbp x a) = 3 / 4 + urcxv x - (a - 1) * urcxW x a := by
  unfold ssUC
  rw [urcx_bp_sub, urcx_bp_subx]
  unfold urcxW urcxv
  field_simp
  unfold urcxLb
  ring

/-- **The incoming speed**: along `b = b_+(x, a)`,
`u_C` has x-derivative `urcxup = v_x - (a - 1)(1/400 + Φ(L_β)/L_β²)`. -/
theorem urcx_uC_deriv {a y : ℝ} (hS : 1 + y ≠ 0) (hL : urcxLb y a ≠ 0) :
    HasDerivAt (fun z => ssUC z (urcbp z a)) (urcxup y a) y := by
  have hb := urcx_bp_deriv a y
  have hS' : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have hN := ((((hasDerivAt_id' y).sub_const 1).fun_pow 3).const_mul (680 : ℝ)).fun_add
    (((hS'.fun_pow 2).const_mul (3 : ℝ)).fun_mul (hb.fun_sub (hasDerivAt_id' y)))
  have hD := ((hS'.fun_pow 2).const_mul (9600 : ℝ)).fun_mul (hb.sub_const 1)
  have hD0 : 9600 * (1 + y) ^ 2 * (urcbp y a - 1) ≠ 0 := by
    rw [urcx_bp_sub]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hS)) hL
  have hq := (hN.fun_div hD hD0).const_add (3 / 4 : ℝ)
  convert hq using 1
  · rfl
  · simp only [Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one, mul_one]
    rw [urcx_bp_sub, urcx_bp_subx]
    unfold urcxup urcxPhi urcxvx urcxv urcxl
    field_simp
    unfold urcxLb
    ring

theorem urcx_Lb_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (ha : 1 ≤ a) : 0 < urcxLb x a := by
  unfold urcxLb
  have : 0 ≤ (24 * x + 51) / 128 * (a - 1) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **`u ≤ U`**:
`U - u = ((x - 1)/96 - 1/400 - v) + (a - 1)(W - 1/200)`, both brackets nonnegative. -/
theorem urcx_u_le {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    ssUC x (urcbp x a) ≤ urcxU x a := by
  have hS : 0 < 1 + x := by linarith
  have hL := urcx_Lb_pos hx ha
  rw [urcx_uC_eq hS.ne' hL.ne']
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  have hX : 0 ≤ X := by linarith
  -- `240S²((x - 1)/96 - 1/400 - v) = 5X³/2 + 23X²/20 + 3X/40 + 199/2160`
  have hv : urcxv (13 / 6 + X) ≤ (13 / 6 + X - 1) / 96 - 1 / 400 := by
    unfold urcxv
    rw [div_le_iff₀ (by positivity)]
    linarith [pow_nonneg hX 2, pow_nonneg hX 3]
  -- `30720S²(c(v - 1/3200 - 1/600) - (x - 1)/200) = 243X³ + 11439X²/8 + 12333X/8 + 3063/32`
  have hv2 : (13 / 6 + X - 1) / 200 ≤
      (24 * (13 / 6 + X) + 51) / 128 * (urcxv (13 / 6 + X) - 1 / 3200 - 1 / 600) := by
    have e : (24 * (13 / 6 + X) + 51) / 128 * (urcxv (13 / 6 + X) - 1 / 3200 - 1 / 600) =
        (24 * (13 / 6 + X) + 51) * (680 * (13 / 6 + X - 1) ^ 2 - 19 * (1 + (13 / 6 + X)) ^ 2) /
          (1228800 * (1 + (13 / 6 + X)) ^ 2) := by
      unfold urcxv
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith [pow_nonneg hX 2, pow_nonneg hX 3, pow_nonneg hX 4]
  have hW : 1 / 200 ≤ urcxW (13 / 6 + X) a := by
    unfold urcxW
    rw [le_div_iff₀ hL]
    unfold urcxLb
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ (24 * (13 / 6 + X) + 51) / 128)
      (by linarith : (0 : ℝ) ≤ 4 / 3 - a)
    linarith
  unfold urcxU
  have := mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hW)
  linarith

/-- **`u_x ≤ V`**:
`V - u_x = (1/96 - v_x) + (a - 1)Φ(L_β)/L_β²`; `v_x ≤ 1/96`, and `Φ` is a concave quadratic in
`L` whose values at the two ends `L = x - 1`, `x - 1 + c/3` of the range of `L_β` are
`p₀(Y)/(409600S³)`, `p₁(Y)/(6553600S³)`, `Y = x - 2`, with explicit quintics `p₀`, `p₁` that
are positive for `1/6 ≤ Y ≤ 2/5`. -/
theorem urcx_up_le {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    urcxup x a ≤ urcxV a := by
  have hS : 0 < 1 + x := by linarith
  obtain ⟨Y, rfl⟩ : ∃ Y, x = 2 + Y := ⟨x - 2, by ring⟩
  have hY : 1 / 6 ≤ Y := by linarith
  have hY' : Y ≤ 2 / 5 := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hp : ∀ n : ℕ, Y ^ n ≤ (2 / 5) ^ n := fun n => pow_le_pow_left₀ hY0 hY' n
  have hq : ∀ n : ℕ, 0 ≤ Y ^ n := fun n => pow_nonneg hY0 n
  -- `v_x ≤ 1/96`: `60S³ - 1632(x - 1) > 0`
  have hvx : urcxvx (2 + Y) ≤ 1 / 96 := by
    unfold urcxvx
    rw [div_le_iff₀ (by positivity)]
    linarith [hq 3, mul_nonneg hY0 (sub_nonneg.2 hY)]
  -- the two endpoint values
  have hP0 : 0 ≤ urcxPhi (2 + Y) (2 + Y - 1) := by
    have e : urcxPhi (2 + Y) (2 + Y - 1) = (13137 + 1361 * Y - 43205 * Y ^ 2 - 42269 * Y ^ 3 -
        11264 * Y ^ 4 - 1024 * Y ^ 5) / (409600 * (1 + (2 + Y)) ^ 3) := by
      unfold urcxPhi urcxvx urcxv
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    linarith [hp 2, hp 3, hp 4, hp 5]
  have hP1 : 0 ≤ urcxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) := by
    have e : urcxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) =
        (322953 + 16409 * Y - 930505 * Y ^ 2 - 820321 * Y ^ 3 - 210256 * Y ^ 4 -
          18496 * Y ^ 5) / (6553600 * (1 + (2 + Y)) ^ 3) := by
      unfold urcxPhi urcxvx urcxv
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    linarith [hp 2, hp 3, hp 4, hp 5]
  -- concavity in `L`: linear interpolation in `s = a - 1 ∈ [0, 1/3]` plus `c²s(1/3 - s)/400`
  have hPhi : 0 ≤ urcxPhi (2 + Y) (urcxLb (2 + Y) a) := by
    have e : urcxPhi (2 + Y) (urcxLb (2 + Y) a) =
        (1 - 3 * (a - 1)) * urcxPhi (2 + Y) (2 + Y - 1) +
          3 * (a - 1) * urcxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) +
          ((24 * (2 + Y) + 51) / 128) ^ 2 * ((a - 1) * (4 / 3 - a)) / 400 := by
      unfold urcxPhi urcxLb
      ring
    rw [e]
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 3 * (a - 1)) hP0
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (a - 1)) hP1
    have h3 : 0 ≤ ((24 * (2 + Y) + 51) / 128) ^ 2 * ((a - 1) * (4 / 3 - a)) / 400 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))) (by norm_num)
    linarith
  unfold urcxup urcxV
  have := mul_nonneg (sub_nonneg.2 ha) (div_nonneg hPhi (sq_nonneg (urcxLb (2 + Y) a)))
  linarith

end SmoothedOctagon
