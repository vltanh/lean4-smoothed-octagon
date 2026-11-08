module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXDefs

/-!
# S2 hand signs: the central x comparison, incoming norm and speed

`archive/lighter-proofs/SHORT_RATIO_CENTRAL_X.md` §2: along `b = b_+(x, a)` the incoming norm
`u = u_C(x, b)` has the representation `u = 3/4 + v - (a - 1)W` (9), with
`v = 17(x - 1)²/(240S²)`, `L_β = b - 1 = x - 1 + c(a - 1)`, `c = (24x + 51)/128`,
`W = c(v - 1/3200)/L_β`, and its total x-derivative is `u_x = v_x - (a - 1)W_x`,
`W_x - 1/400 = Φ(L_β)/L_β²` (10)-(11). On the rectangle `13/6 ≤ x ≤ 12/5`, `1 ≤ a ≤ 4/3`:
`u ≤ U` and `u_x ≤ V` (8).

Route for `u ≤ U`: the note obtains `W ≥ 1/200` from the monotonicity of `W` in `x` and `a`
((10)-(13)); here `L_β(W - 1/200) = c(v - 1/3200) - L_β/200` is affine and decreasing in `a`, and
its value at `a = 4/3` is a cubic in `X = x - 13/6` with positive coefficients. The speed bound
follows the note: `Φ` is a concave quadratic in `L`, and its endpoint values are the printed
quintics `p₀`, `p₁` of (12).

## Main API

* `hl2cxv`, `hl2cxvx`, `hl2cxLb`, `hl2cxW`, `hl2cxPhi`, `hl2cxup` (§2).
* `hl2cx_bp_deriv`: `b_+` has x-derivative `ℓ`.
* `hl2cx_uC_eq`: the representation (9). `hl2cx_uC_deriv`: `u_x = hl2cxup`.
* `hl2cx_u_le`, `hl2cx_up_le`: `u ≤ U`, `u_x ≤ V` (8).
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `v = 17(x - 1)²/(240S²)` (`SHORT_RATIO_CENTRAL_X` §2). -/
noncomputable def hl2cxv (x : ℝ) : ℝ := 17 * (x - 1) ^ 2 / (240 * (1 + x) ^ 2)

/-- `v_x = 17(x - 1)/(60S³)` (`SHORT_RATIO_CENTRAL_X` §2). -/
noncomputable def hl2cxvx (x : ℝ) : ℝ := 17 * (x - 1) / (60 * (1 + x) ^ 3)

/-- `L_β = b_+ - 1 = x - 1 + c(a - 1)`, `c = (24x + 51)/128`. -/
noncomputable def hl2cxLb (x a : ℝ) : ℝ := x - 1 + (24 * x + 51) / 128 * (a - 1)

/-- `W = c(v - 1/3200)/L_β` (`SHORT_RATIO_CENTRAL_X` §2). -/
noncomputable def hl2cxW (x a : ℝ) : ℝ :=
  (24 * x + 51) / 128 * (hl2cxv x - 1 / 3200) / hl2cxLb x a

/-- `Φ(L) = c v_x L - (75/128)(v - 1/3200) - L²/400` (`SHORT_RATIO_CENTRAL_X` (11)). -/
noncomputable def hl2cxPhi (x L : ℝ) : ℝ :=
  (24 * x + 51) / 128 * hl2cxvx x * L - 75 / 128 * (hl2cxv x - 1 / 3200) - L ^ 2 / 400

/-- The incoming speed `u_x = v_x - (a - 1)W_x`, `W_x = 1/400 + Φ(L_β)/L_β²` (9)-(11). -/
noncomputable def hl2cxup (x a : ℝ) : ℝ :=
  hl2cxvx x - (a - 1) * (1 / 400 + hl2cxPhi x (hl2cxLb x a) / hl2cxLb x a ^ 2)

/-- `b_+(x, a)` has x-derivative `ℓ = (3a + 13)/16`. -/
theorem hl2cx_bp_deriv (a y : ℝ) : HasDerivAt (fun z => hl2cbp z a) (hl2cxl a) y := by
  have h := (hasDerivAt_id' y).fun_add ((((hasDerivAt_id' y).const_mul (24 : ℝ)).add_const
    (51 : ℝ)).mul_const (a - 1) |>.div_const (128 : ℝ))
  convert h using 1
  · rfl
  · unfold hl2cxl
    ring

theorem hl2cx_bp_sub (x a : ℝ) : hl2cbp x a - 1 = hl2cxLb x a := by
  unfold hl2cbp hl2cxLb
  ring

theorem hl2cx_bp_subx (x a : ℝ) : hl2cbp x a - x = (24 * x + 51) * (a - 1) / 128 := by
  unfold hl2cbp
  ring

/-- **The representation (9)** `u = 3/4 + v - (a - 1)W`. -/
theorem hl2cx_uC_eq {x a : ℝ} (hS : 1 + x ≠ 0) (hL : hl2cxLb x a ≠ 0) :
    hsUC x (hl2cbp x a) = 3 / 4 + hl2cxv x - (a - 1) * hl2cxW x a := by
  unfold hsUC
  rw [hl2cx_bp_sub, hl2cx_bp_subx]
  unfold hl2cxW hl2cxv
  field_simp
  unfold hl2cxLb
  ring

/-- **The incoming speed** (`SHORT_RATIO_CENTRAL_X` (9)-(11)): along `b = b_+(x, a)`,
`u_C` has x-derivative `hl2cxup = v_x - (a - 1)(1/400 + Φ(L_β)/L_β²)`. -/
theorem hl2cx_uC_deriv {a y : ℝ} (hS : 1 + y ≠ 0) (hL : hl2cxLb y a ≠ 0) :
    HasDerivAt (fun z => hsUC z (hl2cbp z a)) (hl2cxup y a) y := by
  have hb := hl2cx_bp_deriv a y
  have hS' : HasDerivAt (fun z => 1 + z) 1 y := (hasDerivAt_id' y).const_add 1
  have hN := ((((hasDerivAt_id' y).sub_const 1).fun_pow 3).const_mul (680 : ℝ)).fun_add
    (((hS'.fun_pow 2).const_mul (3 : ℝ)).fun_mul (hb.fun_sub (hasDerivAt_id' y)))
  have hD := ((hS'.fun_pow 2).const_mul (9600 : ℝ)).fun_mul (hb.sub_const 1)
  have hD0 : 9600 * (1 + y) ^ 2 * (hl2cbp y a - 1) ≠ 0 := by
    rw [hl2cx_bp_sub]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hS)) hL
  have hq := (hN.fun_div hD hD0).const_add (3 / 4 : ℝ)
  convert hq using 1
  · rfl
  · simp only [Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one, mul_one]
    rw [hl2cx_bp_sub, hl2cx_bp_subx]
    unfold hl2cxup hl2cxPhi hl2cxvx hl2cxv hl2cxl
    field_simp
    unfold hl2cxLb
    ring

theorem hl2cx_Lb_pos {x a : ℝ} (hx : 13 / 6 ≤ x) (ha : 1 ≤ a) : 0 < hl2cxLb x a := by
  unfold hl2cxLb
  have : 0 ≤ (24 * x + 51) / 128 * (a - 1) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **`u ≤ U`** (`SHORT_RATIO_CENTRAL_X` (8)):
`U - u = ((x - 1)/96 - 1/400 - v) + (a - 1)(W - 1/200)`, both brackets nonnegative. -/
theorem hl2cx_u_le {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    hsUC x (hl2cbp x a) ≤ hl2cxU x a := by
  have hS : 0 < 1 + x := by linarith
  have hL := hl2cx_Lb_pos hx ha
  rw [hl2cx_uC_eq hS.ne' hL.ne']
  obtain ⟨X, rfl⟩ : ∃ X, x = 13 / 6 + X := ⟨x - 13 / 6, by ring⟩
  have hX : 0 ≤ X := by linarith
  -- `240S²((x - 1)/96 - 1/400 - v) = 5X³/2 + 23X²/20 + 3X/40 + 199/2160`
  have hv : hl2cxv (13 / 6 + X) ≤ (13 / 6 + X - 1) / 96 - 1 / 400 := by
    unfold hl2cxv
    rw [div_le_iff₀ (by positivity)]
    linarith [pow_nonneg hX 2, pow_nonneg hX 3]
  -- `30720S²(c(v - 1/3200 - 1/600) - (x - 1)/200) = 243X³ + 11439X²/8 + 12333X/8 + 3063/32`
  have hv2 : (13 / 6 + X - 1) / 200 ≤
      (24 * (13 / 6 + X) + 51) / 128 * (hl2cxv (13 / 6 + X) - 1 / 3200 - 1 / 600) := by
    have e : (24 * (13 / 6 + X) + 51) / 128 * (hl2cxv (13 / 6 + X) - 1 / 3200 - 1 / 600) =
        (24 * (13 / 6 + X) + 51) * (680 * (13 / 6 + X - 1) ^ 2 - 19 * (1 + (13 / 6 + X)) ^ 2) /
          (1228800 * (1 + (13 / 6 + X)) ^ 2) := by
      unfold hl2cxv
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith [pow_nonneg hX 2, pow_nonneg hX 3, pow_nonneg hX 4]
  have hW : 1 / 200 ≤ hl2cxW (13 / 6 + X) a := by
    unfold hl2cxW
    rw [le_div_iff₀ hL]
    unfold hl2cxLb
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ (24 * (13 / 6 + X) + 51) / 128)
      (by linarith : (0 : ℝ) ≤ 4 / 3 - a)
    linarith
  unfold hl2cxU
  have := mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hW)
  linarith

/-- **`u_x ≤ V`** (`SHORT_RATIO_CENTRAL_X` (8), (10)-(12)):
`V - u_x = (1/96 - v_x) + (a - 1)Φ(L_β)/L_β²`; `v_x ≤ 1/96`, and `Φ` is a concave quadratic in
`L` whose values at the two ends `L = x - 1`, `x - 1 + c/3` of the range of `L_β` are
`p₀(Y)/(409600S³)`, `p₁(Y)/(6553600S³)`, `Y = x - 2`, with the printed quintics `p₀`, `p₁` of
(12). -/
theorem hl2cx_up_le {x a : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    hl2cxup x a ≤ hl2cxV a := by
  have hS : 0 < 1 + x := by linarith
  obtain ⟨Y, rfl⟩ : ∃ Y, x = 2 + Y := ⟨x - 2, by ring⟩
  have hY : 1 / 6 ≤ Y := by linarith
  have hY' : Y ≤ 2 / 5 := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hp : ∀ n : ℕ, Y ^ n ≤ (2 / 5) ^ n := fun n => pow_le_pow_left₀ hY0 hY' n
  have hq : ∀ n : ℕ, 0 ≤ Y ^ n := fun n => pow_nonneg hY0 n
  -- `v_x ≤ 1/96`: `60S³ - 1632(x - 1) > 0`
  have hvx : hl2cxvx (2 + Y) ≤ 1 / 96 := by
    unfold hl2cxvx
    rw [div_le_iff₀ (by positivity)]
    linarith [hq 3, mul_nonneg hY0 (sub_nonneg.2 hY)]
  -- the two endpoint values (12)
  have hP0 : 0 ≤ hl2cxPhi (2 + Y) (2 + Y - 1) := by
    have e : hl2cxPhi (2 + Y) (2 + Y - 1) = (13137 + 1361 * Y - 43205 * Y ^ 2 - 42269 * Y ^ 3 -
        11264 * Y ^ 4 - 1024 * Y ^ 5) / (409600 * (1 + (2 + Y)) ^ 3) := by
      unfold hl2cxPhi hl2cxvx hl2cxv
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    linarith [hp 2, hp 3, hp 4, hp 5]
  have hP1 : 0 ≤ hl2cxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) := by
    have e : hl2cxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) =
        (322953 + 16409 * Y - 930505 * Y ^ 2 - 820321 * Y ^ 3 - 210256 * Y ^ 4 -
          18496 * Y ^ 5) / (6553600 * (1 + (2 + Y)) ^ 3) := by
      unfold hl2cxPhi hl2cxvx hl2cxv
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (by positivity)
    linarith [hp 2, hp 3, hp 4, hp 5]
  -- concavity in `L`: linear interpolation in `s = a - 1 ∈ [0, 1/3]` plus `c²s(1/3 - s)/400`
  have hPhi : 0 ≤ hl2cxPhi (2 + Y) (hl2cxLb (2 + Y) a) := by
    have e : hl2cxPhi (2 + Y) (hl2cxLb (2 + Y) a) =
        (1 - 3 * (a - 1)) * hl2cxPhi (2 + Y) (2 + Y - 1) +
          3 * (a - 1) * hl2cxPhi (2 + Y) (2 + Y - 1 + (24 * (2 + Y) + 51) / 128 / 3) +
          ((24 * (2 + Y) + 51) / 128) ^ 2 * ((a - 1) * (4 / 3 - a)) / 400 := by
      unfold hl2cxPhi hl2cxLb
      ring
    rw [e]
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 3 * (a - 1)) hP0
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (a - 1)) hP1
    have h3 : 0 ≤ ((24 * (2 + Y) + 51) / 128) ^ 2 * ((a - 1) * (4 / 3 - a)) / 400 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))) (by norm_num)
    linarith
  unfold hl2cxup hl2cxV
  have := mul_nonneg (sub_nonneg.2 ha) (div_nonneg hPhi (sq_nonneg (hl2cxLb (2 + Y) a)))
  linarith

end SmoothedOctagon
