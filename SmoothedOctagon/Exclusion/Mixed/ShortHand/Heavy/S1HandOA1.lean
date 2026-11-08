module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOS2

/-!
# Gate S1 by hand, outer face: shared reductions of the large and small shape branches

* The quartic and cubic division coefficients factor (`SHORT_OUTER_LARGE_SHAPE_REDUCTION` (A15)):
  with `L = S - d₂ = x(2e - 1)`, `H = A₀ - uS ≥ (2x - 3)(3x - 2)/(25S)` (`u ≤ 19/25`),
  `W₄ = L(H + uL) > 0` and `4W₄/x + W₃ = H(4L/x - d₁) + uL(4L/x - 2d₁) > 0`
  (`hl1o_W4_pos`, `hl1o_W43_pos`); hence `b₃ ≤ 0`, `p₄ ≤ 0`, `4p₄/x + p₃ ≤ 0`.
* `E_L ≤ 1/2` on `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `β ≥ x`, `u ≥ 3/4` (`SHORT_OUTER_BETA_LOW_SHAPE`
  §1, `P_E > 0`), the lower bound `(R₂)_β ≥ 83/4200` and the strict decrease of `β ↦ F₀`
  with slope `≤ -7/5120` (`§2`, (6)-(7)): `hl1o_EL_half`, `hl1o_R2b_ge`, `hl1o_F0_bderiv`,
  `hl1o_F0_bmono`.
* The large-shape norm interval and the division coefficient at `u₊ = (6x + 443)/600`
  (`SHORT_OUTER_LARGE_SHAPE_REDUCTION` (A5)-(A7)): `u₋ ≤ u_f`, `u_v ≤ u₊`, and
  `w₀(x, α, u) > (19 + 2x)/28` for `u ≤ u₊` (`hl1o_A_w0`).

Route: the division-coefficient bound at the large shape is proved directly at the affine norm
`u₊` (a two-variable sign), instead of through `u₀` and the shape derivative `(11)-(16)` of
`SHORT_OUTER_BETA`.

## Main API

* `hl1o_W4_pos`, `hl1o_W43_pos`, `hl1o_b3_nonpos`, `hl1o_p4_nonpos`, `hl1o_p43_nonpos`;
* `hl1_eps_le`, `hl1o_EL_half`, `hl1o_R2b_ge`, `hl1o_F0_bderiv`, `hl1o_F0_bmono`;
* `hl1o_um_le`, `hl1o_up_ge`, `hl1o_w0_diff'`, `hl1o_A_w0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `P_E(6/5 - c, 3/2 + z)` (`SHORT_OUTER_BETA_LOW_SHAPE` (4)-(5)). -/
noncomputable def hl1PE2 (c z : ℝ) : ℝ :=
  -6 * c ^ 2 * z ^ 2 - 22 * c ^ 2 * z + 13 / 2 * c ^ 2 + 132 / 5 * c * z ^ 2 + 504 / 5 * c * z + 147 / 5 * c + 12 * z ^ 3 + 949 / 25 * z ^ 2 + 118 / 25 * z + 61 / 100

theorem hl1PE2_pos {c z : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ (1 / 5 : ℝ)) (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) < hl1PE2 c z := by
  unfold hl1PE2
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ c),
    (by positivity : (0 : ℝ) ≤ c * z),
    (by positivity : (0 : ℝ) ≤ c * z ^ 2),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c * z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ c ^ 2),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c * z ^ 2)]

/-- The numerator of `w₀(x, α, u₊(x)) - (19 + 2x)/28` at `α = 6/5 + A`, `x = α + X`. -/
noncomputable def hl1Pw0A (A X : ℝ) : ℝ :=
  -3 / 2450 * A ^ 7 - 3 / 490 * A ^ 6 * X - 333 / 6125 * A ^ 6 - 27 / 2450 * A ^ 5 * X ^ 2 - 27 / 350 * A ^ 5 * X - 171271 / 735000 * A ^ 5 - 3 / 350 * A ^ 4 * X ^ 3 - 2 / 1225 * A ^ 4 * X ^ 2 + 403 / 4200 * A ^ 4 * X - 47443 / 183750 * A ^ 4 - 3 / 1225 * A ^ 3 * X ^ 4 + 131 / 12250 * A ^ 3 * X ^ 3 + 42493 / 73500 * A ^ 3 * X ^ 2 + 25892 / 18375 * A ^ 3 * X + 158373 / 612500 * A ^ 3 - 64 / 6125 * A ^ 2 * X ^ 4 + 86689 / 367500 * A ^ 2 * X ^ 3 + 1564523 / 735000 * A ^ 2 * X ^ 2 + 383959 / 122500 * A ^ 2 * X + 18691411 / 22968750 * A ^ 2 - 813 / 61250 * A * X ^ 4 + 314547 / 612500 * A * X ^ 3 + 259568 / 91875 * A * X ^ 2 + 13074511 / 4593750 * A * X + 310509683 / 459375000 * A - 1441 / 306250 * X ^ 4 + 1484557 / 4593750 * X ^ 3 + 40580277 / 30625000 * X ^ 2 + 88092367 / 91875000 * X + 76411379 / 382812500

theorem hl1Pw0A_pos {A X : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ (4 / 5 : ℝ)) (hX0 : 0 ≤ X) (hX1 : X ≤ (4 / 5 : ℝ)) :
    (0 : ℝ) < hl1Pw0A A X := by
  unfold hl1Pw0A
  nlinarith [(by positivity : (0 : ℝ) ≤ X),
    (by positivity : (0 : ℝ) ≤ X ^ 2),
    (by positivity : (0 : ℝ) ≤ X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ X ^ 3),
    (by positivity : (0 : ℝ) ≤ A),
    (by positivity : (0 : ℝ) ≤ A * X),
    (by positivity : (0 : ℝ) ≤ A * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A * X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A * X ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 2 * X ^ 3),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 2),
    (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 3),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 3),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 3),
    (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 3 * X ^ 3),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 4),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 4 * X ^ 2),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 5),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 5 * X),
    mul_le_mul_of_nonneg_left hA1 (by positivity : (0 : ℝ) ≤ A ^ 6)]
/-! ### The division coefficients -/

theorem hl1o_W4_fac (x C u : ℝ) (hx : 0 < x) :
    hl1W4 x C u = x * (2 * (x - C) - 1) * (((1 + x) - 1 + 1 / (1 + x) - u * (1 + x)) +
      u * (x * (2 * (x - C) - 1))) := by
  have hS : (1 + x) ≠ 0 := by positivity
  simp only [hl1W4, hl1d2, hl1J2, hsE0]
  field_simp
  ring

theorem hl1o_W3_fac (x C u : ℝ) (hx : 0 < x) :
    hl1W3 x C u = -(hl1d1 x C * (((1 + x) - 1 + 1 / (1 + x) - u * (1 + x)) +
      2 * u * (x * (2 * (x - C) - 1)))) := by
  have hS : (1 + x) ≠ 0 := by positivity
  simp only [hl1W3, hl1d1, hl1d2, hl1J2, hsE0]
  field_simp
  ring

/-- `H = A₀ - uS ≥ 0` for `x ≥ 3/2`, `u ≤ 19/25`. -/
theorem hl1o_H_nonneg {x u : ℝ} (hx : 3 / 2 ≤ x) (hu : u ≤ 19 / 25) :
    0 ≤ (1 + x) - 1 + 1 / (1 + x) - u * (1 + x) := by
  have hS : 0 < 1 + x := by linarith
  have e : (1 + x) - 1 + 1 / (1 + x) - 19 / 25 * (1 + x) =
      (2 * x - 3) * (3 * x - 2) / (25 * (1 + x)) := by field_simp; ring
  have h1 : 0 ≤ (2 * x - 3) * (3 * x - 2) / (25 * (1 + x)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  nlinarith

theorem hl1o_W4_pos {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hC : C ≤ 10 / 13) (hu0 : 0 ≤ u)
    (hu : u ≤ 19 / 25) : 0 < hl1W4 x C u := by
  rw [hl1o_W4_fac x C u (by linarith)]
  have hH := hl1o_H_nonneg hx hu
  have hL : 0 < x * (2 * (x - C) - 1) := mul_pos (by linarith) (by linarith)
  have : 0 < (1 + x) - 1 + 1 / (1 + x) - u * (1 + x) + u * (x * (2 * (x - C) - 1)) := by
    rcases eq_or_lt_of_le hu0 with h | h
    · rw [← h]
      have : 0 < 1 / (1 + x) := by positivity
      nlinarith
    · nlinarith [mul_pos h hL]
  positivity

theorem hl1o_W43_pos {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hC0 : 0 ≤ C) (hC : C ≤ 10 / 13)
    (hu0 : 0 < u) (hu : u ≤ 19 / 25) : 0 < 4 * hl1W4 x C u / x + hl1W3 x C u := by
  have hx0 : 0 < x := by linarith
  rw [hl1o_W4_fac x C u hx0, hl1o_W3_fac x C u hx0]
  have hH := hl1o_H_nonneg hx hu
  set H := (1 + x) - 1 + 1 / (1 + x) - u * (1 + x)
  have hL : 0 < x * (2 * (x - C) - 1) := mul_pos (by linarith) (by linarith)
  have e : 4 * (x * (2 * (x - C) - 1) * (H + u * (x * (2 * (x - C) - 1)))) / x +
      -(hl1d1 x C * (H + 2 * u * (x * (2 * (x - C) - 1)))) =
      H * (2 * ((3 + C) * x - 3 * C - 2)) +
        u * (x * (2 * (x - C) - 1)) * (4 * (x - 1) * (1 + C)) := by
    unfold hl1d1; field_simp; ring
  rw [e]
  have h1 : 0 < 2 * ((3 + C) * x - 3 * C - 2) := by nlinarith
  have h2 : 0 < 4 * (x - 1) * (1 + C) := by nlinarith
  have := mul_pos (mul_pos hu0 hL) h2
  nlinarith [mul_nonneg hH h1.le]

theorem hl1o_b3_nonpos {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hC : C ≤ 10 / 13)
    (hu0 : 0 ≤ u) (hu : u ≤ 19 / 25) : hl1b3 x C u ≤ 0 := by
  have := hl1o_W4_pos hx hx2 hC hu0 hu
  unfold hl1b3 hl1q3
  have he : 0 < x - C := by linarith
  have : 0 < hl1W4 x C u / (x - C) := div_pos this he
  linarith

theorem hl1o_p4_nonpos {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hC : C ≤ 10 / 13)
    (hu0 : 0 ≤ u) (hu : u ≤ 19 / 25) : hl1p4 x C u ≤ 0 := by
  have h1 := hl1o_W4_pos hx hx2 hC hu0 hu
  have h2 := hl1g4_nonpos (u := u) (by linarith : (0 : ℝ) < x)
  unfold hl1p4
  unfold hl1b4 at h2
  linarith

theorem hl1o_p43_nonpos {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hC0 : 0 ≤ C)
    (hC : C ≤ 10 / 13) (hu0 : 0 < u) (hu : u ≤ 19 / 25) :
    4 * hl1p4 x C u / x + hl1p3 x C u ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have h1 := hl1o_W43_pos hx hx2 hC0 hC hu0 hu
  have h2 := hl1g4_nonpos (u := u) hx0
  unfold hl1b4 at h2
  have e : 4 * hl1p4 x C u / x + hl1p3 x C u =
      4 * hl1g4 x u / x - (4 * hl1W4 x C u / x + hl1W3 x C u) / 336 := by
    unfold hl1p4 hl1p3; field_simp; ring
  rw [e]
  have : 4 * hl1g4 x u / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hx0.le
  have : 0 < (4 * hl1W4 x C u / x + hl1W3 x C u) / 336 := by positivity
  linarith

/-! ### The pairing and the beta derivative of `F₀` on `1 ≤ α ≤ 6/5` -/

theorem hl1_eps_le {y : ℝ} (h0 : 9 / 14 ≤ y) (h1 : y ≤ 1) : hh1eps y ≤ (5 / 23) ^ 4 := by
  have hy : 0 < y + 1 := by linarith
  have e : hh1eps y = ((1 - y) / (y + 1)) ^ 4 := by unfold hh1eps; ring
  have t0 : 0 ≤ (1 - y) / (y + 1) := div_nonneg (by linarith) hy.le
  have t1 : (1 - y) / (y + 1) ≤ 5 / 23 := by rw [div_le_iff₀ hy]; linarith
  rw [e]
  exact pow_le_pow_left₀ t0 t1 4

/-- `E_L ≤ 1/2` (`SHORT_OUTER_BETA_LOW_SHAPE` §1). -/
theorem hl1o_EL_half {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hxb : x ≤ b) (hu0 : 3 / 4 ≤ u) : hh1oEL x a b u < 1 / 2 := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hS : hh1oEL x a b u - hh1oEL x a x (3 / 4) =
      (2 * u * (2 * (a - x) * (b - x)) +
        (u - 3 / 4) * (2 * hsDg x x a - hh1oK a * (1 + x))) / (7 * a ^ 2) := by
    rw [hl1o_EL hx0 ha.ne', hl1o_EL hx0 ha.ne']
    simp only [hl1oJ, hsE0, hsDg, hh1oK]
    field_simp
    ring
  have hE : hh1oEL x a x (3 / 4) = 1 / 2 - hl1PE2 (6 / 5 - a) (x - 3 / 2) / (28 * a ^ 2 * (1 + x)) := by
    rw [hl1o_EL hx0 ha.ne']
    simp only [hl1oJ, hsE0, hsDg, hh1oK, hl1PE2]
    field_simp
    ring
  have hP := hl1PE2_pos (c := 6 / 5 - a) (z := x - 3 / 2) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h1 : 2 * hsDg x x a - hh1oK a * (1 + x) ≤ 0 := by
    unfold hsDg hh1oK; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hx)]
  have h2 : (2 * u * (2 * (a - x) * (b - x)) +
      (u - 3 / 4) * (2 * hsDg x x a - hh1oK a * (1 + x))) / (7 * a ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have : 2 * u * (2 * (a - x) * (b - x)) ≤ 0 := by
      have : 0 ≤ 2 * u * (2 * (x - a) * (b - x)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
      linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 3 / 4) (by linarith : (0 : ℝ) ≤
      -(2 * hsDg x x a - hh1oK a * (1 + x)))]
  have h3 : 0 < hl1PE2 (6 / 5 - a) (x - 3 / 2) / (28 * a ^ 2 * (1 + x)) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- `(R₂)_β ≥ 83/4200` (`SHORT_OUTER_BETA_LOW_SHAPE` (6)-(7)). -/
theorem hl1o_R2b_ge {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hxb : x ≤ b) (hbx : b ≤ a * x) (hu0 : 3 / 4 ≤ u) : 83 / 4200 ≤ hh1oR2b x a b u := by
  have ha : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hab : 0 < a + b := by linarith
  have e : hh1oR2b x a b u = 4 * (x - a) * (u - hh1oEL x a b u) / (7 * a ^ 2) +
      (u - 1 + a / (a + b) - (a / (a + b)) ^ 2) / a := by
    simp only [hh1oR2b, hh1owb, hh1odb, hh1oEL, hh1od, hh1oL, hh1oE, hh1oK]
    field_simp
    ring
  rw [e]
  have hE := hl1o_EL_half hx hx2 ha1 ha2 hxb hu0
  -- the transport term
  have h1 : 25 * (x - 6 / 5) / 252 ≤ 4 * (x - a) * (u - hh1oEL x a b u) / (7 * a ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : 1 / 4 ≤ u - hh1oEL x a b u := by linarith
    have h4 : 0 ≤ x - a := by linarith
    have h5 : (x - 6 / 5) * (7 * a ^ 2) * 25 ≤ (x - a) * 252 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this h4]
  -- the shape term
  have hr0 : 1 / (1 + x) ≤ a / (a + b) := by
    rw [div_le_div_iff₀ (by positivity) hab]; nlinarith
  have hr1 : a / (a + b) ≤ 1 / 2 := by rw [div_le_iff₀ hab]; linarith
  have h2 : -((x - 1) ^ 2 / (4 * (1 + x) ^ 2)) ≤ (u - 1 + a / (a + b) - (a / (a + b)) ^ 2) / a := by
    set r := a / (a + b)
    have hq : (r - 1 / 2) ^ 2 ≤ (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
      have e2 : (x - 1) ^ 2 / (4 * (1 + x) ^ 2) = (1 / (1 + x) - 1 / 2) ^ 2 := by
        field_simp; ring
      rw [e2]
      nlinarith
    have hnum : -((x - 1) ^ 2 / (4 * (1 + x) ^ 2)) ≤ u - 1 + r - r ^ 2 := by nlinarith
    have hq0 : 0 ≤ (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by positivity
    rw [le_div_iff₀ ha]
    nlinarith
  have h3 : 83 / 4200 ≤ 25 * (x - 6 / 5) / 252 - (x - 1) ^ 2 / (4 * (1 + x) ^ 2) := by
    have hS : 0 < 1 + x := by linarith
    rw [sub_eq_add_neg, ← neg_div, div_add_div _ _ (by norm_num) (by positivity),
      le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  linarith

/-- **The beta derivative of `F₀`** (`SHORT_OUTER_BETA_LOW_SHAPE` (7)): the derivative of
`β ↦ F₀(x, α, β, u)` given by `hh1o_F0_hasDerivAt` is at most `-7/5120`. -/
theorem hl1o_F0_bderiv {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 6 / 5) (hxb : x ≤ b) (hbx : b ≤ a * x) (hu0 : 3 / 4 ≤ u) :
    -(7 / 96) * hh1oR2b x a b u + 7 / 96 * hh1eps (hh1oy a b) * (1 / (a + b)) ≤ -(7 / 5120) := by
  have hR := hl1o_R2b_ge hx hx2 ha1 ha2 hxb hbx hu0
  have ha : 0 < a := by linarith
  have hab : 5 / 2 ≤ a + b := by linarith
  have hy0 : 9 / 14 ≤ hh1oy a b := by
    unfold hh1oy; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hy1 : hh1oy a b ≤ 1 := by
    unfold hh1oy; rw [div_le_one (by positivity)]; nlinarith
  have he := hl1_eps_le hy0 hy1
  have he0 := hh1_eps_nonneg (hh1oy a b)
  have hi : 1 / (a + b) ≤ 2 / 5 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hi0 : 0 ≤ 1 / (a + b) := by positivity
  have : hh1eps (hh1oy a b) * (1 / (a + b)) ≤ (5 / 23) ^ 4 * (2 / 5) :=
    mul_le_mul he hi hi0 (by positivity)
  norm_num at this
  nlinarith

/-- **`F₀` decreases in `β`** at a fixed norm, with slope at most `-7/5120`. -/
theorem hl1o_F0_bmono {x a b1 b2 u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 6 / 5) (hb1 : x ≤ b1) (hb12 : b1 ≤ b2) (hb2 : b2 ≤ a * x) (hu0 : 3 / 4 ≤ u) :
    hh1oF0 x a b2 u ≤ hh1oF0 x a b1 u - 7 / 5120 * (b2 - b1) := by
  have key := ss_le_of_deriv (f := fun t => -(hh1oF0 x a t u + 7 / 5120 * t))
    (f' := fun t => -(-(7 / 96) * hh1oR2b x a t u + 7 / 96 * hh1eps (hh1oy a t) * (1 / (a + t)) +
      7 / 5120)) (x := b1) (y := b2) hb12
    (fun t ht => ((hh1o_F0_hasDerivAt (x := x) (hasDerivAt_const t a) (hasDerivAt_id' t)
      (hasDerivAt_const t u) (by linarith) (by linarith [ht.1])).add
        ((hasDerivAt_id' t).const_mul (7 / 5120))).neg |>.congr_deriv (by ring))
    (fun t ht => by
      have := hl1o_F0_bderiv (b := t) hx hx2 ha1 ha2 (by linarith [ht.1]) (by linarith [ht.2]) hu0
      linarith)
  linarith

/-! ### The large-shape norms and the division coefficient -/

theorem hl1o_um_le {x : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) : (8 * x + 1303) / 1750 ≤ hsUf x := by
  unfold hsUf
  have hS : 0 < 1 + x := by linarith
  have e : 3 / 4 + (x - 1) ^ 2 / (28 * (x + 1) ^ 2) - (8 * x + 1303) / 1750 =
      (4 - x) * (2 * x - 3) ^ 2 / (875 * (x + 1) ^ 2) := by field_simp; ring
  have : 0 ≤ (4 - x) * (2 * x - 3) ^ 2 / (875 * (x + 1) ^ 2) :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
  linarith

theorem hl1o_up_ge {x : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) : hsVbar x ≤ (6 * x + 443) / 600 := by
  unfold hsVbar
  have hS : 0 < (x + 1) * (35 * x + 13) := by positivity
  have e : (6 * x + 443) / 600 - (3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13))) =
      (210 * x ^ 3 - 1157 * x ^ 2 + 2142 * x - 1291) / (600 * ((x + 1) * (35 * x + 13))) := by
    field_simp; ring
  have hP : 0 ≤ 210 * x ^ 3 - 1157 * x ^ 2 + 2142 * x - 1291 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx), mul_nonneg (mul_nonneg
      (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx), mul_nonneg (sub_nonneg.2 hx)
      (sub_nonneg.2 hx2)]
  have : 0 ≤ (210 * x ^ 3 - 1157 * x ^ 2 + 2142 * x - 1291) / (600 * ((x + 1) * (35 * x + 13))) :=
    div_nonneg hP (by positivity)
  linarith

theorem hl1o_w0_diff' {x a u u' : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hl1ow0 x a u - hl1ow0 x a u' =
      (u' - u) * hl1oD0 x a * (hh1oK a * (1 + x) - hl1oD0 x a) / (49 * a ^ 4) := by
  have ha0 : a ≠ 0 := ha.ne'
  simp only [hl1ow0, hl1oJ, hsE0]
  generalize hl1oM x a = M
  generalize hl1oD0 x a = D0
  field_simp
  ring

/-- **The division coefficient on the large shapes** at norms `u ≤ u₊(x)`. -/
theorem hl1o_A_w0 {x a u : ℝ} (ha : 6 / 5 ≤ a) (hax : a ≤ x) (hx2 : x ≤ 2)
    (hu : u ≤ (6 * x + 443) / 600) : (19 + 2 * x) / 28 < hl1ow0 x a u := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have h1 := hl1o_w0_diff' (u := u) (u' := (6 * x + 443) / 600) hx0 ha0
  have hid : hl1ow0 x a ((6 * x + 443) / 600) - (19 + 2 * x) / 28 =
      hl1Pw0A (a - 6 / 5) (x - a) / (a ^ 4 * (x + 1)) := by
    simp only [hl1ow0, hl1oM, hl1oJ, hh1oK, hsE0, hl1oD0, hl1Pw0A]
    field_simp
    ring
  have hP := hl1Pw0A_pos (A := a - 6 / 5) (X := x - a) (by linarith) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨hD0, hD1⟩ := hl1o_KS_D0 (by linarith : (1 : ℝ) ≤ a) hax
  have h2 : 0 ≤ ((6 * x + 443) / 600 - u) * hl1oD0 x a * (hh1oK a * (1 + x) - hl1oD0 x a) /
      (49 * a ^ 4) := div_nonneg (mul_nonneg (mul_nonneg (by linarith) hD0.le) (by linarith))
        (by positivity)
  have h3 : 0 < hl1Pw0A (a - 6 / 5) (x - a) / (a ^ 4 * (x + 1)) := div_pos hP (by positivity)
  linarith

end SmoothedOctagon
