module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2b

/-!
# Gate S4, hand proof W2 (c): positivity of the coefficients by the monomial rule

The polynomials are `U₀, …, U₃` and `P_*` of `S4HandW2b`. On `0 ≤ c ≤ 3/19`, `0 ≤ h ≤ 1/6`:
discard the positive terms
containing `c`, replace `c^i` by `(3/19)^i` in the negative ones (`hl46_w2_cm`), then discard the
nonconstant positive terms of the resulting polynomial in `h` and use `h^j ≤ (1/6)^j` in its
negative ones (`hl46_w2_hm`). Each step is one `linarith` over the monomials of one displayed
polynomial. The same rule proves `T₁, T₂, T₃ > 0` (used in `S4HandW2b`).

## Main API

* `hl46_w2_Ps_pos` (`P_* > 19`), `hl46_w2_T1_pos`, `hl46_w2_T2_pos`, `hl46_w2_T3_pos`,
  `hl46_w2_U0_pos`, …, `hl46_w2_U3_pos`.
* `hl46_w2_Tz_pos`, `hl46_w2_Uz_nonneg` (for `z ≥ 0`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The monomial rule, first step: `c^i h^j ≤ (3/19)^i h^j`. -/
theorem hl46_w2_cm {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (i j : ℕ) :
    c ^ i * h ^ j ≤ (3 / 19) ^ i * h ^ j :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc hc' i) (pow_nonneg hh j)

/-- A discarded positive monomial: `0 ≤ c^i h^j`. -/
theorem hl46_w2_cp {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (i j : ℕ) : 0 ≤ c ^ i * h ^ j := by
  positivity

/-- The monomial rule, second step: `h^j ≤ (1/6)^j`. -/
theorem hl46_w2_hm {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) (j : ℕ) : h ^ j ≤ (1 / 6) ^ j :=
  pow_le_pow_left₀ hh hh' j

/-- `P_*(c, h) > 19` (the lower polynomial in `h` after the first step exceeds `19`). -/
theorem hl46_w2_Ps_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    19 < hl46W2Ps c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2Ps
  linarith [cm 6 1, cm 6 0, cp 5 2, cp 5 1, cm 5 0, cp 4 4, cp 4 3, cp 4 2, cp 4 1, cp 4 0,
    cm 3 5, cm 3 4, cp 3 3, cp 3 2, cp 3 1, cp 3 0, cm 2 6, cm 2 5, cm 2 4, cm 2 3, cm 2 2,
    cm 2 1, cp 2 0, cm 1 7, cm 1 6, cm 1 5, cm 1 4, cm 1 3, cm 1 2, cm 1 1, cm 1 0, hp 1, hm 1,
    hp 2, hm 2, hp 3, hm 3, hp 4, hm 4, hp 5, hm 5, hp 6, hm 6, hp 7, hm 7, hp 8, hm 8]

/-- `T₁(c, h) > 0` (monomial rule). -/
theorem hl46_w2_T1_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2T1 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2T1
  linarith [cm 6 0, cp 5 1, cp 5 0, cp 4 3, cm 4 2, cm 4 1, cm 4 0, cm 3 4, cp 3 3, cp 3 2,
    cp 3 1, cp 3 0, cm 2 5, cm 2 4, cm 2 3, cm 2 2, cp 2 1, cp 2 0, cm 1 6, cm 1 5, cm 1 4,
    cm 1 3, cm 1 2, cm 1 1, cm 1 0, hp 1, hm 1, hp 2, hm 2, hp 3, hm 3, hp 4, hm 4, hp 5, hm 5,
    hp 6, hm 6, hp 7, hm 7]

/-- `T₂(c, h) > 0` (monomial rule). -/
theorem hl46_w2_T2_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2T2 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2T2
  linarith [cp 5 0, cm 4 1, cm 4 0, cp 3 3, cp 3 2, cm 3 1, cm 3 0, cm 2 4, cp 2 3, cp 2 2,
    cp 2 1, cp 2 0, cp 1 4, cp 1 3, cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1, hp 2, hm 2, hp 3, hm 3,
    hp 4, hm 4, hp 5, hm 5, hp 6, hm 6]

/-- `T₃(c, h) > 0` (monomial rule). -/
theorem hl46_w2_T3_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2T3 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2T3
  linarith [cm 4 0, cm 3 1, cm 3 0, cp 2 2, cp 2 1, cm 2 0, cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1,
    hp 2, hm 2, hp 3, hm 3, hp 4, hm 4]

/-- `U₀(c, h) > 0` (the lower polynomial in `h` exceeds `4469`). -/
theorem hl46_w2_U0_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2U0 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2U0
  linarith [cp 5 2, cp 5 1, cp 5 0, cm 4 4, cm 4 3, cm 4 2, cm 4 1, cp 4 0, cp 3 5, cp 3 4,
    cp 3 3, cp 3 2, cp 3 1, cp 3 0, cp 2 6, cp 2 5, cp 2 4, cp 2 3, cp 2 2, cp 2 1, cp 2 0,
    cp 1 7, cp 1 6, cp 1 5, cp 1 4, cp 1 3, cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1, hp 2, hm 2, hp 3,
    hm 3, hp 4, hm 4, hp 5, hm 5, hp 6, hm 6, hp 7, hm 7, hp 8, hm 8]

/-- `U₁(c, h) > 0` (the lower polynomial in `h` exceeds `7533`). -/
theorem hl46_w2_U1_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2U1 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2U1
  linarith [cp 5 1, cp 5 0, cm 4 3, cm 4 2, cm 4 1, cm 4 0, cp 3 4, cp 3 3, cp 3 2, cp 3 1,
    cp 3 0, cp 2 5, cp 2 4, cp 2 3, cp 2 2, cp 2 1, cp 2 0, cp 1 6, cp 1 5, cp 1 4, cp 1 3,
    cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1, hp 2, hm 2, hp 3, hm 3, hp 4, hm 4, hp 5, hm 5, hp 6,
    hm 6, hp 7, hm 7]

/-- `U₂(c, h) > 0` (the lower polynomial in `h` exceeds `2584`). -/
theorem hl46_w2_U2_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2U2 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2U2
  linarith [cp 5 0, cm 4 1, cm 4 0, cm 3 3, cm 3 2, cm 3 1, cm 3 0, cp 2 4, cp 2 3, cp 2 2,
    cp 2 1, cp 2 0, cp 1 4, cp 1 3, cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1, hp 2, hm 2, hp 3, hm 3,
    hp 4, hm 4, hp 5, hm 5, hp 6, hm 6]

/-- `U₃(c, h) > 0` (the lower polynomial in `h` exceeds `239`). -/
theorem hl46_w2_U3_pos {c h : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W2U3 c h := by
  have cm := hl46_w2_cm hc hc' hh
  have cp := hl46_w2_cp hc hh
  have hp := fun j => pow_nonneg hh j
  have hm := hl46_w2_hm hh hh'
  unfold hl46W2U3
  linarith [cp 4 0, cm 3 1, cm 3 0, cp 2 2, cp 2 1, cp 2 0, cp 1 2, cp 1 1, cp 1 0, hp 1, hm 1,
    hp 2, hm 2, hp 3, hm 3, hp 4, hm 4]
/-- `P_* + T₁z + T₂z² + T₃z³ > 0` for `z ≥ 0`. -/
theorem hl46_w2_Tz_pos {c h z : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h)
    (hh' : h ≤ 1 / 6) (hz : 0 ≤ z) : 0 < hl46W2Tz c h z := by
  have h0 := hl46_w2_Ps_pos hc hc' hh hh'
  have h1 := hl46_w2_T1_pos hc hc' hh hh'
  have h2 := hl46_w2_T2_pos hc hc' hh hh'
  have h3 := hl46_w2_T3_pos hc hc' hh hh'
  have e2 : 0 ≤ hl46W2T2 c h + z * hl46W2T3 c h := add_nonneg h2.le (mul_nonneg hz h3.le)
  have e1 : 0 ≤ hl46W2T1 c h + z * (hl46W2T2 c h + z * hl46W2T3 c h) :=
    add_nonneg h1.le (mul_nonneg hz e2)
  unfold hl46W2Tz
  have := mul_nonneg hz e1
  linarith

/-- `U₀ + U₁z + U₂z² + U₃z³ ≥ 0` for `z ≥ 0`, hence `Ψ_au ≥ 0`. -/
theorem hl46_w2_Uz_nonneg {c h z : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 3 / 19) (hh : 0 ≤ h)
    (hh' : h ≤ 1 / 6) (hz : 0 ≤ z) : 0 ≤ hl46W2Uz c h z := by
  have h0 := hl46_w2_U0_pos hc hc' hh hh'
  have h1 := hl46_w2_U1_pos hc hc' hh hh'
  have h2 := hl46_w2_U2_pos hc hc' hh hh'
  have h3 := hl46_w2_U3_pos hc hc' hh hh'
  have e2 : 0 ≤ hl46W2U2 c h + z * hl46W2U3 c h := add_nonneg h2.le (mul_nonneg hz h3.le)
  have e1 : 0 ≤ hl46W2U1 c h + z * (hl46W2U2 c h + z * hl46W2U3 c h) :=
    add_nonneg h1.le (mul_nonneg hz e2)
  unfold hl46W2Uz
  have := mul_nonneg hz e1
  linarith

end SmoothedOctagon
