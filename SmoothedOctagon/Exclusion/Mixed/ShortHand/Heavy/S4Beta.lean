module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta1

/-!
# Heavy leaf `hs4_floor_box`: monotonicity in `β`

For `2 ≤ x ≤ 13/6`, `1 ≤ α ≤ 22/19` and `x ≤ β₁ ≤ β₂ ≤ 20x/19`, with `u = ū(x, β)`:
`Φ(β₂) ≤ Φ(β₁)` and `Ψ(β₂) ≤ Ψ(β₁)` (`hh46_s4_beta_mono`). This moves every point of the box
`13δ/5 ≤ α - 1 ≤ 3δ` to one of the two faces `η = 13/5` and `δ = 1/19`.

Route (not in the notes, which use six derivative signs of degrees up to `(19, 16, 10)`): split
`F(β₁, u₁) - F(β₂, u₂) = [F(β₁, u₁) - F(β₁, u₂)] + [F(β₁, u₂) - F(β₂, u₂)]`.

* The fixed-`u` step is an exact divided difference (`D` and `A = α + β` are affine in `β`) plus
  `log(A₂/A₁) ≥ (β₂ - β₁)/A₂`; its quotient is bounded below, piece by piece monotonically in
  `β₁, β₂`, by functions of `(x, α, u)` that are `≥ 1/15` (`hh46_s4_kPhi_ge`, `hh46_s4_kI_ge`,
  `hh46_s4_kII_ge`).
* The `u`-step is exact (`F` is quadratic in `u`): `(u₁ - u₂)∂_uF(midpoint)`, and
  `∂_uF ≥ -13/20` (`hh46_s4_Lu_ge`).
* `0 ≤ ū(β₁) - ū(β₂) ≤ (β₂ - β₁)/100` and `757/1000 ≤ ū ≤ 19/25`.

Then `F(β₁) - F(β₂) ≥ (β₂ - β₁)(1/105 - 13/2000) ≥ 0`.

## Main API

`hh46_s4_ubar_bounds`, `hh46_s4_ubar_lip`, `hh46_s4_beta_mono`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-! ### The incoming majorant -/

theorem hh46_s4_ubar_bounds {x b : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hb : x ≤ b)
    (hb2 : b ≤ 20 / 19 * x) : 757 / 1000 ≤ hsUbar x b ∧ hsUbar x b ≤ 19 / 25 := by
  have hx0 : 0 < x := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < (x + 1) * (35 * x + 13) := by positivity
  have hc0 : 0 ≤ (b - x) ^ 3 / (48 * x ^ 2) := by
    have : 0 ≤ b - x := by linarith
    positivity
  have hc1 : (b - x) ^ 3 / (48 * x ^ 2) ≤ x / 329232 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : 0 ≤ b - x := by linarith
    have h2 : b - x ≤ x / 19 := by linarith
    have h3 : (b - x) ^ 3 ≤ (x / 19) ^ 3 := pow_le_pow_left₀ h1 h2 3
    nlinarith [h3]
  unfold hsUbar
  constructor
  · have key : 7 / 1000 ≤ 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) / (b - 1) := by
      rw [le_div_iff₀ hb1, le_div_iff₀ hV]
      have : b - 1 ≤ 20 / 19 * x - 1 := by linarith
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x),
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ x - 2))
          (by linarith : (0:ℝ) ≤ x - 2)]
    have : 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) / (b - 1) ≤
        (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (b - x) ^ 3 / (48 * x ^ 2)) / (b - 1) := by
      apply div_le_div_of_nonneg_right _ hb1.le
      linarith
    linarith
  · have h1 : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (b - x) ^ 3 / (48 * x ^ 2)) / (b - 1) ≤
        (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + x / 329232) / (x - 1) := by
      have h0 : 0 ≤ 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + x / 329232 := by
        have : 0 ≤ x - 1 := by linarith
        positivity
      apply div_le_div₀ h0 (by linarith) (by linarith) (by linarith)
    have h2 : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + x / 329232) / (x - 1) ≤ 1 / 100 := by
      rw [div_le_iff₀ (by linarith), div_add_div _ _ hV.ne' (by norm_num), div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x),
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ x - 2))
          (by linarith : (0:ℝ) ≤ 13 / 6 - x)]
    linarith

theorem hh46_s4_ubar_lip_pq {x p q : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hp0 : 0 ≤ p)
    (hpq : p ≤ q) (hq1 : q ≤ x / 19) :
    0 ≤ hsUbar x (x + p) - hsUbar x (x + q) ∧ hsUbar x (x + p) - hsUbar x (x + q) ≤ (q - p) / 100 := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x - 1 := by linarith
  have hV : 0 < (x + 1) * (35 * x + 13) := by positivity
  have hq0 : 0 ≤ q := by linarith
  have e : hsUbar x (x + p) - hsUbar x (x + q) = (q - p) * (96 * x ^ 2 * (x - 1) ^ 3 -
      (x + 1) * (35 * x + 13) * (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2))) /
      (48 * x ^ 2 * (x + 1) * (35 * x + 13) * (p + (x - 1)) * (q + (x - 1))) := by
    unfold hsUbar
    have h1 : x + p - 1 = p + (x - 1) := by ring
    have h2 : x + q - 1 = q + (x - 1) := by ring
    have h3 : x + p - x = p := by ring
    have h4 : x + q - x = q := by ring
    rw [h1, h2, h3, h4]
    have : p + (x - 1) ≠ 0 := by linarith
    have : q + (x - 1) ≠ 0 := by linarith
    have : x + 1 ≠ 0 := by linarith
    have : 35 * x + 13 ≠ 0 := by linarith
    have : x ≠ 0 := by linarith
    field_simp
    ring
  have hP : 0 < p + (x - 1) := by linarith
  have hQ : 0 < q + (x - 1) := by linarith
  have hden : 0 < 48 * x ^ 2 * (x + 1) * (35 * x + 13) * (p + (x - 1)) * (q + (x - 1)) := by
    positivity
  have hpq2 : p * q ≤ (x / 19) ^ 2 := by nlinarith
  have hW1 : p * q * (p + q) ≤ (x / 19) ^ 2 * (2 * (x / 19)) := by
    have : p + q ≤ 2 * (x / 19) := by linarith
    have h0 : 0 ≤ p * q := mul_nonneg hp0 hq0
    nlinarith [mul_le_mul hpq2 this (by linarith) (by positivity)]
  have hW2 : p ^ 2 + p * q + q ^ 2 ≤ 3 * (x / 19) ^ 2 := by nlinarith
  have hW : (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2)) ≤
      (x / 19) ^ 2 * (2 * (x / 19)) + (x - 1) * (3 * (x / 19) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hW2 hm.le]
  have hW0 : 0 ≤ (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2)) := by positivity
  have hbig : (x + 1) * (35 * x + 13) * ((x / 19) ^ 2 * (2 * (x / 19)) + (x - 1) * (3 * (x / 19) ^ 2))
      ≤ 96 * x ^ 2 * (x - 1) ^ 3 := by
    have h1 : (x + 1) * (35 * x + 13) ≤ 300 := by nlinarith
    have h2 : (x / 19) ^ 2 * (2 * (x / 19)) + (x - 1) * (3 * (x / 19) ^ 2) ≤ x ^ 2 / 90 := by
      have e2 : (x / 19) ^ 2 * (2 * (x / 19)) + (x - 1) * (3 * (x / 19) ^ 2) =
          x ^ 2 * (2 * x / 19 + 3 * (x - 1)) / 361 := by ring
      rw [e2]
      have : 2 * x / 19 + 3 * (x - 1) ≤ 361 / 90 := by linarith
      have := mul_le_mul_of_nonneg_left this (sq_nonneg x)
      linarith
    have h3 : x ^ 2 ≤ x ^ 2 * (x - 1) ^ 3 := by
      have : 1 ≤ (x - 1) ^ 3 := one_le_pow₀ (by linarith)
      have := mul_le_mul_of_nonneg_left this (sq_nonneg x)
      linarith
    have h4 : 0 ≤ (x / 19) ^ 2 * (2 * (x / 19)) + (x - 1) * (3 * (x / 19) ^ 2) := by positivity
    have h5 := mul_le_mul h1 h2 h4 (by norm_num)
    have h6 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith
  rw [e]
  constructor
  · apply div_nonneg _ hden.le
    apply mul_nonneg (by linarith)
    have := mul_le_mul_of_nonneg_left hW hV.le
    linarith
  · rw [div_le_div_iff₀ hden (by norm_num)]
    have hqp : 0 ≤ q - p := by linarith
    have h1 : 96 * x ^ 2 * (x - 1) ^ 3 - (x + 1) * (35 * x + 13) *
        (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2)) ≤ 96 * x ^ 2 * (x - 1) ^ 3 := by
      have := mul_nonneg hV.le hW0
      linarith
    have h2 : (x - 1) ^ 2 ≤ (p + (x - 1)) * (q + (x - 1)) := by
      have e2 : (p + (x - 1)) * (q + (x - 1)) = (x - 1) ^ 2 + (x - 1) * (p + q) + p * q := by ring
      have := mul_nonneg hp0 hq0
      have := mul_nonneg hm.le (add_nonneg hp0 hq0)
      linarith
    have h48 : 0 ≤ 48 * x ^ 2 * (x + 1) * (35 * x + 13) := by positivity
    have h3 : 200 * (x - 1) ≤ (x + 1) * (35 * x + 13) := by nlinarith [sq_nonneg (x - 2)]
    have h7 : 0 ≤ 48 * x ^ 2 * (x - 1) ^ 2 := by positivity
    have h6' := mul_le_mul_of_nonneg_left h3 h7
    have h6 : 96 * x ^ 2 * (x - 1) ^ 3 * 100 ≤ 48 * x ^ 2 * (x + 1) * (35 * x + 13) * (x - 1) ^ 2 := by
      have e6 : 48 * x ^ 2 * (x - 1) ^ 2 * (200 * (x - 1)) = 96 * x ^ 2 * (x - 1) ^ 3 * 100 := by ring
      have e7 : 48 * x ^ 2 * (x - 1) ^ 2 * ((x + 1) * (35 * x + 13)) =
          48 * x ^ 2 * (x + 1) * (35 * x + 13) * (x - 1) ^ 2 := by ring
      linarith
    have h8 := mul_le_mul_of_nonneg_left h2 h48
    have h5 : 96 * x ^ 2 * (x - 1) ^ 3 * 100 ≤
        48 * x ^ 2 * (x + 1) * (35 * x + 13) * (p + (x - 1)) * (q + (x - 1)) := by
      have e8 : 48 * x ^ 2 * (x + 1) * (35 * x + 13) * ((p + (x - 1)) * (q + (x - 1))) =
          48 * x ^ 2 * (x + 1) * (35 * x + 13) * (p + (x - 1)) * (q + (x - 1)) := by ring
      linarith
    have h9 := mul_le_mul_of_nonneg_left h1 hqp
    have h10 := mul_le_mul_of_nonneg_left h5 hqp
    have e9 : (q - p) * (96 * x ^ 2 * (x - 1) ^ 3 - (x + 1) * (35 * x + 13) *
          (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2))) * 100 =
        100 * ((q - p) * (96 * x ^ 2 * (x - 1) ^ 3 - (x + 1) * (35 * x + 13) *
          (p * q * (p + q) + (x - 1) * (p ^ 2 + p * q + q ^ 2)))) := by ring
    have e10 : (q - p) * (96 * x ^ 2 * (x - 1) ^ 3 * 100) = 100 * ((q - p) * (96 * x ^ 2 * (x - 1) ^ 3)) := by
      ring
    linarith

theorem hh46_s4_ubar_lip {x b1 b2 : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hb1 : x ≤ b1)
    (h12 : b1 ≤ b2) (hb2 : b2 ≤ 20 / 19 * x) :
    0 ≤ hsUbar x b1 - hsUbar x b2 ∧ hsUbar x b1 - hsUbar x b2 ≤ (b2 - b1) / 100 := by
  have h := hh46_s4_ubar_lip_pq (p := b1 - x) (q := b2 - x) hx hx2 (by linarith) (by linarith)
    (by linarith)
  rw [show x + (b1 - x) = b1 by ring, show x + (b2 - x) = b2 by ring,
    show b2 - x - (b1 - x) = b2 - b1 by ring] at h
  exact h

end SmoothedOctagon
