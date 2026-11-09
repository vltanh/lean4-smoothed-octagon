module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Window
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.OrderShapeSigns

/-!
# Case M2, forward successor: the duration ratio exceeds one third

An actual forward window has `t > 1/3`. Suppose `1/4 < t ≤ 1/3`. The combined residual
`F = (7 - Je²)N + C_*(3/4 - 𝒯_U)` (`nsfComb 6 0`) is negative (`nsf_window_comb`); its
`v`-coefficient is negative (`nsf_LR_Cv`, from `Je² ≤ 10/3`, `WD/x ≤ 9/4`) and its `log q`
coefficient is nonpositive, so raising `v` to `v̂ = v_G + ρ(v_G - F_ℓ)` (`ρ = (3/4)(q + 2t + x - 1)`)
and `log q` to `L₊` keeps it negative. It is a concave quadratic in `k` (`nsf_comb_pos_of_ends`), and
both shape endpoints `k = 1`, `k = 2t + x` have positive residual (`nlr_unit_pos`
of `Nonshort/Forward/LowRatio/UnitShape`, and the certificate `nsfCLRb_pos`), a contradiction.

## Main API

* `nsfVhat`; `nsf_LRb_link`; `nsf_LR_Cv`.
* `nsf_lowRatio_core`: the scalar exclusion; `nsf_low_ratio`: **`t > 1/3`** for an actual forward
  window.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The low-ratio effective norm `v̂ = v_G + ρ(v_G - F_ℓ)`, `ρ = (3/4)(q + 2t + x - 1)`. -/
noncomputable def nsfVhat (t x q : ℝ) : ℝ :=
  nsfVG t x + 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q)

/-- The cleared low-ratio residual at `k = 2t + x` is the certificate polynomial `nsfCLRb`. -/
theorem nsf_LRb_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15) * nsfComb 6 0 t x (2 * t + x) q (nsfVhat t x q) (nsrLp q) 0 =
      (nsfCLRbD0_0 (1 - 2 * t) + nsfCLRbD0_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD0_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD0_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD0_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD0_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD0_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD0_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD0_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD0_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD0_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) + (nsfCLRbD1_0 (1 - 2 * t) + nsfCLRbD1_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD1_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD1_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD1_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD1_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD1_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD1_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD1_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD1_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD1_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) + (nsfCLRbD2_0 (1 - 2 * t) + nsfCLRbD2_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD2_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD2_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD2_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD2_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD2_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD2_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD2_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD2_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD2_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (2 : ℕ) + (nsfCLRbD3_0 (1 - 2 * t) + nsfCLRbD3_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD3_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD3_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD3_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD3_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD3_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD3_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD3_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD3_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD3_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (3 : ℕ) + (nsfCLRbD4_0 (1 - 2 * t) + nsfCLRbD4_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD4_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD4_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD4_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD4_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD4_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD4_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD4_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD4_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD4_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (4 : ℕ) + (nsfCLRbD5_0 (1 - 2 * t) + nsfCLRbD5_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD5_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD5_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD5_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD5_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD5_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD5_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD5_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD5_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD5_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (5 : ℕ) + (nsfCLRbD6_0 (1 - 2 * t) + nsfCLRbD6_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD6_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD6_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD6_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD6_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD6_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD6_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD6_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD6_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD6_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (6 : ℕ) + (nsfCLRbD7_0 (1 - 2 * t) + nsfCLRbD7_1 (1 - 2 * t) * (2 * t + x - 1) + nsfCLRbD7_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + nsfCLRbD7_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + nsfCLRbD7_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + nsfCLRbD7_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + nsfCLRbD7_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + nsfCLRbD7_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + nsfCLRbD7_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + nsfCLRbD7_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + nsfCLRbD7_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (7 : ℕ) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
  have hv : nsfVhat t x q = (180 + 180 * q + 435 * x + (375 / 2) * x * q + 135 * x * q ^ (2 : ℕ) + (45 / 2) * x * q ^ (3 : ℕ) + (639 / 2) * x ^ (2 : ℕ) + 267 * x ^ (2 : ℕ) * q + 270 * x ^ (2 : ℕ) * q ^ (2 : ℕ) - (195 / 2) * x ^ (2 : ℕ) * q ^ (3 : ℕ) + (269 / 4) * x ^ (3 : ℕ) + (409 / 2) * x ^ (3 : ℕ) * q + (111 / 4) * x ^ (3 : ℕ) * q ^ (2 : ℕ) - (147 / 2) * x ^ (3 : ℕ) * q ^ (3 : ℕ) + (15 / 4) * x ^ (4 : ℕ) + (237 / 4) * x ^ (4 : ℕ) * q - 60 * x ^ (4 : ℕ) * q ^ (2 : ℕ) - (15 / 2) * x ^ (4 : ℕ) * q ^ (3 : ℕ) + (3 / 2) * x ^ (5 : ℕ) + 6 * x ^ (5 : ℕ) * q - (15 / 2) * x ^ (5 : ℕ) * q ^ (2 : ℕ) - (135 / 2) * t - (765 / 2) * t * q + (135 / 2) * t * q ^ (2 : ℕ) + (45 / 2) * t * q ^ (3 : ℕ) - (585 / 2) * t * x + (255 / 2) * t * x * q + (495 / 2) * t * x * q ^ (2 : ℕ) - (465 / 2) * t * x * q ^ (3 : ℕ) - (489 / 2) * t * x ^ (2 : ℕ) + 267 * t * x ^ (2 : ℕ) * q - 288 * t * x ^ (2 : ℕ) * q ^ (2 : ℕ) - (327 / 2) * t * x ^ (2 : ℕ) * q ^ (3 : ℕ) - (11 / 4) * t * x ^ (3 : ℕ) + 103 * t * x ^ (3 : ℕ) * q - (1131 / 4) * t * x ^ (3 : ℕ) * q ^ (2 : ℕ) - (33 / 2) * t * x ^ (3 : ℕ) * q ^ (3 : ℕ) + (75 / 4) * t * x ^ (4 : ℕ) + (93 / 4) * t * x ^ (4 : ℕ) * q - (63 / 2) * t * x ^ (4 : ℕ) * q ^ (2 : ℕ) - 180 * t ^ (2 : ℕ) + 495 * t ^ (2 : ℕ) * q + 180 * t ^ (2 : ℕ) * q ^ (2 : ℕ) - 135 * t ^ (2 : ℕ) * q ^ (3 : ℕ) - 30 * t ^ (2 : ℕ) * x + 285 * t ^ (2 : ℕ) * x * q - 375 * t ^ (2 : ℕ) * x * q ^ (2 : ℕ) - 90 * t ^ (2 : ℕ) * x * q ^ (3 : ℕ) + 273 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 228 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q - 318 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q ^ (2 : ℕ) - 9 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q ^ (3 : ℕ) + (267 / 2) * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (249 / 2) * t ^ (2 : ℕ) * x ^ (3 : ℕ) * q - 33 * t ^ (2 : ℕ) * x ^ (3 : ℕ) * q ^ (2 : ℕ) + 9 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 9 * t ^ (2 : ℕ) * x ^ (4 : ℕ) * q + 270 * t ^ (3 : ℕ) - 270 * t ^ (3 : ℕ) * q ^ (2 : ℕ) + 450 * t ^ (3 : ℕ) * x + 270 * t ^ (3 : ℕ) * x * q - 180 * t ^ (3 : ℕ) * x * q ^ (2 : ℕ) + 198 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 180 * t ^ (3 : ℕ) * x ^ (2 : ℕ) * q - 18 * t ^ (3 : ℕ) * x ^ (2 : ℕ) * q ^ (2 : ℕ) + 18 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + 18 * t ^ (3 : ℕ) * x ^ (3 : ℕ) * q) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2 * (q + 1)) := by
    unfold nsfVhat nsfVG nsrFl; field_simp; ring
  rw [nsf_comb_dec, hv]
  unfold nsrLp
  apply mul_left_cancel₀ (mul_ne_zero hW hq.ne')
  rw [nsf_clear_LR hW hq.ne' hq1 hR]
  unfold nsfCLRbD0_0 nsfCLRbD0_1 nsfCLRbD0_2 nsfCLRbD0_3 nsfCLRbD0_4 nsfCLRbD0_5 nsfCLRbD0_6 nsfCLRbD0_7 nsfCLRbD0_8 nsfCLRbD0_9 nsfCLRbD0_10 nsfCLRbD1_0 nsfCLRbD1_1 nsfCLRbD1_2 nsfCLRbD1_3 nsfCLRbD1_4 nsfCLRbD1_5 nsfCLRbD1_6 nsfCLRbD1_7 nsfCLRbD1_8 nsfCLRbD1_9 nsfCLRbD1_10 nsfCLRbD2_0 nsfCLRbD2_1 nsfCLRbD2_2 nsfCLRbD2_3 nsfCLRbD2_4 nsfCLRbD2_5 nsfCLRbD2_6 nsfCLRbD2_7 nsfCLRbD2_8 nsfCLRbD2_9 nsfCLRbD2_10 nsfCLRbD3_0 nsfCLRbD3_1 nsfCLRbD3_2 nsfCLRbD3_3 nsfCLRbD3_4 nsfCLRbD3_5 nsfCLRbD3_6 nsfCLRbD3_7 nsfCLRbD3_8 nsfCLRbD3_9 nsfCLRbD3_10 nsfCLRbD4_0 nsfCLRbD4_1 nsfCLRbD4_2 nsfCLRbD4_3 nsfCLRbD4_4 nsfCLRbD4_5 nsfCLRbD4_6 nsfCLRbD4_7 nsfCLRbD4_8 nsfCLRbD4_9 nsfCLRbD4_10 nsfCLRbD5_0 nsfCLRbD5_1 nsfCLRbD5_2 nsfCLRbD5_3 nsfCLRbD5_4 nsfCLRbD5_5 nsfCLRbD5_6 nsfCLRbD5_7 nsfCLRbD5_8 nsfCLRbD5_9 nsfCLRbD5_10 nsfCLRbD6_0 nsfCLRbD6_1 nsfCLRbD6_2 nsfCLRbD6_3 nsfCLRbD6_4 nsfCLRbD6_5 nsfCLRbD6_6 nsfCLRbD6_7 nsfCLRbD6_8 nsfCLRbD6_9 nsfCLRbD6_10 nsfCLRbD7_0 nsfCLRbD7_1 nsfCLRbD7_2 nsfCLRbD7_3 nsfCLRbD7_4 nsfCLRbD7_5 nsfCLRbD7_6 nsfCLRbD7_7 nsfCLRbD7_8 nsfCLRbD7_9 nsfCLRbD7_10
  unfold nsfComb nsfCv nsfCL nsfTPv nsfTP nsfKt nsfHt nsfE0 nsrN nsrNv nsrNL
  ring

/-- `Je² ≤ 10/3` on the low-ratio domain. -/
theorem nsf_LR_J {t x q : ℝ} (ht1 : t ≤ 1 / 3) (hx1 : x ≤ 1) (hx : 0 < x) (ho : 1 ≤ 2 * t + x)
    (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    (t + x * (x + 2)) * q ^ 2 ≤ 10 / 3 * (1 + x) ^ 2 := by
  have h1 : (q * (2 * t + x)) ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ (by positivity) hqo 2
  have h2 : t + x * (x + 2) ≤ 10 / 3 * (2 * t + x) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
  nlinarith

/-- `WD/x ≤ 9/4` on the low-ratio domain. -/
theorem nsf_LR_WD {t x q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx : 0 < x) (_hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 9 / 4 * x := by
  have hW : 0 < 1 + x := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have ho0 : 0 < 2 * t + x := by linarith
  have h1 : (2 * t + x) * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
      (1 + x) * (t + x * (x + 2)) - (t + x) * (1 + x) * (2 * t + x) := by
    have := mul_le_mul_of_nonneg_right hqo hJ0
    linarith
  have h2b : 2 * (1 - t) * (1 + x) ≤ 9 / 4 * (2 * t + x) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 4) (by linarith : (0 : ℝ) ≤ 7 / 4 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x - (1 - 2 * t)) (by linarith : (0 : ℝ) ≤ 1 / 4 + 2 * t)]
  have e : (1 + x) * (t + x * (x + 2)) - (t + x) * (1 + x) * (2 * t + x) =
      (1 + x) * (t * (1 - 2 * t) + x * (2 - 3 * t)) := by ring
  have h3 : t * (1 - 2 * t) + x * (2 - 3 * t) ≤ x * (2 * (1 - t)) := by
    have := mul_le_mul_of_nonneg_left hx0 (by linarith : (0 : ℝ) ≤ t)
    linarith
  have h4 : (1 + x) * (t * (1 - 2 * t) + x * (2 - 3 * t)) ≤ 9 / 4 * x * (2 * t + x) := by
    have h5 := mul_le_mul_of_nonneg_left h3 hW.le
    have h6 := mul_le_mul_of_nonneg_left h2b hx.le
    nlinarith
  rw [e] at h1
  have h7 : (2 * t + x) * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤ (2 * t + x) * (9 / 4 * x) := by
    linarith
  exact le_of_mul_le_mul_left h7 ho0

/-- **The `v`-coefficient is negative** on the low-ratio domain, by `Je² ≤ 10/3` and
`WD/x ≤ 9/4`. -/
theorem nsf_LR_Cv {t x k q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx1 : x ≤ 1) (hk : 1 ≤ k) (hq : 1 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    nsfCv 6 0 t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have ho : 1 ≤ 2 * t + x := by linarith
  have hJ0 : 0 < t + x * (x + 2) := by positivity
  have hq0 : 0 < q := by linarith
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0.le
    linarith
  have hle := nsf_Cv_le (α := 6) (M := 0) (t := t) (x := x) (k := k) (q := q) (by linarith)
    (by linarith) hD (by positivity)
  have hNv := nsf_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hJ := nsf_LR_J ht1 hx1 hx ho hq0.le hqo
  have hWD := nsf_LR_WD ht0 ht1 hx0 hx hq0.le hqo
  have hA : 0 < x * q * k := by positivity
  have hNv0 : nsrNv t x k q < 0 := by linarith
  have e1 : 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrNv t x k q ≤
      4 * q * (11 / 3 * (1 + x) ^ 2) * nsrNv t x k q := by
    apply mul_le_mul_of_nonpos_right _ hNv0.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have e2 : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
      4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) := by
    have h0 : 0 ≤ 4 * q ^ 2 * (1 + x) ^ 2 * k := by positivity
    have := mul_le_mul_of_nonneg_left hWD h0
    have e : 4 * q ^ 2 * (1 + x) ^ 2 * k * (9 / 4 * x) = 4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) := by
      ring
    linarith
  have e3 : 4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) ≤
      4 * q * (1 + x) ^ 2 * (9 / 4) * (-nsrNv t x k q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : 4 * q * (1 + x) ^ 2 * nsrNv t x k q < 0 := mul_neg_of_pos_of_neg (by positivity) hNv0
  have e4 : 4 * q * (11 / 3 * (1 + x) ^ 2) * nsrNv t x k q + 4 * q * (1 + x) ^ 2 * (9 / 4) * (-nsrNv t x k q)
      = 17 / 12 * (4 * q * (1 + x) ^ 2 * nsrNv t x k q) := by ring
  linarith

/-- **The low-ratio scalar exclusion**: for `1/4 < t ≤ 1/3`, `1 ≤ k < 2t + x`, the swap bound and
the incoming floor, the combined residual `nsfComb 6 0` cannot be negative. -/
theorem nsf_lowRatio_core {t x k q v F : ℝ} (ht0 : 1 / 4 < t) (ht1 : t ≤ 1 / 3) (hk1 : 1 ≤ k)
    (hko : k < 2 * t + x) (h4 : 4 * t + x < 2) (hx1 : x < 1) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nsrSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) (hcomb : nsfComb 6 0 t x k q v (Real.log q) F < 0) :
    False := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hj : 1 < 2 * t + x := by linarith
  have hq0 : 0 < q := by linarith
  have hqo : q * (2 * t + x) ≤ 1 + x := by nlinarith
  have hCv := nsf_LR_Cv ht0.le ht1 (by linarith) hx1.le hk1 hq.le hqo
  have hCL : nsfCL 6 t x k q ≤ 0 := by
    unfold nsfCL
    have hJ : (t + x * (x + 2)) * q ^ 2 ≤ 7 * (1 + x) ^ 2 := by
      have h1 : q * (2 * t + x) ≤ 1 + x := hqo
      have h2 : q ^ 2 * (2 * t + x) ^ 2 ≤ (1 + x) ^ 2 := by nlinarith [mul_le_mul h1 h1 (by positivity) (by linarith)]
      have h3 : t + x * (x + 2) ≤ 7 * (2 * t + x) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg q)]
    have := nsrNL_nonpos (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq0.le (by linarith)
    have h7 : 0 ≤ 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) := by
      apply mul_nonneg (by positivity); linarith
    exact mul_nonpos_of_nonneg_of_nonpos h7 this
  -- the rational substitutions
  have hVG := nsf_secN_lt_VG hx (by linarith : t < 1)
  rw [← hv] at hVG
  have hFl := nsr_m2F_gt_Fl hq (by linarith : 0 < t + x) hW
  have hLp := nsr_log_lt_Lp hq
  have hvh : v < nsfVhat t x q := by
    unfold nsfVhat
    have : 0 ≤ 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q) := by
      apply mul_nonneg (by linarith); linarith
    linarith
  have e1 := nsf_comb_sub_v 6 0 t x k q (nsfVhat t x q) v (nsrLp q) 0
  have e2 := nsf_comb_sub_L 6 0 t x k q v (nsrLp q) (Real.log q) 0
  have e3 := nsf_comb_sub_F 6 0 t x k q v (Real.log q) 0 F
  have m1 : (nsfVhat t x q - v) * nsfCv 6 0 t x k q < 0 := mul_neg_of_pos_of_neg (by linarith) hCv
  have m2 : (nsrLp q - Real.log q) * nsfCL 6 t x k q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hCL
  have hG : nsfComb 6 0 t x k q (nsfVhat t x q) (nsrLp q) 0 < 0 := by
    have : (0 - F) * (4 * q * (1 + x) ^ 2 * 0) = 0 := by ring
    linarith
  -- the two shape endpoints
  have hy1 : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hA : 0 < nsfComb 6 0 t x 1 q (nsfVhat t x q) (nsrLp q) 0 := by
    have hy : q - 1 ≤ 1 - 2 * t := by nlinarith
    exact nlr_unit_pos ht0.le ht1 hj.le hq.le hy
  have hB : 0 < nsfComb 6 0 t x (2 * t + x) q (nsfVhat t x q) (nsrLp q) 0 := by
    have hy2 : q - 1 ≤ 1 - 2 * t := by nlinarith
    have h := nsfCLRb_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hy2
    rw [← nsf_LRb_link t x q hq0 hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by nlinarith
  have := nsf_comb_pos_of_ends (by linarith) hq0.le hD hk1 hko.le hA hB
  linarith

/-- **The duration ratio exceeds one third**: an actual forward window has `t > 1/3`. -/
theorem nsf_low_ratio (W : M2Window) (hF : W.ForwardNext) : 1 / 3 < W.nt := by
  by_contra h
  push Not at h
  obtain ⟨-, -, hx, hk1, hq, -, hv, -, -, hFl, -⟩ := nsr_window_basic W
  exact nsf_lowRatio_core (nsf_window_quarter W) h hk1.le (nsf_window_order W) (nsf_window_four W)
    (nsf_window_x_lt_one W) hq (by
      have := nsf_window_swap W
      have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by
        have := nsf_window_order W; have := nsf_window_quarter W; linarith
      rwa [lt_div_iff₀ hden] at this) hv hFl
    (nsf_window_comb W hF (α := 6) (M := 0) (by norm_num) le_rfl)

end SmoothedOctagon
