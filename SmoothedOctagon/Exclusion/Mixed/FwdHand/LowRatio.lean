module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Window
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Clear
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatioHand
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRb

/-!
# Case M2, forward successor by hand: the duration ratio exceeds one third

`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` with `MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` §§2-3: an
actual forward window has `t > 1/3`. Suppose `1/4 < t ≤ 1/3`. The combined residual
`F = (7 - Je²)N + C_*(3/4 - 𝒯_U)` (`fhComb 6 0`) is negative (`fh_window_comb`); its
`v`-coefficient is negative (`fh_LR_Cv`, from `Je² ≤ 10/3`, `WD/x ≤ 9/4`) and its `log q`
coefficient is nonpositive, so raising `v` to `v̂ = v_G + ρ(v_G - F_ℓ)` (`ρ = (3/4)(q + 2t + x - 1)`)
and `log q` to `L₊` keeps it negative. It is a concave quadratic in `k` (`fh_comb_pos_of_ends`), and
both shape endpoints `k = 1`, `k = 2t + x` have positive residual (the hand proof `lrh_unit_pos`
of `FwdHand/LowRatioHand`, and the certificate `CertLRb`), a contradiction.

Route: the shape monotonicity `Ĝ_k > 0` of the notes (§5 of the ratio reduction) is replaced by
concavity in `k` and a second endpoint certificate at `k = 2t + x`; the unit-shape sign (10) at
`k = 1` is the hand proof of the PR-2 notes `docs/lighter-proofs/NONSHORT_LOW_RATIO*.md`.

## Main API

* `fhVhat`; `fh_LRb_link`; `fh_LR_Cv`.
* `fh_lowRatio_core`: the scalar exclusion; `fh_low_ratio`: **`t > 1/3`** for an actual forward
  window.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The low-ratio effective norm `v̂ = v_G + ρ(v_G - F_ℓ)`, `ρ = (3/4)(q + 2t + x - 1)`
(`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (4)). -/
noncomputable def fhVhat (t x q : ℝ) : ℝ :=
  fhVG t x + 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q)

/-- The cleared low-ratio residual at `k = 2t + x` is the certificate polynomial `fhCLRb`. -/
theorem fh_LRb_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15) * fhComb 6 0 t x (2 * t + x) q (fhVhat t x q) (nhLp q) 0 =
      (fhCLRbD0_0 (1 - 2 * t) + fhCLRbD0_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD0_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD0_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD0_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD0_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD0_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD0_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD0_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD0_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD0_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) + (fhCLRbD1_0 (1 - 2 * t) + fhCLRbD1_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD1_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD1_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD1_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD1_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD1_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD1_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD1_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD1_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD1_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) + (fhCLRbD2_0 (1 - 2 * t) + fhCLRbD2_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD2_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD2_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD2_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD2_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD2_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD2_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD2_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD2_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD2_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (2 : ℕ) + (fhCLRbD3_0 (1 - 2 * t) + fhCLRbD3_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD3_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD3_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD3_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD3_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD3_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD3_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD3_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD3_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD3_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (3 : ℕ) + (fhCLRbD4_0 (1 - 2 * t) + fhCLRbD4_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD4_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD4_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD4_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD4_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD4_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD4_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD4_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD4_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD4_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (4 : ℕ) + (fhCLRbD5_0 (1 - 2 * t) + fhCLRbD5_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD5_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD5_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD5_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD5_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD5_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD5_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD5_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD5_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD5_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (5 : ℕ) + (fhCLRbD6_0 (1 - 2 * t) + fhCLRbD6_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD6_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD6_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD6_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD6_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD6_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD6_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD6_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD6_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD6_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (6 : ℕ) + (fhCLRbD7_0 (1 - 2 * t) + fhCLRbD7_1 (1 - 2 * t) * (2 * t + x - 1) + fhCLRbD7_2 (1 - 2 * t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCLRbD7_3 (1 - 2 * t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCLRbD7_4 (1 - 2 * t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCLRbD7_5 (1 - 2 * t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCLRbD7_6 (1 - 2 * t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCLRbD7_7 (1 - 2 * t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCLRbD7_8 (1 - 2 * t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCLRbD7_9 (1 - 2 * t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCLRbD7_10 (1 - 2 * t) * (2 * t + x - 1) ^ (10 : ℕ)) * (q - 1) ^ (7 : ℕ) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ 2 + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
  have hv : fhVhat t x q = (180 + 180 * q + 435 * x + (375 / 2) * x * q + 135 * x * q ^ (2 : ℕ) + (45 / 2) * x * q ^ (3 : ℕ) + (639 / 2) * x ^ (2 : ℕ) + 267 * x ^ (2 : ℕ) * q + 270 * x ^ (2 : ℕ) * q ^ (2 : ℕ) - (195 / 2) * x ^ (2 : ℕ) * q ^ (3 : ℕ) + (269 / 4) * x ^ (3 : ℕ) + (409 / 2) * x ^ (3 : ℕ) * q + (111 / 4) * x ^ (3 : ℕ) * q ^ (2 : ℕ) - (147 / 2) * x ^ (3 : ℕ) * q ^ (3 : ℕ) + (15 / 4) * x ^ (4 : ℕ) + (237 / 4) * x ^ (4 : ℕ) * q - 60 * x ^ (4 : ℕ) * q ^ (2 : ℕ) - (15 / 2) * x ^ (4 : ℕ) * q ^ (3 : ℕ) + (3 / 2) * x ^ (5 : ℕ) + 6 * x ^ (5 : ℕ) * q - (15 / 2) * x ^ (5 : ℕ) * q ^ (2 : ℕ) - (135 / 2) * t - (765 / 2) * t * q + (135 / 2) * t * q ^ (2 : ℕ) + (45 / 2) * t * q ^ (3 : ℕ) - (585 / 2) * t * x + (255 / 2) * t * x * q + (495 / 2) * t * x * q ^ (2 : ℕ) - (465 / 2) * t * x * q ^ (3 : ℕ) - (489 / 2) * t * x ^ (2 : ℕ) + 267 * t * x ^ (2 : ℕ) * q - 288 * t * x ^ (2 : ℕ) * q ^ (2 : ℕ) - (327 / 2) * t * x ^ (2 : ℕ) * q ^ (3 : ℕ) - (11 / 4) * t * x ^ (3 : ℕ) + 103 * t * x ^ (3 : ℕ) * q - (1131 / 4) * t * x ^ (3 : ℕ) * q ^ (2 : ℕ) - (33 / 2) * t * x ^ (3 : ℕ) * q ^ (3 : ℕ) + (75 / 4) * t * x ^ (4 : ℕ) + (93 / 4) * t * x ^ (4 : ℕ) * q - (63 / 2) * t * x ^ (4 : ℕ) * q ^ (2 : ℕ) - 180 * t ^ (2 : ℕ) + 495 * t ^ (2 : ℕ) * q + 180 * t ^ (2 : ℕ) * q ^ (2 : ℕ) - 135 * t ^ (2 : ℕ) * q ^ (3 : ℕ) - 30 * t ^ (2 : ℕ) * x + 285 * t ^ (2 : ℕ) * x * q - 375 * t ^ (2 : ℕ) * x * q ^ (2 : ℕ) - 90 * t ^ (2 : ℕ) * x * q ^ (3 : ℕ) + 273 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 228 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q - 318 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q ^ (2 : ℕ) - 9 * t ^ (2 : ℕ) * x ^ (2 : ℕ) * q ^ (3 : ℕ) + (267 / 2) * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (249 / 2) * t ^ (2 : ℕ) * x ^ (3 : ℕ) * q - 33 * t ^ (2 : ℕ) * x ^ (3 : ℕ) * q ^ (2 : ℕ) + 9 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 9 * t ^ (2 : ℕ) * x ^ (4 : ℕ) * q + 270 * t ^ (3 : ℕ) - 270 * t ^ (3 : ℕ) * q ^ (2 : ℕ) + 450 * t ^ (3 : ℕ) * x + 270 * t ^ (3 : ℕ) * x * q - 180 * t ^ (3 : ℕ) * x * q ^ (2 : ℕ) + 198 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 180 * t ^ (3 : ℕ) * x ^ (2 : ℕ) * q - 18 * t ^ (3 : ℕ) * x ^ (2 : ℕ) * q ^ (2 : ℕ) + 18 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + 18 * t ^ (3 : ℕ) * x ^ (3 : ℕ) * q) / (12 * (x ^ 2 + 10 * x + 15) * (1 + x) ^ 2 * (q + 1)) := by
    unfold fhVhat fhVG nhFl; field_simp; ring
  rw [fh_comb_dec, hv]
  unfold nhLp
  apply mul_left_cancel₀ (mul_ne_zero hW hq.ne')
  rw [fh_clear_LR hW hq.ne' hq1 hR]
  unfold fhCLRbD0_0 fhCLRbD0_1 fhCLRbD0_2 fhCLRbD0_3 fhCLRbD0_4 fhCLRbD0_5 fhCLRbD0_6 fhCLRbD0_7 fhCLRbD0_8 fhCLRbD0_9 fhCLRbD0_10 fhCLRbD1_0 fhCLRbD1_1 fhCLRbD1_2 fhCLRbD1_3 fhCLRbD1_4 fhCLRbD1_5 fhCLRbD1_6 fhCLRbD1_7 fhCLRbD1_8 fhCLRbD1_9 fhCLRbD1_10 fhCLRbD2_0 fhCLRbD2_1 fhCLRbD2_2 fhCLRbD2_3 fhCLRbD2_4 fhCLRbD2_5 fhCLRbD2_6 fhCLRbD2_7 fhCLRbD2_8 fhCLRbD2_9 fhCLRbD2_10 fhCLRbD3_0 fhCLRbD3_1 fhCLRbD3_2 fhCLRbD3_3 fhCLRbD3_4 fhCLRbD3_5 fhCLRbD3_6 fhCLRbD3_7 fhCLRbD3_8 fhCLRbD3_9 fhCLRbD3_10 fhCLRbD4_0 fhCLRbD4_1 fhCLRbD4_2 fhCLRbD4_3 fhCLRbD4_4 fhCLRbD4_5 fhCLRbD4_6 fhCLRbD4_7 fhCLRbD4_8 fhCLRbD4_9 fhCLRbD4_10 fhCLRbD5_0 fhCLRbD5_1 fhCLRbD5_2 fhCLRbD5_3 fhCLRbD5_4 fhCLRbD5_5 fhCLRbD5_6 fhCLRbD5_7 fhCLRbD5_8 fhCLRbD5_9 fhCLRbD5_10 fhCLRbD6_0 fhCLRbD6_1 fhCLRbD6_2 fhCLRbD6_3 fhCLRbD6_4 fhCLRbD6_5 fhCLRbD6_6 fhCLRbD6_7 fhCLRbD6_8 fhCLRbD6_9 fhCLRbD6_10 fhCLRbD7_0 fhCLRbD7_1 fhCLRbD7_2 fhCLRbD7_3 fhCLRbD7_4 fhCLRbD7_5 fhCLRbD7_6 fhCLRbD7_7 fhCLRbD7_8 fhCLRbD7_9 fhCLRbD7_10
  unfold fhComb fhCv fhCL fhTPv fhTP fhKt fhHt fhE0 nhN nhNv nhNL
  ring

/-- `Je² ≤ 10/3` on the low-ratio domain (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)). -/
theorem fh_LR_J {t x q : ℝ} (ht1 : t ≤ 1 / 3) (hx1 : x ≤ 1) (hx : 0 < x) (ho : 1 ≤ 2 * t + x)
    (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    (t + x * (x + 2)) * q ^ 2 ≤ 10 / 3 * (1 + x) ^ 2 := by
  have h1 : (q * (2 * t + x)) ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ (by positivity) hqo 2
  have h2 : t + x * (x + 2) ≤ 10 / 3 * (2 * t + x) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
  nlinarith

/-- `WD/x ≤ 9/4` on the low-ratio domain (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)). -/
theorem fh_LR_WD {t x q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx : 0 < x) (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
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

/-- **The `v`-coefficient is negative** on the low-ratio domain
(`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)-(9)). -/
theorem fh_LR_Cv {t x k q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx1 : x ≤ 1) (hk : 1 ≤ k) (hq : 1 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    fhCv 6 0 t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have ho : 1 ≤ 2 * t + x := by linarith
  have hJ0 : 0 < t + x * (x + 2) := by positivity
  have hq0 : 0 < q := by linarith
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0.le
    linarith
  have hle := fh_Cv_le (α := 6) (M := 0) (t := t) (x := x) (k := k) (q := q) (by linarith)
    (by linarith) hD (by positivity)
  have hNv := fh_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hJ := fh_LR_J ht1 hx1 hx ho hq0.le hqo
  have hWD := fh_LR_WD ht0 ht1 hx0 hx hq0.le hqo
  have hA : 0 < x * q * k := by positivity
  have hNv0 : nhNv t x k q < 0 := by linarith
  have e1 : 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nhNv t x k q ≤
      4 * q * (11 / 3 * (1 + x) ^ 2) * nhNv t x k q := by
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
      4 * q * (1 + x) ^ 2 * (9 / 4) * (-nhNv t x k q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : 4 * q * (1 + x) ^ 2 * nhNv t x k q < 0 := mul_neg_of_pos_of_neg (by positivity) hNv0
  have e4 : 4 * q * (11 / 3 * (1 + x) ^ 2) * nhNv t x k q + 4 * q * (1 + x) ^ 2 * (9 / 4) * (-nhNv t x k q)
      = 17 / 12 * (4 * q * (1 + x) ^ 2 * nhNv t x k q) := by ring
  linarith

/-- **The low-ratio scalar exclusion** (`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION`). -/
theorem fh_lowRatio_core {t x k q v F : ℝ} (ht0 : 1 / 4 < t) (ht1 : t ≤ 1 / 3) (hk1 : 1 ≤ k)
    (hko : k < 2 * t + x) (h4 : 4 * t + x < 2) (hx1 : x < 1) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nhSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) (hcomb : fhComb 6 0 t x k q v (Real.log q) F < 0) :
    False := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hj : 1 < 2 * t + x := by linarith
  have hq0 : 0 < q := by linarith
  have hqo : q * (2 * t + x) ≤ 1 + x := by nlinarith
  have hCv := fh_LR_Cv ht0.le ht1 (by linarith) hx1.le hk1 hq.le hqo
  have hCL : fhCL 6 t x k q ≤ 0 := by
    unfold fhCL
    have hJ : (t + x * (x + 2)) * q ^ 2 ≤ 7 * (1 + x) ^ 2 := by
      have h1 : q * (2 * t + x) ≤ 1 + x := hqo
      have h2 : q ^ 2 * (2 * t + x) ^ 2 ≤ (1 + x) ^ 2 := by nlinarith [mul_le_mul h1 h1 (by positivity) (by linarith)]
      have h3 : t + x * (x + 2) ≤ 7 * (2 * t + x) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg q)]
    have := nhNL_nonpos (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq0.le (by linarith)
    have h7 : 0 ≤ 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) := by
      apply mul_nonneg (by positivity); linarith
    exact mul_nonpos_of_nonneg_of_nonpos h7 this
  -- the rational substitutions
  have hVG := fh_secN_lt_VG hx (by linarith : t < 1)
  rw [← hv] at hVG
  have hFl := nh_m2F_gt_Fl hq (by linarith : 0 < t + x) hW
  have hLp := nh_log_lt_Lp hq
  have hvh : v < fhVhat t x q := by
    unfold fhVhat
    have : 0 ≤ 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q) := by
      apply mul_nonneg (by linarith); linarith
    linarith
  have e1 := fh_comb_sub_v 6 0 t x k q (fhVhat t x q) v (nhLp q) 0
  have e2 := fh_comb_sub_L 6 0 t x k q v (nhLp q) (Real.log q) 0
  have e3 := fh_comb_sub_F 6 0 t x k q v (Real.log q) 0 F
  have m1 : (fhVhat t x q - v) * fhCv 6 0 t x k q < 0 := mul_neg_of_pos_of_neg (by linarith) hCv
  have m2 : (nhLp q - Real.log q) * fhCL 6 t x k q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hCL
  have hG : fhComb 6 0 t x k q (fhVhat t x q) (nhLp q) 0 < 0 := by
    have : (0 - F) * (4 * q * (1 + x) ^ 2 * 0) = 0 := by ring
    linarith
  -- the two shape endpoints
  have hy1 : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hA : 0 < fhComb 6 0 t x 1 q (fhVhat t x q) (nhLp q) 0 := by
    have hy : q - 1 ≤ 1 - 2 * t := by nlinarith
    exact lrh_unit_pos ht0.le ht1 hj.le hq.le hy
  have hB : 0 < fhComb 6 0 t x (2 * t + x) q (fhVhat t x q) (nhLp q) 0 := by
    have hy2 : q - 1 ≤ 1 - 2 * t := by nlinarith
    have h := fhCLRb_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hy2
    rw [← fh_LRb_link t x q hq0 hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by nlinarith
  have := fh_comb_pos_of_ends (by linarith) hq0.le hD hk1 hko.le hA hB
  linarith

/-- **The duration ratio exceeds one third** (`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (1)). -/
theorem fh_low_ratio (W : M2Window) (hF : W.ForwardNext) : 1 / 3 < W.nt := by
  by_contra h
  push Not at h
  obtain ⟨-, -, hx, hk1, hq, -, hv, -, -, hFl, -⟩ := nh_window_basic W
  exact fh_lowRatio_core (fh_window_quarter W) h hk1.le (fh_window_order W) (fh_window_four W)
    (fh_window_x_lt_one W) hq (by
      have := fh_window_swap W
      have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by
        have := fh_window_order W; have := fh_window_quarter W; linarith
      rwa [lt_div_iff₀ hden] at this) hv hFl
    (fh_window_comb W hF (α := 6) (M := 0) (by norm_num) le_rfl)

end SmoothedOctagon
