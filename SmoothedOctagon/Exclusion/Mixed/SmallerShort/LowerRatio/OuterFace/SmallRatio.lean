module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallRatio.NormBeta
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.RationalForms

/-!
# Smaller-short window, lower ratio, outer face, small ratios: shape concavity and the terminal faces

At the fixed slope `C = 8/17` and a fixed
norm `u ∈ {3/4, 19/25}`, `F₁` is concave in `r = 1/α ∈ [1/x, 1]` (`1 ≤ x ≤ 3/2`): with `b₄ ≤ 0`,
`b₃ < 0`, the residue `R = Q < 0` (shifted `R_f`, `R_v`), `2 ≤ Z ≤ S`, the curvature
is at most `H = 6b₃/x + 2b₂ + 2e²Q/S³ + 7e²/384 = -H_u(z)/(k S⁴(17x - 8)) < 0`. The
two shape faces `α = 1` and `α = x` are then univariate.

The terminal faces `α = 1`, `α = x` are proved by clearing the denominator of the full univariate
test (degree 8 and 12 in `z = x - 1`) and bounding its adverse monomials on `0 ≤ z ≤ 1/2`.

## Main API

* `lro_S_recip`: `F₁(x, α, x + (8/17)(α - 1), u) ≥ min(F₁ at α = x, F₁ at α = 1)`;
* `lro_S_face`: `F₁(x, α, x + (8/17)(α - 1), u) ≥ 1/1000` for `3/4 ≤ u ≤ 19/25`;
* `lro_S_main`: both outer tests are positive on the S branch.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `b₃` at `C = 8/17`, `u = 3 / 4`, in factored form. -/
theorem lro_S_b3_f {x : ℝ} (hx : 1 ≤ x) :
    lrb3 x (8 / 17) (3 / 4) = -(x * (34 * x - 33) * (102 * (x - 1) ^ 3 + 326 * (x - 1) ^ 2 + 213 * (x - 1) + 6)) /
      (6528 * (1 + x) * (17 * x - 8)) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrb3, lrq3, lrW4, lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_Q_f {x : ℝ} (hx : 1 ≤ x) :
    lrQ1 x (8 / 17) (3 / 4) = (1975026 * (x - 1) ^ 6 + 4628624 * (x - 1) ^ 5 - 9751999 * (x - 1) ^ 4 - 22148742 * (x - 1) ^ 3 - 11575796 * (x - 1) ^ 2 - 1745301 * (x - 1) - 381066) /
      (384 * (1 + x) * (17 * x - 8) ^ 4) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1,
    lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_b2_f {x : ℝ} (hx : 1 ≤ x) :
    lrb2 x (8 / 17) (3 / 4) = (214727 * x ^ 6 - 44302 * x ^ 5 - 520588 * x ^ 4 + 193724 * x ^ 3 + 214209 * x ^ 2 - 65634 * x + 5440) / (13056 * (1 + x) ^ 2 * (17 * x - 8) ^ 2) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrb2, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_H_f {x : ℝ} (hx : 1 ≤ x) :
    6 * lrb3 x (8 / 17) (3 / 4) / x + 2 * lrb2 x (8 / 17) (3 / 4) +
      2 * lrQ1 x (8 / 17) (3 / 4) * (x - 8 / 17) ^ 2 / (1 + x) ^ 3 + 7 / 96 * (x - 8 / 17) ^ 2 / 2 ^ 2 =
      (-104618 * (x - 1) ^ 7 - 944350 * (x - 1) ^ 6 - 3078173 * (x - 1) ^ 5 - 5115909 * (x - 1) ^ 4 - 5655650 * (x - 1) ^ 3 - 3066570 * (x - 1) ^ 2 - 473814 * (x - 1) - 26244) / (110976 * (1 + x) ^ 4 * (17 * x - 8)) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  rw [lro_S_b3_f hx, lro_S_b2_f hx, lro_S_Q_f hx]
  field_simp
  ring

theorem lro_S_cub_f {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 102 * z ^ 3 + 326 * z ^ 2 + 213 * z + 6 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3)]

theorem lro_S_Qn_f {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1975026 * z ^ 6 - 4628624 * z ^ 5 + 9751999 * z ^ 4 + 22148742 * z ^ 3 + 11575796 * z ^ 2 + 1745301 * z + 381066 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

/-- `b₃` at `C = 8/17`, `u = 19 / 25`, in factored form. -/
theorem lro_S_b3_v {x : ℝ} (hx : 1 ≤ x) :
    lrb3 x (8 / 17) (19 / 25) = -(x * (34 * x - 33) * (646 * (x - 1) ^ 3 + 2059 * (x - 1) ^ 2 + 1332 * (x - 1) + 21)) /
      (40800 * (1 + x) * (17 * x - 8)) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrb3, lrq3, lrW4, lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_Q_v {x : ℝ} (hx : 1 ≤ x) :
    lrQ1 x (8 / 17) (19 / 25) = (47400624 * (x - 1) ^ 6 + 103809667 * (x - 1) ^ 5 - 265528270 * (x - 1) ^ 4 - 559521750 * (x - 1) ^ 3 - 271140920 * (x - 1) ^ 2 - 29263997 * (x - 1) - 7166586) /
      (9600 * (1 + x) * (17 * x - 8) ^ 4) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1,
    lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_b2_v {x : ℝ} (hx : 1 ≤ x) :
    lrb2 x (8 / 17) (19 / 25) = (8435332 * x ^ 6 - 1970708 * x ^ 5 - 20734420 * x ^ 4 + 7702440 * x ^ 3 + 8629280 * x ^ 2 - 2555283 * x + 205632) / (510000 * (1 + x) ^ 2 * (17 * x - 8) ^ 2) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  simp only [lrb2, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem lro_S_H_v {x : ℝ} (hx : 1 ≤ x) :
    6 * lrb3 x (8 / 17) (19 / 25) / x + 2 * lrb2 x (8 / 17) (19 / 25) +
      2 * lrQ1 x (8 / 17) (19 / 25) * (x - 8 / 17) ^ 2 / (1 + x) ^ 3 + 7 / 96 * (x - 8 / 17) ^ 2 / 2 ^ 2 =
      (-67573113 * (x - 1) ^ 7 - 612084507 * (x - 1) ^ 6 - 2020804467 * (x - 1) ^ 5 - 3435750315 * (x - 1) ^ 4 - 3860747930 * (x - 1) ^ 3 - 2142156386 * (x - 1) ^ 2 - 362867574 * (x - 1) - 25280964) / (69360000 * (1 + x) ^ 4 * (17 * x - 8)) := by
  have h1 : 17 * x - 8 ≠ 0 := by linarith
  have h2 : 1 + x ≠ 0 := by linarith
  have h3 : x - 8 / 17 ≠ 0 := by linarith
  have h1' : x * 17 - 8 ≠ 0 := by linarith
  have h1'' : -8 + x * 17 ≠ 0 := by linarith
  have h1''' : -8 + 17 * x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  rw [lro_S_b3_v hx, lro_S_b2_v hx, lro_S_Q_v hx]
  field_simp
  ring

theorem lro_S_cub_v {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 646 * z ^ 3 + 2059 * z ^ 2 + 1332 * z + 21 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3)]

theorem lro_S_Qn_v {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -47400624 * z ^ 6 - 103809667 * z ^ 5 + 265528270 * z ^ 4 + 559521750 * z ^ 3 + 271140920 * z ^ 2 + 29263997 * z + 7166586 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

theorem lro_S_Tone_f {x : ℝ} (hx : 1 ≤ x) :
    lroF1 x 1 x (3 / 4) - 1 / 1000 = (-1 / 4 * (x - 1) ^ 8 - 5617 / 1152 * (x - 1) ^ 7 - 26875 / 768 * (x - 1) ^ 6 - 1571680247 / 14400000 * (x - 1) ^ 5 - 3459790127 / 28800000 * (x - 1) ^ 4 + 4810759 / 225000 * (x - 1) ^ 3 + 11005489 / 200000 * (x - 1) ^ 2 + 14323143 / 400000 * (x - 1) + 457947 / 200000) / ((1 + x) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F1_expl (by linarith) (by linarith) (by linarith)]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have h2 : 1 + x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  have hL0 : 2 * x + 9 ≠ 0 := by linarith
  rw [show 2 * (1 + x) + 7 * 1 = 2 * x + 9 by ring]
  generalize hL : 2 * x + 9 = L at hL0 ⊢
  field_simp
  subst hL
  ring

theorem lro_S_Tnone_f {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1 / 4 * z ^ 8 - 5617 / 1152 * z ^ 7 - 26875 / 768 * z ^ 6 - 1571680247 / 14400000 * z ^ 5 - 3459790127 / 28800000 * z ^ 4 + 4810759 / 225000 * z ^ 3 + 11005489 / 200000 * z ^ 2 + 14323143 / 400000 * z + 457947 / 200000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_S_Tdiag_f {x : ℝ} (hx : 1 ≤ x) :
    lroF1 x x (x + 8 / 17 * (x - 1)) (3 / 4) - 1 / 1000 = (-175673967 / 256 * (x - 1) ^ 12 - 1158755871 / 128 * (x - 1) ^ 11 - 1999222135900871 / 40800000 * (x - 1) ^ 10 - 17491781638007411 / 122400000 * (x - 1) ^ 9 - 24089227340352659 / 97920000 * (x - 1) ^ 8 - 15217111013443261 / 61200000 * (x - 1) ^ 7 - 29207167633902287 / 244800000 * (x - 1) ^ 6 + 3323543091605027 / 122400000 * (x - 1) ^ 5 + 254294436039889 / 3200000 * (x - 1) ^ 4 + 191024376990709 / 3600000 * (x - 1) ^ 3 + 14433622563919 / 800000 * (x - 1) ^ 2 + 24668502171 / 8000 * (x - 1) + 38248191387 / 200000) / (x ^ 4 * (1 + x) ^ 2 * (21 * x - 4) * (203 * x - 16) ^ 3) := by
  rw [lro_F1_expl (by linarith) (by linarith) (by linarith)]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have h2 : 1 + x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  have hL10 : 21 * x - 4 ≠ 0 := by linarith
  have hL20 : 203 * x - 16 ≠ 0 := by linarith
  rw [show x + (x + 8 / 17 * (x - 1)) = 2 * (21 * x - 4) / 17 by ring,
    show 2 * (2 * (21 * x - 4) / 17) + 7 * x = (203 * x - 16) / 17 by ring]
  generalize hL1 : 21 * x - 4 = L1 at hL10 ⊢
  generalize hL2 : 203 * x - 16 = L2 at hL20 ⊢
  field_simp
  subst hL1 hL2
  ring

theorem lro_S_Tndiag_f {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -175673967 / 256 * z ^ 12 - 1158755871 / 128 * z ^ 11 - 1999222135900871 / 40800000 * z ^ 10 - 17491781638007411 / 122400000 * z ^ 9 - 24089227340352659 / 97920000 * z ^ 8 - 15217111013443261 / 61200000 * z ^ 7 - 29207167633902287 / 244800000 * z ^ 6 + 3323543091605027 / 122400000 * z ^ 5 + 254294436039889 / 3200000 * z ^ 4 + 191024376990709 / 3600000 * z ^ 3 + 14433622563919 / 800000 * z ^ 2 + 24668502171 / 8000 * z + 38248191387 / 200000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_S_Tone_v {x : ℝ} (hx : 1 ≤ x) :
    lroF1 x 1 x (19 / 25) - 1 / 1000 = (-19 / 75 * (x - 1) ^ 8 - 9286 / 1875 * (x - 1) ^ 7 - 267853 / 7500 * (x - 1) ^ 6 - 12682229 / 112500 * (x - 1) ^ 5 - 2444717 / 18750 * (x - 1) ^ 4 + 4393571 / 900000 * (x - 1) ^ 3 + 19620029 / 450000 * (x - 1) ^ 2 + 140316167 / 3600000 * (x - 1) + 3943607 / 450000) / ((1 + x) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F1_expl (by linarith) (by linarith) (by linarith)]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have h2 : 1 + x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  have hL0 : 2 * x + 9 ≠ 0 := by linarith
  rw [show 2 * (1 + x) + 7 * 1 = 2 * x + 9 by ring]
  generalize hL : 2 * x + 9 = L at hL0 ⊢
  field_simp
  subst hL
  ring

theorem lro_S_Tnone_v {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -19 / 75 * z ^ 8 - 9286 / 1875 * z ^ 7 - 267853 / 7500 * z ^ 6 - 12682229 / 112500 * z ^ 5 - 2444717 / 18750 * z ^ 4 + 4393571 / 900000 * z ^ 3 + 19620029 / 450000 * z ^ 2 + 140316167 / 3600000 * z + 3943607 / 450000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_S_Tdiag_v {x : ℝ} (hx : 1 ≤ x) :
    lroF1 x x (x + 8 / 17 * (x - 1)) (19 / 25) - 1 / 1000 = (-1581065703 / 2500 * (x - 1) ^ 12 - 82803015687 / 10000 * (x - 1) ^ 11 - 598583632162537 / 13600000 * (x - 1) ^ 10 - 3783621965800859 / 30600000 * (x - 1) ^ 9 - 599977878999577 / 3060000 * (x - 1) ^ 8 - 2390080968901619 / 15300000 * (x - 1) ^ 7 + 432323006401807 / 61200000 * (x - 1) ^ 6 + 1198780005650827 / 7650000 * (x - 1) ^ 5 + 26799773543503 / 150000 * (x - 1) ^ 4 + 32506024786207 / 300000 * (x - 1) ^ 3 + 282531870555851 / 7200000 * (x - 1) ^ 2 + 2905360145099 / 360000 * (x - 1) + 329374000247 / 450000) / (x ^ 4 * (1 + x) ^ 2 * (21 * x - 4) * (203 * x - 16) ^ 3) := by
  rw [lro_F1_expl (by linarith) (by linarith) (by linarith)]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have h2 : 1 + x ≠ 0 := by linarith
  have h4 : x ≠ 0 := by linarith
  have hL10 : 21 * x - 4 ≠ 0 := by linarith
  have hL20 : 203 * x - 16 ≠ 0 := by linarith
  rw [show x + (x + 8 / 17 * (x - 1)) = 2 * (21 * x - 4) / 17 by ring,
    show 2 * (2 * (21 * x - 4) / 17) + 7 * x = (203 * x - 16) / 17 by ring]
  generalize hL1 : 21 * x - 4 = L1 at hL10 ⊢
  generalize hL2 : 203 * x - 16 = L2 at hL20 ⊢
  field_simp
  subst hL1 hL2
  ring

theorem lro_S_Tndiag_v {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1581065703 / 2500 * z ^ 12 - 82803015687 / 10000 * z ^ 11 - 598583632162537 / 13600000 * z ^ 10 - 3783621965800859 / 30600000 * z ^ 9 - 599977878999577 / 3060000 * z ^ 8 - 2390080968901619 / 15300000 * z ^ 7 + 432323006401807 / 61200000 * z ^ 6 + 1198780005650827 / 7650000 * z ^ 5 + 26799773543503 / 150000 * z ^ 4 + 32506024786207 / 300000 * z ^ 3 + 282531870555851 / 7200000 * z ^ 2 + 2905360145099 / 360000 * z + 329374000247 / 450000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

/-! ### Assembly of the S branch -/

theorem lro_S_signs {x u : ℝ} (hu : u = 3 / 4 ∨ u = 19 / 25) (hx1 : 1 ≤ x) (hx : x ≤ 3 / 2) :
    lrb3 x (8 / 17) u ≤ 0 ∧ lrQ1 x (8 / 17) u ≤ 0 ∧
      6 * lrb3 x (8 / 17) u / x + 2 * lrb2 x (8 / 17) u +
        2 * lrQ1 x (8 / 17) u * (x - 8 / 17) ^ 2 / (1 + x) ^ 3 +
          7 / 96 * (x - 8 / 17) ^ 2 / 2 ^ 2 ≤ 0 := by
  have hz0 : 0 ≤ x - 1 := by linarith
  have hz1 : x - 1 ≤ 1 / 2 := by linarith
  have hd1 : 0 < 17 * x - 8 := by linarith
  rcases hu with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · rw [lro_S_b3_f hx1]
      have := lro_S_cub_f hz0 hz1
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : 0 ≤ x * (34 * x - 33) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · rw [lro_S_Q_f hx1]
      have := lro_S_Qn_f hz0 hz1
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · rw [lro_S_H_f hx1]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3, pow_nonneg hz0 4, pow_nonneg hz0 5,
        pow_nonneg hz0 6, pow_nonneg hz0 7]
  · refine ⟨?_, ?_, ?_⟩
    · rw [lro_S_b3_v hx1]
      have := lro_S_cub_v hz0 hz1
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : 0 ≤ x * (34 * x - 33) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · rw [lro_S_Q_v hx1]
      have := lro_S_Qn_v hz0 hz1
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · rw [lro_S_H_v hx1]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3, pow_nonneg hz0 4, pow_nonneg hz0 5,
        pow_nonneg hz0 6, pow_nonneg hz0 7]

/-- **Reciprocal-shape concavity at `C = 8/17`**: at `u ∈ {3/4, 19/25}`, `F₁` on the slope
`8/17` is at least its smaller value at `α = 1` and `α = x`. -/
theorem lro_S_recip {x a u : ℝ} (hu : u = 3 / 4 ∨ u = 19 / 25) (ha1 : 1 ≤ a) (hax : a ≤ x)
    (hx : x ≤ 3 / 2) :
    min (lroF1 x x (x + 8 / 17 * (x - 1)) u) (lroF1 x 1 (x + 8 / 17 * (1 - 1)) u) ≤
      lroF1 x a (x + 8 / 17 * (a - 1)) u := by
  have hx1 : 1 ≤ x := le_trans ha1 hax
  have hx0 : 0 < x := by linarith
  obtain ⟨hb3, hQ, hH⟩ := lro_S_signs hu hx1 hx
  have hZ : ∀ a' : ℝ, 1 ≤ a' → a' ≤ x → 0 < 1 + 8 / 17 + (x - 8 / 17) * (1 / a') := by
    intro a' h1 h2
    have : 0 < (x - 8 / 17) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  have hrep : ∀ a' : ℝ, 1 ≤ a' → a' ≤ x → lroF1 x a' (x + 8 / 17 * (a' - 1)) u =
      lrG (lrb0 x (8 / 17) u) (lrb1 x (8 / 17) u) (lrb2 x (8 / 17) u) (lrb3 x (8 / 17) u)
        (lrb4 x u) (lrQ1 x (8 / 17) u) (1 + 8 / 17) (x - 8 / 17) (1 / a') :=
    fun a' h1 h2 => lro_F1_rG hx0 (by linarith) rfl (by linarith) (hZ a' h1 h2)
  rw [hrep a ha1 hax, hrep x hx1 le_rfl, hrep 1 le_rfl hx1]
  apply lrG_min (one_div_le_one_div_of_le (by linarith) hax)
    (one_div_le_one_div_of_le one_pos ha1)
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 1 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    constructor
    · nlinarith
    · nlinarith
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 1 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    have hZl : 2 ≤ 1 + 8 / 17 + (x - 8 / 17) * s := by nlinarith
    have hZu : 1 + 8 / 17 + (x - 8 / 17) * s ≤ 1 + x := by nlinarith
    have := lr_curv_bound (b2 := lrb2 x (8 / 17) u) (lrg4_nonpos (u := u) hx0) hb3 hQ hx0 h1
      (by norm_num) hZl hZu
    linarith

/-- The two terminal faces at the norm endpoints. -/
theorem lro_S_terminals {x u : ℝ} (hu : u = 3 / 4 ∨ u = 19 / 25) (hx1 : 1 ≤ x)
    (hx : x ≤ 3 / 2) :
    1 / 1000 < lroF1 x x (x + 8 / 17 * (x - 1)) u ∧
      1 / 1000 < lroF1 x 1 (x + 8 / 17 * (1 - 1)) u := by
  have hz0 : 0 ≤ x - 1 := by linarith
  have hz1 : x - 1 ≤ 1 / 2 := by linarith
  have hb : x + 8 / 17 * (1 - 1) = x := by ring
  rw [hb]
  have hd1 : 0 < 21 * x - 4 := by linarith
  have hd2 : 0 < 203 * x - 16 := by linarith
  rcases hu with rfl | rfl
  · constructor
    · have h := lro_S_Tdiag_f hx1
      have hn := lro_S_Tndiag_f hz0 hz1
      have : 0 < lroF1 x x (x + 8 / 17 * (x - 1)) (3 / 4) - 1 / 1000 := by
        rw [h]; apply div_pos hn (by positivity)
      linarith
    · have h := lro_S_Tone_f hx1
      have hn := lro_S_Tnone_f hz0 hz1
      have : 0 < lroF1 x 1 x (3 / 4) - 1 / 1000 := by
        rw [h]; apply div_pos hn (by positivity)
      linarith
  · constructor
    · have h := lro_S_Tdiag_v hx1
      have hn := lro_S_Tndiag_v hz0 hz1
      have : 0 < lroF1 x x (x + 8 / 17 * (x - 1)) (19 / 25) - 1 / 1000 := by
        rw [h]; apply div_pos hn (by positivity)
      linarith
    · have h := lro_S_Tone_v hx1
      have hn := lro_S_Tnone_v hz0 hz1
      have : 0 < lroF1 x 1 x (19 / 25) - 1 / 1000 := by
        rw [h]; apply div_pos hn (by positivity)
      linarith

/-- **The fixed-slope S face**: `F₁ > 1/1000` on the slope `C = 8/17` for `3/4 ≤ u ≤ 19/25`. -/
theorem lro_S_face {x a u : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2) (hu0 : 3 / 4 ≤ u)
    (hu1 : u ≤ 19 / 25) : 1 / 1000 < lroF1 x a (x + 8 / 17 * (a - 1)) u := by
  have hx1 : 1 ≤ x := le_trans ha1 hax
  have hm := lro_F1_umin (x := x) (a := a) (b := x + 8 / 17 * (a - 1)) hu0 hu1
    (by positivity : a ≠ 0)
  have h1 := lro_S_recip (u := 3 / 4) (Or.inl rfl) ha1 hax hx
  have h2 := lro_S_recip (u := 19 / 25) (Or.inr rfl) ha1 hax hx
  obtain ⟨t1, t2⟩ := lro_S_terminals (u := 3 / 4) (Or.inl rfl) hx1 hx
  obtain ⟨t3, t4⟩ := lro_S_terminals (u := 19 / 25) (Or.inr rfl) hx1 hx
  have m1 := lt_of_lt_of_le (lt_min t1 t2) h1
  have m2 := lt_of_lt_of_le (lt_min t3 t4) h2
  exact lt_of_lt_of_le (lt_min m1 m2) hm

/-- **The S branch of the outer face**: for `1 ≤ α ≤ x ≤ 3/2`,
`β = x + C(α - 1)` with `8/17 ≤ C ≤ 10/13`, `3/4 ≤ u ≤ 19/25`: `F₀ ≥ F₁ > 0`. -/
theorem lro_S_main {x a b u C : ℝ} (ha1 : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ 3 / 2)
    (hC0 : 8 / 17 ≤ C) (hC1 : C ≤ 10 / 13) (hb : b = x + C * (a - 1)) (hu0 : 3 / 4 ≤ u)
    (hu1 : u ≤ 19 / 25) : 0 < lroF1 x a b u ∧ 0 < lroF0 x a b u := by
  have hx1 : 1 ≤ x := le_trans ha1 hax
  have hA : 0 ≤ a - 1 := by linarith
  have hF := lro_S_face ha1 hax hx hu0 hu1
  have hl := lro_S_beta (C := C) ha1 hax hx hu0 hu1 hC0 hC1
  rw [← hb] at hl
  have hxb : x ≤ b := by rw [hb]; nlinarith
  have hbx : b ≤ a * x := by rw [hb]; nlinarith
  have h0 := lro_S_F0_ge ha1 hax hx hxb hbx hu0 hu1
  constructor <;> linarith

end SmoothedOctagon
