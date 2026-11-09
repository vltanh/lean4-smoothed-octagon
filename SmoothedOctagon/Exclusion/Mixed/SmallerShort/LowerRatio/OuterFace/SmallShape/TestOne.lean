module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Shapes

/-!
# Smaller-short window, lower ratio, outer face, small shapes: the test `F₁`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`,
`1/2 ≤ C ≤ 10/13`, `3/4 ≤ u ≤ 19/25`:

* `w₀ > 6/7` (its value at `u = 19/25` minus `6/7` has a positive numerator, and `w₀` decreases
  in `u`), so `β ↦ F₁` is concave and `C ∈ {1/2, 10/13}`;
* norm concavity gives `u ∈ {3/4, 19/25}`;
* the reciprocal-shape curvature is at most `5b₃ + 2b₂ + 21/800 < 0` on `r ∈ [5/6, 1]`
  (residue `Q < 0`), so `α` is `6/5` or the lower shape `α_*(x) = 1` (`x ≤ 5/3`),
  `(6x + 3)/13` (`x ≥ 5/3`, below the cap);
* the terminal curves are positive.

The residue, curvature and terminal signs are univariate signs in `x`, each cleared and bounded
termwise.

## Main API

* `lro_B_w0`, `lro_B_recip`, `lro_B_F1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `N(3/2 + z, 6/5 - c)/1225`, where `w₀(x, α, 19/25) - 6/7 = N/(1225α⁴(x + 1))`. -/
noncomputable def lrPwN (c z : ℝ) : ℝ :=
  -36 / 1225 * c ^ 4 * z ^ 2 - 311 / 1225 * c ^ 4 * z - 23 / 70 * c ^ 4 - 72 / 1225 * c ^ 3 * z ^ 3 - 1096 / 6125 * c ^ 3 * z ^ 2 + 5534 / 6125 * c ^ 3 * z + 1992 / 1225 * c ^ 3 + 2036 / 6125 * c ^ 2 * z ^ 3 + 6572 / 4375 * c ^ 2 * z ^ 2 - 7086 / 30625 * c ^ 2 * z - 32961 / 12250 * c ^ 2 - 2608 / 4375 * c * z ^ 3 - 451326 / 153125 * c * z ^ 2 - 334686 / 153125 * c * z + 82989 / 61250 * c + 7631 / 21875 * z ^ 3 + 2783533 / 1531250 * z ^ 2 + 6328071 / 3062500 * z + 253971 / 1225000

theorem lrPwN_pos {c z : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ (1 / 5 : ℝ)) (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < lrPwN c z := by
  unfold lrPwN
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ c),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c * z),
    (by positivity : (0 : ℝ) ≤ c ^ 2 * z ^ 2),
    (by positivity : (0 : ℝ) ≤ c ^ 2 * z ^ 3),
    (by positivity : (0 : ℝ) ≤ c ^ 3),
    (by positivity : (0 : ℝ) ≤ c ^ 3 * z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ c ^ 3 * z),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c ^ 2 * z ^ 3),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c ^ 3),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c ^ 3 * z),
    mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ c ^ 3 * z ^ 2)]

theorem lro_B_Q_hf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -z ^ 6 - 125 / 24 * z ^ 5 - 191 / 48 * z ^ 4 + 641 / 48 * z ^ 3 + 2425 / 96 * z ^ 2 + 727 / 48 * z + 1237 / 384 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

theorem lro_B_Q_hf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) - lrQ1 x (1 / 2) (3 / 4) = (-(x - (3 / 2 : ℝ)) ^ 6 - 125 / 24 * (x - (3 / 2 : ℝ)) ^ 5 - 191 / 48 * (x - (3 / 2 : ℝ)) ^ 4 + 641 / 48 * (x - (3 / 2 : ℝ)) ^ 3 + 2425 / 96 * (x - (3 / 2 : ℝ)) ^ 2 + 727 / 48 * (x - (3 / 2 : ℝ)) + 1237 / 384) / ((x + 1) * (2 * x - 1) ^ 4) := by
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 2 * x - 1 ≠ 0 := by nlinarith
  have hd6 : x * 2 - 1 ≠ 0 := by nlinarith
  have hd7 : -1 + x * 2 ≠ 0 := by nlinarith
  have hd8 : -1 + 2 * x ≠ 0 := by nlinarith
  have hd9 : x - 1 / 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_Q_hf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    lrQ1 x (1 / 2) (3 / 4) < (0 : ℝ) := by
  have hid := lro_B_Q_hf_id h0 h1
  have hn := lro_B_Q_hf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x - 1 := by nlinarith
  have hD : 0 < (x + 1) * (2 * x - 1) ^ 4 := (mul_pos hP0 (pow_pos hP1 4))
  have : 0 < (0 : ℝ) - lrQ1 x (1 / 2) (3 / 4) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_M1_hf_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 5 / 8 * z ^ 7 + 189 / 32 * z ^ 6 + 89 / 4 * z ^ 5 + 206921 / 4800 * z ^ 4 + 147873 / 3200 * z ^ 3 + 1043323 / 38400 * z ^ 2 + 10083 / 1280 * z + 1123 / 1536 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_M1_hf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-21 / 800 : ℝ) - (2 * lrb2 x (1 / 2) (3 / 4) + 5 * lrb3 x (1 / 2) (3 / 4)) = (5 / 8 * (x - (3 / 2 : ℝ)) ^ 7 + 189 / 32 * (x - (3 / 2 : ℝ)) ^ 6 + 89 / 4 * (x - (3 / 2 : ℝ)) ^ 5 + 206921 / 4800 * (x - (3 / 2 : ℝ)) ^ 4 + 147873 / 3200 * (x - (3 / 2 : ℝ)) ^ 3 + 1043323 / 38400 * (x - (3 / 2 : ℝ)) ^ 2 + 10083 / 1280 * (x - (3 / 2 : ℝ)) + 1123 / 1536) / ((x + 1) ^ 2 * (2 * x - 1) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 2 * x - 1 ≠ 0 := by nlinarith
  have hd6 : x * 2 - 1 ≠ 0 := by nlinarith
  have hd7 : -1 + x * 2 ≠ 0 := by nlinarith
  have hd8 : -1 + 2 * x ≠ 0 := by nlinarith
  have hd9 : x - 1 / 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_M1_hf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (1 / 2) (3 / 4) + 5 * lrb3 x (1 / 2) (3 / 4)) < (-21 / 800 : ℝ) := by
  have hid := lro_B_M1_hf_id h0 h1
  have hn := lro_B_M1_hf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x - 1 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (2 * x - 1) ^ 2 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 2))
  have : 0 < (-21 / 800 : ℝ) - (2 * lrb2 x (1 / 2) (3 / 4) + 5 * lrb3 x (1 / 2) (3 / 4)) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T65_hf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -625 / 432 * z ^ 9 - 30883205 / 746496 * z ^ 8 - 116853163 / 248832 * z ^ 7 - 2511335448581 / 933120000 * z ^ 6 - 66089628239 / 8100000 * z ^ 5 - 155292486024659 / 12441600000 * z ^ 4 - 31428950969771 / 4147200000 * z ^ 3 + 56510403287359 / 37324800000 * z ^ 2 + 10761085295233 / 2488320000 * z + 1181006740963 / 746496000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem lro_B_T65_hf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) = (-625 / 432 * (x - (3 / 2 : ℝ)) ^ 9 - 30883205 / 746496 * (x - (3 / 2 : ℝ)) ^ 8 - 116853163 / 248832 * (x - (3 / 2 : ℝ)) ^ 7 - 2511335448581 / 933120000 * (x - (3 / 2 : ℝ)) ^ 6 - 66089628239 / 8100000 * (x - (3 / 2 : ℝ)) ^ 5 - 155292486024659 / 12441600000 * (x - (3 / 2 : ℝ)) ^ 4 - 31428950969771 / 4147200000 * (x - (3 / 2 : ℝ)) ^ 3 + 56510403287359 / 37324800000 * (x - (3 / 2 : ℝ)) ^ 2 + 10761085295233 / 2488320000 * (x - (3 / 2 : ℝ)) + 1181006740963 / 746496000) /
      ((10 * x + 13) * (x + 1) ^ 2 * (2 * x + 11) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 1 / 2 * (6 / 5 - 1)) = (10 * x + 13) / (10 : ℝ) by ring,
    show 2 * ((10 * x + 13) / (10 : ℝ)) + 7 * (6 / 5) = (2 * x + 11) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 10 * x + 13 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 2 * x + 11 ≠ 0 := by nlinarith
  have hp0 : 10 * x + 13 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 11 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 10 * x + 13 = p at hp0 ⊢
  generalize hq : 2 * x + 11 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T65_hf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (3 / 4) := by
  have hid := lro_B_T65_hf_id h0 h1
  have hn := lro_B_T65_hf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 10 * x + 13 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 2 * x + 11 := by nlinarith
  have hD : 0 < (10 * x + 13) * (x + 1) ^ 2 * (2 * x + 11) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T13_hf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -874577 / 2 * z ^ 12 - 88184357 / 12 * z ^ 11 - 1584801308617 / 28125 * z ^ 10 - 541601150382371 / 2025000 * z ^ 9 - 10500977835997489 / 11664000 * z ^ 8 - 4002825537397115273 / 1749600000 * z ^ 7 - 46007909098796736871 / 10497600000 * z ^ 6 - 75199977761218909651 / 12597120000 * z ^ 5 - 239909931802640439041 / 47239200000 * z ^ 4 - 120924343680865332751 / 70858800000 * z ^ 3 + 474433798868158092691 / 425152800000 * z ^ 2 + 421997616454495604809 / 318864600000 * z + 92560608054967214851 / 239148450000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_B_T13_hf_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (3 / 4) - (0 : ℝ) = (-874577 / 2 * (x - (5 / 3 : ℝ)) ^ 12 - 88184357 / 12 * (x - (5 / 3 : ℝ)) ^ 11 - 1584801308617 / 28125 * (x - (5 / 3 : ℝ)) ^ 10 - 541601150382371 / 2025000 * (x - (5 / 3 : ℝ)) ^ 9 - 10500977835997489 / 11664000 * (x - (5 / 3 : ℝ)) ^ 8 - 4002825537397115273 / 1749600000 * (x - (5 / 3 : ℝ)) ^ 7 - 46007909098796736871 / 10497600000 * (x - (5 / 3 : ℝ)) ^ 6 - 75199977761218909651 / 12597120000 * (x - (5 / 3 : ℝ)) ^ 5 - 239909931802640439041 / 47239200000 * (x - (5 / 3 : ℝ)) ^ 4 - 120924343680865332751 / 70858800000 * (x - (5 / 3 : ℝ)) ^ 3 + 474433798868158092691 / 425152800000 * (x - (5 / 3 : ℝ)) ^ 2 + 421997616454495604809 / 318864600000 * (x - (5 / 3 : ℝ)) + 92560608054967214851 / 239148450000) /
      ((11 * x - 1) * (x + 1) ^ 2 * (86 * x + 17) ^ 3 * (2 * x + 1) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((6 * x + 3) / 13) + (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) = (11 * x - 1) / (13 / 2 : ℝ) by ring,
    show 2 * ((11 * x - 1) / (13 / 2 : ℝ)) + 7 * ((6 * x + 3) / 13) = (86 * x + 17) / (13 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 11 * x - 1 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 86 * x + 17 ≠ 0 := by nlinarith
  have hd3 : 2 * x + 1 ≠ 0 := by nlinarith
  have hp0 : 11 * x - 1 ≠ 0 := by nlinarith
  have hq0 : 86 * x + 17 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 11 * x - 1 = p at hp0 ⊢
  generalize hq : 86 * x + 17 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T13_hf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have hid := lro_B_T13_hf_id h0 h1
  have hn := lro_B_T13_hf_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 11 * x - 1 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 86 * x + 17 := by nlinarith
  have hP3 : 0 < 2 * x + 1 := by nlinarith
  have hD : 0 < (11 * x - 1) * (x + 1) ^ 2 * (86 * x + 17) ^ 3 * (2 * x + 1) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_Q_hv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -24 / 25 * z ^ 6 - 2911 / 600 * z ^ 5 - 3391 / 1200 * z ^ 4 + 1433 / 96 * z ^ 3 + 124249 / 4800 * z ^ 2 + 141811 / 9600 * z + 11411 / 3840 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

theorem lro_B_Q_hv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) - lrQ1 x (1 / 2) (19 / 25) = (-24 / 25 * (x - (3 / 2 : ℝ)) ^ 6 - 2911 / 600 * (x - (3 / 2 : ℝ)) ^ 5 - 3391 / 1200 * (x - (3 / 2 : ℝ)) ^ 4 + 1433 / 96 * (x - (3 / 2 : ℝ)) ^ 3 + 124249 / 4800 * (x - (3 / 2 : ℝ)) ^ 2 + 141811 / 9600 * (x - (3 / 2 : ℝ)) + 11411 / 3840) / ((x + 1) * (2 * x - 1) ^ 4) := by
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 2 * x - 1 ≠ 0 := by nlinarith
  have hd6 : x * 2 - 1 ≠ 0 := by nlinarith
  have hd7 : -1 + x * 2 ≠ 0 := by nlinarith
  have hd8 : -1 + 2 * x ≠ 0 := by nlinarith
  have hd9 : x - 1 / 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_Q_hv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    lrQ1 x (1 / 2) (19 / 25) < (0 : ℝ) := by
  have hid := lro_B_Q_hv_id h0 h1
  have hn := lro_B_Q_hv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x - 1 := by nlinarith
  have hD : 0 < (x + 1) * (2 * x - 1) ^ 4 := (mul_pos hP0 (pow_pos hP1 4))
  have : 0 < (0 : ℝ) - lrQ1 x (1 / 2) (19 / 25) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_M1_hv_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 19 / 30 * z ^ 7 + 11218 / 1875 * z ^ 6 + 338053 / 15000 * z ^ 5 + 655349 / 15000 * z ^ 4 + 563417 / 12000 * z ^ 3 + 66779 / 2400 * z ^ 2 + 15847 / 1920 * z + 53 / 64 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_M1_hv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-21 / 800 : ℝ) - (2 * lrb2 x (1 / 2) (19 / 25) + 5 * lrb3 x (1 / 2) (19 / 25)) = (19 / 30 * (x - (3 / 2 : ℝ)) ^ 7 + 11218 / 1875 * (x - (3 / 2 : ℝ)) ^ 6 + 338053 / 15000 * (x - (3 / 2 : ℝ)) ^ 5 + 655349 / 15000 * (x - (3 / 2 : ℝ)) ^ 4 + 563417 / 12000 * (x - (3 / 2 : ℝ)) ^ 3 + 66779 / 2400 * (x - (3 / 2 : ℝ)) ^ 2 + 15847 / 1920 * (x - (3 / 2 : ℝ)) + 53 / 64) / ((x + 1) ^ 2 * (2 * x - 1) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 2 * x - 1 ≠ 0 := by nlinarith
  have hd6 : x * 2 - 1 ≠ 0 := by nlinarith
  have hd7 : -1 + x * 2 ≠ 0 := by nlinarith
  have hd8 : -1 + 2 * x ≠ 0 := by nlinarith
  have hd9 : x - 1 / 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_M1_hv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (1 / 2) (19 / 25) + 5 * lrb3 x (1 / 2) (19 / 25)) < (-21 / 800 : ℝ) := by
  have hid := lro_B_M1_hv_id h0 h1
  have hn := lro_B_M1_hv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x - 1 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (2 * x - 1) ^ 2 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 2))
  have : 0 < (-21 / 800 : ℝ) - (2 * lrb2 x (1 / 2) (19 / 25) + 5 * lrb3 x (1 / 2) (19 / 25)) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T65_hv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -475 / 324 * z ^ 9 - 6806581 / 162000 * z ^ 8 - 1163265817 / 2430000 * z ^ 7 - 80544989537 / 29160000 * z ^ 6 - 154765422449 / 18225000 * z ^ 5 - 326702273117 / 24300000 * z ^ 4 - 5378214045151 / 583200000 * z ^ 3 + 74688909281 / 583200000 * z ^ 2 + 6023042711 / 1440000 * z + 569405039 / 288000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem lro_B_T65_hv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) = (-475 / 324 * (x - (3 / 2 : ℝ)) ^ 9 - 6806581 / 162000 * (x - (3 / 2 : ℝ)) ^ 8 - 1163265817 / 2430000 * (x - (3 / 2 : ℝ)) ^ 7 - 80544989537 / 29160000 * (x - (3 / 2 : ℝ)) ^ 6 - 154765422449 / 18225000 * (x - (3 / 2 : ℝ)) ^ 5 - 326702273117 / 24300000 * (x - (3 / 2 : ℝ)) ^ 4 - 5378214045151 / 583200000 * (x - (3 / 2 : ℝ)) ^ 3 + 74688909281 / 583200000 * (x - (3 / 2 : ℝ)) ^ 2 + 6023042711 / 1440000 * (x - (3 / 2 : ℝ)) + 569405039 / 288000) /
      ((10 * x + 13) * (x + 1) ^ 2 * (2 * x + 11) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 1 / 2 * (6 / 5 - 1)) = (10 * x + 13) / (10 : ℝ) by ring,
    show 2 * ((10 * x + 13) / (10 : ℝ)) + 7 * (6 / 5) = (2 * x + 11) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 10 * x + 13 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 2 * x + 11 ≠ 0 := by nlinarith
  have hp0 : 10 * x + 13 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 11 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 10 * x + 13 = p at hp0 ⊢
  generalize hq : 2 * x + 11 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T65_hv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (19 / 25) := by
  have hid := lro_B_T65_hv_id h0 h1
  have hn := lro_B_T65_hv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 10 * x + 13 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 2 * x + 11 := by nlinarith
  have hD : 0 < (10 * x + 13) * (x + 1) ^ 2 * (2 * x + 11) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T13_hv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -251878176 / 625 * z ^ 12 - 4131080176 / 625 * z ^ 11 - 12552126824363 / 253125 * z ^ 10 - 177495718281841 / 759375 * z ^ 9 - 163180650597407 / 202500 * z ^ 8 - 9913586343037247 / 4556250 * z ^ 7 - 62200675653395617 / 13668750 * z ^ 6 - 37809967313449643 / 5467500 * z ^ 5 - 27246745103847007583 / 3936600000 * z ^ 4 - 44075389683354628651 / 11809800000 * z ^ 3 - 8496962660392372621 / 47239200000 * z ^ 2 + 283711885474715769929 / 318864600000 * z + 79887180512546651491 / 239148450000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_B_T13_hv_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (19 / 25) - (0 : ℝ) = (-251878176 / 625 * (x - (5 / 3 : ℝ)) ^ 12 - 4131080176 / 625 * (x - (5 / 3 : ℝ)) ^ 11 - 12552126824363 / 253125 * (x - (5 / 3 : ℝ)) ^ 10 - 177495718281841 / 759375 * (x - (5 / 3 : ℝ)) ^ 9 - 163180650597407 / 202500 * (x - (5 / 3 : ℝ)) ^ 8 - 9913586343037247 / 4556250 * (x - (5 / 3 : ℝ)) ^ 7 - 62200675653395617 / 13668750 * (x - (5 / 3 : ℝ)) ^ 6 - 37809967313449643 / 5467500 * (x - (5 / 3 : ℝ)) ^ 5 - 27246745103847007583 / 3936600000 * (x - (5 / 3 : ℝ)) ^ 4 - 44075389683354628651 / 11809800000 * (x - (5 / 3 : ℝ)) ^ 3 - 8496962660392372621 / 47239200000 * (x - (5 / 3 : ℝ)) ^ 2 + 283711885474715769929 / 318864600000 * (x - (5 / 3 : ℝ)) + 79887180512546651491 / 239148450000) /
      ((11 * x - 1) * (x + 1) ^ 2 * (86 * x + 17) ^ 3 * (2 * x + 1) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((6 * x + 3) / 13) + (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) = (11 * x - 1) / (13 / 2 : ℝ) by ring,
    show 2 * ((11 * x - 1) / (13 / 2 : ℝ)) + 7 * ((6 * x + 3) / 13) = (86 * x + 17) / (13 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 11 * x - 1 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 86 * x + 17 ≠ 0 := by nlinarith
  have hd3 : 2 * x + 1 ≠ 0 := by nlinarith
  have hp0 : 11 * x - 1 ≠ 0 := by nlinarith
  have hq0 : 86 * x + 17 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 11 * x - 1 = p at hp0 ⊢
  generalize hq : 86 * x + 17 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T13_hv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have hid := lro_B_T13_hv_id h0 h1
  have hn := lro_B_T13_hv_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 11 * x - 1 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 86 * x + 17 := by nlinarith
  have hP3 : 0 < 2 * x + 1 := by nlinarith
  have hD : 0 < (11 * x - 1) * (x + 1) ^ 2 * (86 * x + 17) ^ 3 * (2 * x + 1) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_Q_tf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -129623 / 64 * z ^ 6 - 1538407 / 192 * z ^ 5 + 2999659 / 768 * z ^ 4 + 4363537 / 128 * z ^ 3 + 92864897 / 3072 * z ^ 2 + 7044843 / 1024 * z + 24226009 / 12288 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

theorem lro_B_Q_tf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) - lrQ1 x (10 / 13) (3 / 4) = (-129623 / 64 * (x - (3 / 2 : ℝ)) ^ 6 - 1538407 / 192 * (x - (3 / 2 : ℝ)) ^ 5 + 2999659 / 768 * (x - (3 / 2 : ℝ)) ^ 4 + 4363537 / 128 * (x - (3 / 2 : ℝ)) ^ 3 + 92864897 / 3072 * (x - (3 / 2 : ℝ)) ^ 2 + 7044843 / 1024 * (x - (3 / 2 : ℝ)) + 24226009 / 12288) / ((x + 1) * (13 * x - 10) ^ 4) := by
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd6 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd7 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd8 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd9 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_Q_tf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    lrQ1 x (10 / 13) (3 / 4) < (0 : ℝ) := by
  have hid := lro_B_Q_tf_id h0 h1
  have hn := lro_B_Q_tf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x + 1) * (13 * x - 10) ^ 4 := (mul_pos hP0 (pow_pos hP1 4))
  have : 0 < (0 : ℝ) - lrQ1 x (10 / 13) (3 / 4) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_M1_tf_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 845 / 32 * z ^ 7 + 29575 / 128 * z ^ 6 + 12549 / 16 * z ^ 5 + 660383099 / 499200 * z ^ 4 + 596595607 / 499200 * z ^ 3 + 1183300271 / 1996800 * z ^ 2 + 10472361 / 66560 * z + 3291829 / 319488 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_M1_tf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-21 / 800 : ℝ) - (2 * lrb2 x (10 / 13) (3 / 4) + 5 * lrb3 x (10 / 13) (3 / 4)) = (845 / 32 * (x - (3 / 2 : ℝ)) ^ 7 + 29575 / 128 * (x - (3 / 2 : ℝ)) ^ 6 + 12549 / 16 * (x - (3 / 2 : ℝ)) ^ 5 + 660383099 / 499200 * (x - (3 / 2 : ℝ)) ^ 4 + 596595607 / 499200 * (x - (3 / 2 : ℝ)) ^ 3 + 1183300271 / 1996800 * (x - (3 / 2 : ℝ)) ^ 2 + 10472361 / 66560 * (x - (3 / 2 : ℝ)) + 3291829 / 319488) / ((x + 1) ^ 2 * (13 * x - 10) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd6 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd7 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd8 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd9 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_M1_tf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (10 / 13) (3 / 4) + 5 * lrb3 x (10 / 13) (3 / 4)) < (-21 / 800 : ℝ) := by
  have hid := lro_B_M1_tf_id h0 h1
  have hn := lro_B_M1_tf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (13 * x - 10) ^ 2 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 2))
  have : 0 < (-21 / 800 : ℝ) - (2 * lrb2 x (10 / 13) (3 / 4) + 5 * lrb3 x (10 / 13) (3 / 4)) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T65_tf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -2231328125 / 6912 * z ^ 9 - 111294984750625 / 11943936 * z ^ 8 - 1276812421850875 / 11943936 * z ^ 7 - 74134793435270191 / 119439360 * z ^ 6 - 2289554860065789679 / 1194393600 * z ^ 5 - 117612911620066571929 / 38817792000 * z ^ 4 - 624370863359479763561 / 310542336000 * z ^ 3 + 2580113712562108484531 / 15527116800000 * z ^ 2 + 6120944603978410445687 / 6210846720000 * z + 150738399167629478149 / 382205952000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem lro_B_T65_tf_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) = (-2231328125 / 6912 * (x - (3 / 2 : ℝ)) ^ 9 - 111294984750625 / 11943936 * (x - (3 / 2 : ℝ)) ^ 8 - 1276812421850875 / 11943936 * (x - (3 / 2 : ℝ)) ^ 7 - 74134793435270191 / 119439360 * (x - (3 / 2 : ℝ)) ^ 6 - 2289554860065789679 / 1194393600 * (x - (3 / 2 : ℝ)) ^ 5 - 117612911620066571929 / 38817792000 * (x - (3 / 2 : ℝ)) ^ 4 - 624370863359479763561 / 310542336000 * (x - (3 / 2 : ℝ)) ^ 3 + 2580113712562108484531 / 15527116800000 * (x - (3 / 2 : ℝ)) ^ 2 + 6120944603978410445687 / 6210846720000 * (x - (3 / 2 : ℝ)) + 150738399167629478149 / 382205952000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T65_tf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) := by
  have hid := lro_B_T65_tf_id h0 h1
  have hn := lro_B_T65_tf_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T13_tf_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -29949692000 * z ^ 12 - 1459697881300 / 3 * z ^ 11 - 2391361389685293 / 650 * z ^ 10 - 37561908882450669701 / 2106000 * z ^ 9 - 377634913304422707887 / 5923125 * z ^ 8 - 76767568355319151870783 / 437400000 * z ^ 7 - 950727627520215419338763 / 2624400000 * z ^ 6 - 33137165575251389353011739 / 62985600000 * z ^ 5 - 5748671509329054200959051 / 11809800000 * z ^ 4 - 15867507633386513266734767 / 70858800000 * z ^ 3 + 4397597420466447100082179 / 212576400000 * z ^ 2 + 22383620895194775932455493 / 318864600000 * z + 2643623526657918623359411 / 119574225000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_B_T13_tf_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (3 / 4) - (0 : ℝ) = (-29949692000 * (x - (5 / 3 : ℝ)) ^ 12 - 1459697881300 / 3 * (x - (5 / 3 : ℝ)) ^ 11 - 2391361389685293 / 650 * (x - (5 / 3 : ℝ)) ^ 10 - 37561908882450669701 / 2106000 * (x - (5 / 3 : ℝ)) ^ 9 - 377634913304422707887 / 5923125 * (x - (5 / 3 : ℝ)) ^ 8 - 76767568355319151870783 / 437400000 * (x - (5 / 3 : ℝ)) ^ 7 - 950727627520215419338763 / 2624400000 * (x - (5 / 3 : ℝ)) ^ 6 - 33137165575251389353011739 / 62985600000 * (x - (5 / 3 : ℝ)) ^ 5 - 5748671509329054200959051 / 11809800000 * (x - (5 / 3 : ℝ)) ^ 4 - 15867507633386513266734767 / 70858800000 * (x - (5 / 3 : ℝ)) ^ 3 + 4397597420466447100082179 / 212576400000 * (x - (5 / 3 : ℝ)) ^ 2 + 22383620895194775932455493 / 318864600000 * (x - (5 / 3 : ℝ)) + 2643623526657918623359411 / 119574225000) /
      ((307 * x - 61) * (x + 1) ^ 2 * (1160 * x + 151) ^ 3 * (2 * x + 1) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((6 * x + 3) / 13) + (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) = (307 * x - 61) / (169 : ℝ) by ring,
    show 2 * ((307 * x - 61) / (169 : ℝ)) + 7 * ((6 * x + 3) / 13) = (1160 * x + 151) / (169 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 307 * x - 61 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 1160 * x + 151 ≠ 0 := by nlinarith
  have hd3 : 2 * x + 1 ≠ 0 := by nlinarith
  have hp0 : 307 * x - 61 ≠ 0 := by nlinarith
  have hq0 : 1160 * x + 151 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 307 * x - 61 = p at hp0 ⊢
  generalize hq : 1160 * x + 151 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T13_tf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have hid := lro_B_T13_tf_id h0 h1
  have hn := lro_B_T13_tf_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 307 * x - 61 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 1160 * x + 151 := by nlinarith
  have hP3 : 0 < 2 * x + 1 := by nlinarith
  have hD : 0 < (307 * x - 61) * (x + 1) ^ 2 * (1160 * x + 151) ^ 3 * (2 * x + 1) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_Q_tv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -388869 / 200 * z ^ 6 - 14155271 / 1920 * z ^ 5 + 35447607 / 6400 * z ^ 4 + 674848373 / 19200 * z ^ 3 + 368892567 / 12800 * z ^ 2 + 765004441 / 153600 * z + 92497301 / 61440 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5)]

theorem lro_B_Q_tv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) - lrQ1 x (10 / 13) (19 / 25) = (-388869 / 200 * (x - (3 / 2 : ℝ)) ^ 6 - 14155271 / 1920 * (x - (3 / 2 : ℝ)) ^ 5 + 35447607 / 6400 * (x - (3 / 2 : ℝ)) ^ 4 + 674848373 / 19200 * (x - (3 / 2 : ℝ)) ^ 3 + 368892567 / 12800 * (x - (3 / 2 : ℝ)) ^ 2 + 765004441 / 153600 * (x - (3 / 2 : ℝ)) + 92497301 / 61440) / ((x + 1) * (13 * x - 10) ^ 4) := by
  simp only [lrQ1, lrq0, lrq1, lrq2, lrq3, lrW0, lrW1, lrW2, lrW3, lrW4, lrd0, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd6 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd7 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd8 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd9 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_Q_tv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    lrQ1 x (10 / 13) (19 / 25) < (0 : ℝ) := by
  have hid := lro_B_Q_tv_id h0 h1
  have hn := lro_B_Q_tv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x + 1) * (13 * x - 10) ^ 4 := (mul_pos hP0 (pow_pos hP1 4))
  have : 0 < (0 : ℝ) - lrQ1 x (10 / 13) (19 / 25) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_M1_tv_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 3211 / 120 * z ^ 7 + 2340481 / 10000 * z ^ 6 + 23832089 / 30000 * z ^ 5 + 174331873 / 130000 * z ^ 4 + 758955539 / 624000 * z ^ 3 + 152534671 / 249600 * z ^ 2 + 1394767 / 8320 * z + 82137 / 6656 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_M1_tv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-21 / 800 : ℝ) - (2 * lrb2 x (10 / 13) (19 / 25) + 5 * lrb3 x (10 / 13) (19 / 25)) = (3211 / 120 * (x - (3 / 2 : ℝ)) ^ 7 + 2340481 / 10000 * (x - (3 / 2 : ℝ)) ^ 6 + 23832089 / 30000 * (x - (3 / 2 : ℝ)) ^ 5 + 174331873 / 130000 * (x - (3 / 2 : ℝ)) ^ 4 + 758955539 / 624000 * (x - (3 / 2 : ℝ)) ^ 3 + 152534671 / 249600 * (x - (3 / 2 : ℝ)) ^ 2 + 1394767 / 8320 * (x - (3 / 2 : ℝ)) + 82137 / 6656) / ((x + 1) ^ 2 * (13 * x - 10) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd2 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 1 ≠ 0 := by nlinarith
  have hd5 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd6 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd7 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd8 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd9 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_B_M1_tv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (10 / 13) (19 / 25) + 5 * lrb3 x (10 / 13) (19 / 25)) < (-21 / 800 : ℝ) := by
  have hid := lro_B_M1_tv_id h0 h1
  have hn := lro_B_M1_tv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (13 * x - 10) ^ 2 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 2))
  have : 0 < (-21 / 800 : ℝ) - (2 * lrb2 x (10 / 13) (19 / 25) + 5 * lrb3 x (10 / 13) (19 / 25)) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T65_tv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1695809375 / 5184 * z ^ 9 - 196229016191 / 20736 * z ^ 8 - 33892311188281 / 311040 * z ^ 7 - 11885701406888803 / 18662400 * z ^ 6 - 1488203715960593 / 746496 * z ^ 5 - 974604802706378681 / 299520000 * z ^ 4 - 11638366344514651741 / 4852224000 * z ^ 3 - 83594161042362317417 / 485222400000 * z ^ 2 + 279380675554614067 / 299520000 * z + 57147715913092721 / 119808000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8)]

theorem lro_B_T65_tv_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) = (-1695809375 / 5184 * (x - (3 / 2 : ℝ)) ^ 9 - 196229016191 / 20736 * (x - (3 / 2 : ℝ)) ^ 8 - 33892311188281 / 311040 * (x - (3 / 2 : ℝ)) ^ 7 - 11885701406888803 / 18662400 * (x - (3 / 2 : ℝ)) ^ 6 - 1488203715960593 / 746496 * (x - (3 / 2 : ℝ)) ^ 5 - 974604802706378681 / 299520000 * (x - (3 / 2 : ℝ)) ^ 4 - 11638366344514651741 / 4852224000 * (x - (3 / 2 : ℝ)) ^ 3 - 83594161042362317417 / 485222400000 * (x - (3 / 2 : ℝ)) ^ 2 + 279380675554614067 / 299520000 * (x - (3 / 2 : ℝ)) + 57147715913092721 / 119808000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T65_tv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) := by
  have hid := lro_B_T65_tv_id h0 h1
  have hn := lro_B_T65_tv_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T13_tv_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 3 : ℝ)) :
    (0 : ℝ) < -138008180736 / 5 * z ^ 12 - 10924523581184 / 25 * z ^ 11 - 426633888986490976 / 131625 * z ^ 10 - 31169138341680727228 / 1974375 * z ^ 9 - 12898839221666343332 / 219375 * z ^ 8 - 394879646593924387619 / 2278125 * z ^ 7 - 10576046595078825513913 / 27337500 * z ^ 6 - 3714399621237661344833 / 6075000 * z ^ 5 - 1246506063010012064500721 / 1968300000 * z ^ 4 - 551587127637507632334859 / 1476225000 * z ^ 3 - 546402343741377933257903 / 7873200000 * z ^ 2 + 13422684283385176492456933 / 318864600000 * z + 2281657762618844913234451 / 119574225000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11)]

theorem lro_B_T13_tv_id {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (19 / 25) - (0 : ℝ) = (-138008180736 / 5 * (x - (5 / 3 : ℝ)) ^ 12 - 10924523581184 / 25 * (x - (5 / 3 : ℝ)) ^ 11 - 426633888986490976 / 131625 * (x - (5 / 3 : ℝ)) ^ 10 - 31169138341680727228 / 1974375 * (x - (5 / 3 : ℝ)) ^ 9 - 12898839221666343332 / 219375 * (x - (5 / 3 : ℝ)) ^ 8 - 394879646593924387619 / 2278125 * (x - (5 / 3 : ℝ)) ^ 7 - 10576046595078825513913 / 27337500 * (x - (5 / 3 : ℝ)) ^ 6 - 3714399621237661344833 / 6075000 * (x - (5 / 3 : ℝ)) ^ 5 - 1246506063010012064500721 / 1968300000 * (x - (5 / 3 : ℝ)) ^ 4 - 551587127637507632334859 / 1476225000 * (x - (5 / 3 : ℝ)) ^ 3 - 546402343741377933257903 / 7873200000 * (x - (5 / 3 : ℝ)) ^ 2 + 13422684283385176492456933 / 318864600000 * (x - (5 / 3 : ℝ)) + 2281657762618844913234451 / 119574225000) /
      ((307 * x - 61) * (x + 1) ^ 2 * (1160 * x + 151) ^ 3 * (2 * x + 1) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show ((6 * x + 3) / 13) + (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) = (307 * x - 61) / (169 : ℝ) by ring,
    show 2 * ((307 * x - 61) / (169 : ℝ)) + 7 * ((6 * x + 3) / 13) = (1160 * x + 151) / (169 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 307 * x - 61 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 1160 * x + 151 ≠ 0 := by nlinarith
  have hd3 : 2 * x + 1 ≠ 0 := by nlinarith
  have hp0 : 307 * x - 61 ≠ 0 := by nlinarith
  have hq0 : 1160 * x + 151 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 307 * x - 61 = p at hp0 ⊢
  generalize hq : 1160 * x + 151 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T13_tv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have hid := lro_B_T13_tv_id h0 h1
  have hn := lro_B_T13_tv_num (z := x - (5 / 3 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 307 * x - 61 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 1160 * x + 151 := by nlinarith
  have hP3 : 0 < 2 * x + 1 := by nlinarith
  have hD : 0 < (307 * x - 61) * (x + 1) ^ 2 * (1160 * x + 151) ^ 3 * (2 * x + 1) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T1_f_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) < -1 / 4 * z ^ 8 - 6769 / 1152 * z ^ 7 - 15497 / 288 * z ^ 6 - 1738549711 / 7200000 * z ^ 5 - 3934512103 / 7200000 * z ^ 4 - 33908912149 / 57600000 * z ^ 3 - 7450455389 / 28800000 * z ^ 2 + 56527253 / 2880000 * z + 10344481 / 288000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_T1_f_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (5 / 3 : ℝ)) :
    lroF1 x (1) (x) (3 / 4) - (0 : ℝ) = (-1 / 4 * (x - (3 / 2 : ℝ)) ^ 8 - 6769 / 1152 * (x - (3 / 2 : ℝ)) ^ 7 - 15497 / 288 * (x - (3 / 2 : ℝ)) ^ 6 - 1738549711 / 7200000 * (x - (3 / 2 : ℝ)) ^ 5 - 3934512103 / 7200000 * (x - (3 / 2 : ℝ)) ^ 4 - 33908912149 / 57600000 * (x - (3 / 2 : ℝ)) ^ 3 - 7450455389 / 28800000 * (x - (3 / 2 : ℝ)) ^ 2 + 56527253 / 2880000 * (x - (3 / 2 : ℝ)) + 10344481 / 288000) /
      ((x + 1) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (1) + (x) = (x + 1) / (1 : ℝ) by ring,
    show 2 * ((x + 1) / (1 : ℝ)) + 7 * (1) = (2 * x + 9) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : 2 * x + 9 ≠ 0 := by nlinarith
  have hp0 : x + 1 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 9 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : x + 1 = p at hp0 ⊢
  generalize hq : 2 * x + 9 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T1_f {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (3 / 4) := by
  have hid := lro_B_T1_f_id h0 h1
  have hn := lro_B_T1_f_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x + 9 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (2 * x + 9) ^ 3 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 3))
  have : 0 < lroF1 x (1) (x) (3 / 4) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_B_T1_v_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) < -19 / 75 * z ^ 8 - 11186 / 1875 * z ^ 7 - 411157 / 7500 * z ^ 6 - 6964826 / 28125 * z ^ 5 - 255928673 / 450000 * z ^ 4 - 572978441 / 900000 * z ^ 3 - 141958301 / 450000 * z ^ 2 - 41606 / 5625 * z + 344633 / 9000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lro_B_T1_v_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (5 / 3 : ℝ)) :
    lroF1 x (1) (x) (19 / 25) - (0 : ℝ) = (-19 / 75 * (x - (3 / 2 : ℝ)) ^ 8 - 11186 / 1875 * (x - (3 / 2 : ℝ)) ^ 7 - 411157 / 7500 * (x - (3 / 2 : ℝ)) ^ 6 - 6964826 / 28125 * (x - (3 / 2 : ℝ)) ^ 5 - 255928673 / 450000 * (x - (3 / 2 : ℝ)) ^ 4 - 572978441 / 900000 * (x - (3 / 2 : ℝ)) ^ 3 - 141958301 / 450000 * (x - (3 / 2 : ℝ)) ^ 2 - 41606 / 5625 * (x - (3 / 2 : ℝ)) + 344633 / 9000) /
      ((x + 1) ^ 2 * (2 * x + 9) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (1) + (x) = (x + 1) / (1 : ℝ) by ring,
    show 2 * ((x + 1) / (1 : ℝ)) + 7 * (1) = (2 * x + 9) / (1 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : x + 1 ≠ 0 := by nlinarith
  have hd1 : 2 * x + 9 ≠ 0 := by nlinarith
  have hp0 : x + 1 ≠ 0 := by nlinarith
  have hq0 : 2 * x + 9 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : x + 1 = p at hp0 ⊢
  generalize hq : 2 * x + 9 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_B_T1_v {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (19 / 25) := by
  have hid := lro_B_T1_v_id h0 h1
  have hn := lro_B_T1_v_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x + 1 := by nlinarith
  have hP1 : 0 < 2 * x + 9 := by nlinarith
  have hD : 0 < (x + 1) ^ 2 * (2 * x + 9) ^ 3 := (mul_pos (pow_pos hP0 2) (pow_pos hP1 3))
  have : 0 < lroF1 x (1) (x) (19 / 25) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith

/-- `w₀ > 6/7` on the small shapes. -/
theorem lro_B_w0 {x a u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hu : u ≤ 19 / 25) : 6 / 7 < lrow0 x a u := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have h1 := lro_w0_diff' (u := u) (u' := 19 / 25) hx0 ha0
  have hid : lrow0 x a (19 / 25) - 6 / 7 = lrPwN (6 / 5 - a) (x - 3 / 2) / (a ^ 4 * (x + 1)) := by
    simp only [lrow0, lroM, lroJ, lroK, ssE0, lroD0, lrPwN]
    field_simp
    ring
  have hP := lrPwN_pos (c := 6 / 5 - a) (z := x - 3 / 2) (by linarith) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨hD0, hD1⟩ := lro_KS_D0 ha1 (by linarith : a ≤ x)
  have h2 : 0 ≤ (19 / 25 - u) * lroD0 x a * (lroK a * (1 + x) - lroD0 x a) / (49 * a ^ 4) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hD0.le) (by linarith)) (by positivity)
  have h3 : 0 < lrPwN (6 / 5 - a) (x - 3 / 2) / (a ^ 4 * (x + 1)) := div_pos hP (by positivity)
  linarith

/-- **Reciprocal-shape concavity of `F₁` on the small shapes**. -/
theorem lro_B_recip {x a aS C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (haS1 : 1 ≤ aS) (haS : aS ≤ a)
    (ha2 : a ≤ 6 / 5) (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 10 / 13) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25)
    (hQ : lrQ1 x C u < 0) (hM : 2 * lrb2 x C u + 5 * lrb3 x C u < -21 / 800) :
    min (lroF1 x aS (x + C * (aS - 1)) u) (lroF1 x (6 / 5) (x + C * (6 / 5 - 1)) u) ≤
      lroF1 x a (x + C * (a - 1)) u := by
  have hx0 : 0 < x := by linarith
  have hb3 := lro_b3_nonpos hx hx2 hC1 (by linarith) hu1
  have hb4 := lrg4_nonpos (u := u) hx0
  have hZ : ∀ a' : ℝ, 1 ≤ a' → a' ≤ 6 / 5 → 0 < 1 + C + (x - C) * (1 / a') := by
    intro a' h1 h2
    have : 0 < (x - C) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  have hrep : ∀ a' : ℝ, 1 ≤ a' → a' ≤ 6 / 5 → lroF1 x a' (x + C * (a' - 1)) u =
      lrG (lrb0 x C u) (lrb1 x C u) (lrb2 x C u) (lrb3 x C u) (lrb4 x u) (lrQ1 x C u)
        (1 + C) (x - C) (1 / a') :=
    fun a' h1 h2 => lro_F1_rG hx0 (by linarith) rfl (by linarith) (hZ a' h1 h2)
  rw [hrep a (by linarith) ha2, hrep aS haS1 (by linarith), hrep (6 / 5) (by norm_num) le_rfl]
  rw [min_comm]
  apply lrG_min (one_div_le_one_div_of_le (by linarith) ha2)
    (one_div_le_one_div_of_le (by linarith) haS)
  · intro s hs
    have h1 : 1 / (6 / 5) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by linarith)]; exact haS1)
    norm_num at h1
    constructor
    · nlinarith
    · nlinarith
  · intro s hs
    have h1 : 1 / (6 / 5) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by linarith)]; exact haS1)
    norm_num at h1
    set Z := 1 + C + (x - C) * s with hZdef
    have hZ0 : 0 < Z := by nlinarith
    have hZe : 11 * (x - C) ≤ 6 * Z := by nlinarith
    have t1 : 12 * lrb4 x u * s ^ 2 ≤ 0 := by nlinarith [sq_nonneg s]
    have t2 : 6 * lrb3 x C u * s ≤ 5 * lrb3 x C u := by nlinarith
    have t3 : 2 * lrQ1 x C u * (x - C) ^ 2 / Z ^ 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - C)]) (by positivity)
    have t4 : 7 / 96 * (x - C) ^ 2 / Z ^ 2 ≤ 21 / 800 := by
      rw [div_le_iff₀ (by positivity)]
      have : (x - C) ^ 2 ≤ 36 / 121 * Z ^ 2 := by nlinarith
      nlinarith
    nlinarith

/-- **Branch B, `F₁ > 0`.** -/
theorem lro_B_F1 {x a b C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 10 / 13)
    (hb : b = x + C * (a - 1)) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) : 0 < lroF1 x a b u := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  -- the lower shape below the cap
  obtain ⟨aS, haS1, haS, hlow⟩ : ∃ aS, 1 ≤ aS ∧ aS ≤ a ∧ ∀ C' u', (C' = 1 / 2 ∨ C' = 10 / 13) →
      (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < lroF1 x aS (x + C' * (aS - 1)) u' := by
    rcases le_total x (5 / 3) with h53 | h53
    · refine ⟨1, le_rfl, ha1, fun C' u' _ hu' => ?_⟩
      rw [show x + C' * (1 - 1) = x by ring]
      rcases hu' with rfl | rfl
      · exact lro_B_T1_f hx h53
      · exact lro_B_T1_v hx h53
    · refine ⟨(6 * x + 3) / 13, by linarith, ?_, fun C' u' hC' hu' => ?_⟩
      · have h1 : ((6 * x + 3) / 13) ^ 2 ≤ a ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h53) (sub_nonneg.2 hx2)]
        nlinarith [sq_nonneg (a - (6 * x + 3) / 13)]
      · rcases hC' with rfl | rfl <;> rcases hu' with rfl | rfl
        · exact lro_B_T13_hf h53 hx2
        · exact lro_B_T13_hv h53 hx2
        · exact lro_B_T13_tf h53 hx2
        · exact lro_B_T13_tv h53 hx2
  have hshape : ∀ C' u', (C' = 1 / 2 ∨ C' = 10 / 13) → (u' = 3 / 4 ∨ u' = 19 / 25) →
      0 < lroF1 x a (x + C' * (a - 1)) u' := by
    intro C' u' hC' hu'
    have hu0' : 3 / 4 ≤ u' := by rcases hu' with rfl | rfl <;> norm_num
    have hu1' : u' ≤ 19 / 25 := by rcases hu' with rfl | rfl <;> norm_num
    have hC0' : 1 / 2 ≤ C' := by rcases hC' with rfl | rfl <;> norm_num
    have hC1' : C' ≤ 10 / 13 := by rcases hC' with rfl | rfl <;> norm_num
    have key : lrQ1 x C' u' < 0 ∧ 2 * lrb2 x C' u' + 5 * lrb3 x C' u' < -21 / 800 ∧
        0 < lroF1 x (6 / 5) (x + C' * (6 / 5 - 1)) u' := by
      rcases hC' with rfl | rfl <;> rcases hu' with rfl | rfl
      · exact ⟨lro_B_Q_hf hx hx2, lro_B_M1_hf hx hx2, lro_B_T65_hf hx hx2⟩
      · exact ⟨lro_B_Q_hv hx hx2, lro_B_M1_hv hx hx2, lro_B_T65_hv hx hx2⟩
      · exact ⟨lro_B_Q_tf hx hx2, lro_B_M1_tf hx hx2, lro_B_T65_tf hx hx2⟩
      · exact ⟨lro_B_Q_tv hx hx2, lro_B_M1_tv hx hx2, lro_B_T65_tv hx hx2⟩
    obtain ⟨hQ, hM, t2⟩ := key
    have := lro_B_recip hx hx2 haS1 haS ha2 hC0' hC1' hu0' hu1' hQ hM
    exact lt_of_lt_of_le (lt_min (hlow C' u' hC' hu') t2) this
  have hbeta : ∀ u', (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < lroF1 x a b u' := by
    intro u' hu'
    have hu1' : u' ≤ 19 / 25 := by rcases hu' with rfl | rfl <;> norm_num
    have hw0 := lro_B_w0 (u := u') hx hx2 ha1 ha2 hu1'
    have hA : 0 ≤ a - 1 := by linarith
    have hm := lro_F1_bmin (x := x) (a := a) (b1 := x + 1 / 2 * (a - 1)) (b := b)
      (b2 := x + 10 / 13 * (a - 1)) (u := u') hx0 ha0 (by nlinarith)
      (by rw [hb]; nlinarith) (by rw [hb]; nlinarith) (by nlinarith) (by nlinarith)
    exact lt_of_lt_of_le (lt_min (hshape _ _ (Or.inl rfl) hu') (hshape _ _ (Or.inr rfl) hu')) hm
  have hm := lro_F1_umin (x := x) (a := a) (b := b) hu0 hu1 ha0.ne'
  exact lt_of_lt_of_le (lt_min (hbeta _ (Or.inl rfl)) (hbeta _ (Or.inr rfl))) hm

end SmoothedOctagon
