module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal

/-!
# Smaller-short window, lower ratio, outer face, small shapes: the test `F₁`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`,
`1/2 ≤ C ≤ 10/13`, `3/4 ≤ u ≤ 19/25`:

* `w₀ > 8/9` by the norm comparison and the two shape/ratio increments
  (`SmallShape/Norm`), so `β ↦ F₁` is concave and `C ∈ {1/2, 10/13}`;
* norm concavity gives `u ∈ {3/4, 19/25}`;
* the reciprocal-shape curvature is at most `5b₃ + 2b₂ + 21/800 < 0` on `r ∈ [5/6, 1]`
  (residue `Q < 0`), so `α` is `6/5` or the lower shape `α_*(x) = 1` (`x ≤ 5/3`),
  `(6x + 3)/13` (`x ≥ 5/3`, below the cap);
* the terminal curves are positive.

The terminal curves use a decreasing derivative numerator and endpoint comparison
(`SmallShape/Terminal`). The residue and curvature signs are proved below.

## Main API

* `lro_B_w0`, `lro_B_recip`, `lro_B_F1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

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


theorem lro_B_T65_hf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_hf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

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


theorem lro_B_T65_hv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_hv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

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


theorem lro_B_T65_tf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 10 / 13) (u := 3 / 4)
    (Or.inr rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_tf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 10 / 13) (u := 3 / 4)
    (Or.inr rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

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


theorem lro_B_T65_tv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 10 / 13) (u := 19 / 25)
    (Or.inr rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_tv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 10 / 13) (u := 19 / 25)
    (Or.inr rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T1_f {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .unit (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .unit) x = 1 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .unit (Or.inl rfl) (by linarith), he] at h
  simpa only [sub_self, mul_zero, add_zero] using (lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h)

theorem lro_B_T1_v {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .unit (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .unit) x = 1 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .unit (Or.inl rfl) (by linarith), he] at h
  simpa only [sub_self, mul_zero, add_zero] using (lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h)

/-- `w₀ > 6/7` on the small shapes. -/
theorem lro_B_w0 {x a u : ℝ} (hx : 3 / 2 ≤ x) (_hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hu : u ≤ 19 / 25) : 6 / 7 < lrow0 x a u := by
  have h := lro_small_shape_w0 hx ha1 ha2 hu
  linarith only [h]

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
