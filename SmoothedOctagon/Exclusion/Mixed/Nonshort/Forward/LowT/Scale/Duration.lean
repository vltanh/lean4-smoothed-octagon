module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Polynomial
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# Curvature in the duration increment

The third duration derivative is concave. Its values at zero and at `9/32`
are nonnegative. The latter increases with the order gap and is concave in
the scale, so its sign reduces to two corners of the scale and gap rectangle.
-/

@[expose] public section

namespace SmoothedOctagon.LowTScale

private noncomputable def curvJ (h : ℝ) : Polynomial ℝ :=
  curvatureEnd (Polynomial.C h) Polynomial.X

private noncomputable def curvH (j : ℝ) : Polynomial ℝ :=
  curvatureEnd Polynomial.X (Polynomial.C j)

private theorem curvJ_eval (h j : ℝ) : (curvJ h).eval j = curvatureEnd h j := by
  simp [curvJ, curvatureEnd, coefficient, row3, row4, row5, row6]

private theorem curvH_eval (h j : ℝ) : (curvH j).eval h = curvatureEnd h j := by
  simp [curvH, curvatureEnd, coefficient, row3, row4, row5, row6]

theorem coefficient3_nonneg {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) : 0 ≤ coefficient 3 h j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = (1 / 30) + v := ⟨j - (1 / 30), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 13 / 60 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (13 / 60 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  norm_num [coefficient, row3]
  ring_nf
  linarith only [hi 9 0, hi 8 1, hi 8 0, hi 7 2, hi 7 1, hi 7 0, hi 6 3, hi 6 2, hi 6 1, hi 6 0,
    hi 5 4, hi 5 3, hi 5 2, hi 5 1, hi 5 0, hi 4 5, hi 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 6,
    hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 7, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2,
    hi 2 1, hi 2 0, hi 1 7, hi 1 6, hi 1 5, hi 1 4, lo 1 3, lo 1 2, lo 1 1, hi 1 0, lo 0 8, lo 0 7,
    lo 0 6, lo 0 5, lo 0 4, lo 0 3, lo 0 2, lo 0 1]

theorem coefficient5_nonpos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : coefficient 5 h j ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = (0) + v := ⟨j - (0), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 1 / 4 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (1 / 4 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  norm_num [coefficient, row5]
  ring_nf
  linarith only [lo 9 0, lo 8 1, lo 8 0, lo 7 2, lo 7 1, lo 7 0, lo 6 3, lo 6 2, lo 6 1, lo 6 0,
    lo 5 4, lo 5 3, lo 5 2, lo 5 1, lo 5 0, lo 4 5, lo 4 4, lo 4 3, lo 4 2, lo 4 1, lo 4 0, lo 3 6,
    lo 3 5, lo 3 4, lo 3 3, lo 3 2, lo 3 1, lo 3 0, lo 2 7, lo 2 6, lo 2 5, lo 2 4, lo 2 3, lo 2 2,
    lo 2 1, lo 2 0, lo 1 7, lo 1 6, lo 1 5, lo 1 4, hi 1 3, hi 1 2, hi 1 1, lo 1 0, hi 0 8, hi 0 7,
    hi 0 6, hi 0 5, hi 0 4, hi 0 3, hi 0 2, lo 0 1]

theorem coefficient6_nonpos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : coefficient 6 h j ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = (0) + v := ⟨j - (0), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 1 / 4 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (1 / 4 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  norm_num [coefficient, row6]
  ring_nf
  linarith only [lo 7 1, lo 7 0, lo 6 2, lo 6 1, lo 6 0, lo 5 3, lo 5 2, lo 5 1, lo 5 0, lo 4 4,
    lo 4 3, lo 4 2, lo 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 6, hi 2 5,
    hi 2 4, hi 2 3, hi 2 2, hi 2 1, hi 2 0, hi 1 7, hi 1 6, hi 1 5, hi 1 4, hi 1 3, hi 1 2, hi 1 1,
    lo 1 0, hi 0 8, hi 0 7, hi 0 6, lo 0 5, lo 0 4, lo 0 3, lo 0 2, lo 0 1]

set_option maxRecDepth 4096 in
private theorem curvature_increases {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : 0 ≤ (curvJ h).derivative.eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = (0) + v := ⟨j - (0), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 1 / 4 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (1 / 4 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  conv in (curvJ _) =>
    simp only [curvJ, curvatureEnd]
    norm_num only [coefficient]
    simp only [row3, row4, row5, row6]
    norm_num
    ring_nf
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_ofNat,
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num
  ring_nf
  linarith only [hi 8 0, hi 7 1, hi 7 0, hi 6 2, hi 6 1, hi 6 0, hi 5 3, hi 5 2, hi 5 1, hi 5 0,
    hi 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 6,
    hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, hi 2 0, hi 1 6, hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1,
    lo 1 0, hi 0 7, hi 0 6, lo 0 5, lo 0 4, lo 0 3, lo 0 2, lo 0 1]

set_option maxRecDepth 4096 in
private theorem curvature_concave {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : (curvH j).derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = (0) + v := ⟨j - (0), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 1 / 4 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (1 / 4 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  conv in (curvH _) =>
    simp only [curvH, curvatureEnd]
    norm_num only [coefficient]
    simp only [row3, row4, row5, row6]
    norm_num
    ring_nf
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_ofNat,
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num
  ring_nf
  linarith only [lo 7 0, lo 6 1, lo 6 0, lo 5 2, lo 5 1, lo 5 0, lo 4 3, lo 4 2, lo 4 1, lo 4 0,
    lo 3 4, lo 3 3, lo 3 2, lo 3 1, lo 3 0, lo 2 5, lo 2 4, lo 2 3, lo 2 2, lo 2 1, lo 2 0, lo 1 6,
    lo 1 5, lo 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, lo 0 7, lo 0 6, lo 0 5, lo 0 4, lo 0 3, lo 0 2,
    lo 0 1]

theorem curvatureEnd_pos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) : 0 < curvatureEnd h j := by
  have hf := UnitShape.polynomial_floor (p := curvH (1 / 30)) (m := 1) h0 h1
    (fun s hs0 hs1 => curvature_concave hs0 hs1 (by norm_num) (by norm_num))
    (by norm_num [curvH, curvatureEnd, coefficient, row3, row4, row5, row6])
    (by norm_num [curvH, curvatureEnd, coefficient, row3, row4, row5, row6])
  have hm := UnitShape.polynomial_mono (p := curvJ h) hj0
    (fun s hs0 hs1 => curvature_increases h0 h1 (by linarith only [hs0]) (hs1.trans hj1))
  rw [curvH_eval] at hf
  rw [curvJ_eval, curvJ_eval] at hm
  linarith only [hf, hm]

/-- Nonnegative third duration derivative on the whole duration rectangle. -/
theorem duration_third_nonneg {h j y : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) (hy0 : 0 ≤ y) (hy1 : y ≤ 9 / 32) :
    0 ≤ (durationPolynomial h j).derivative.derivative.derivative.eval y := by
  have h5 := coefficient5_nonpos h0 h1 (by linarith only [hj0]) hj1
  have h6 := coefficient6_nonpos h0 h1 (by linarith only [hj0]) hj1
  apply UnitShape.polynomial_floor (p := (durationPolynomial h j).derivative.derivative.derivative)
    (m := 0) hy0 hy1
  · intro s hs0 _
    have h6s := mul_nonpos_of_nonpos_of_nonneg h6 hs0
    norm_num [durationPolynomial, Fin.sum_univ_succ, Polynomial.derivative_mul,
      Polynomial.derivative_pow]
    nlinarith only [h5, h6s]
  · rw [duration_third]
    have := coefficient3_nonneg h0 h1 hj0 hj1
    norm_num
    linarith only [this]
  · rw [duration_third]
    have := curvatureEnd_pos h0 h1 hj0 hj1
    unfold curvatureEnd at this
    norm_num
    linarith only [this]

end SmoothedOctagon.LowTScale
