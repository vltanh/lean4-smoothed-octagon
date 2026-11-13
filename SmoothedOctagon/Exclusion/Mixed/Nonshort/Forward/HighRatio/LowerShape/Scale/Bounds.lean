module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.Scale.Polynomial

/-!
# Direct coefficient bounds for the scale slope

Shift to the left endpoints of the scale and gap intervals. Positive
monomials may be discarded, and negative monomials are bounded by their
values at the upper endpoints. All constants are deliberately rounded.
-/

@[expose] public section
namespace SmoothedOctagon.HighRatioScale

theorem slope_h_coefficient0 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (30000) ≤ ((slopeRow0 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow0, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 7 0, lo 6 1, hi 6 0, lo 5 2, hi 5 1, hi 5 0, lo 4 3, hi 4 2, hi 4 1, hi 4 0,
    lo 3 4, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1,
    lo 2 0, hi 1 6, hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 6, hi 0 5,
    lo 0 4, lo 0 3, lo 0 2, lo 0 1]

theorem slope_h_coefficient1 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow1 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow1, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, lo 5 2, hi 5 1, hi 5 0,
    lo 4 4, lo 4 3, hi 4 2, hi 4 1, hi 4 0, lo 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 7, hi 1 6,
    hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, lo 0 4,
    lo 0 3, lo 0 2, lo 0 1]

theorem slope_h_coefficient2 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow2 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow2, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, lo 5 2, hi 5 1, hi 5 0,
    lo 4 4, lo 4 3, hi 4 2, hi 4 1, hi 4 0, lo 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 7, hi 1 6,
    hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, lo 0 4,
    lo 0 3, lo 0 2, lo 0 1]

theorem slope_h_coefficient3 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow3 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow3, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, lo 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, lo 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 7, hi 1 6,
    hi 1 5, hi 1 4, hi 1 3, hi 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, hi 0 4,
    lo 0 3, lo 0 2, lo 0 1]

theorem slope_h_coefficient4 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow4 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow4, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, hi 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, lo 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, hi 2 0, hi 1 7, hi 1 6,
    hi 1 5, hi 1 4, hi 1 3, hi 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, hi 0 4,
    lo 0 3, lo 0 2, lo 0 1]

theorem slope_h_coefficient5 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow5 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow5, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, hi 7 0, lo 6 2, hi 6 1, hi 6 0, lo 5 3, hi 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, hi 2 0, hi 1 6, hi 1 5,
    hi 1 4, hi 1 3, hi 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, hi 0 4, lo 0 3,
    lo 0 2, lo 0 1]

theorem slope_h_coefficient6 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (-5000) ≤ ((slopeRow6 Polynomial.X (Polynomial.C j)).derivative).eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow6, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [hi 7 0, hi 6 1, hi 6 0, hi 5 2, hi 5 1, lo 5 0, hi 4 3, hi 4 2, lo 4 1, lo 4 0,
    hi 3 4, hi 3 3, lo 3 2, lo 3 1, hi 3 0, hi 2 5, hi 2 4, lo 2 3, lo 2 2, hi 2 1,
    hi 2 0, hi 1 6, hi 1 5, lo 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6,
    lo 0 5, lo 0 4, lo 0 3, lo 0 2, lo 0 1]

theorem slope_j_coefficient0 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (10000) ≤ ((slopeRow0 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow0, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 7 0, lo 6 1, hi 6 0, lo 5 2, hi 5 1, hi 5 0, lo 4 3, hi 4 2, hi 4 1, hi 4 0,
    hi 3 4, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 5, hi 2 4, hi 2 3, hi 2 2, lo 2 1,
    lo 2 0, hi 1 5, hi 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, lo 0 5, lo 0 4, lo 0 3,
    lo 0 2, lo 0 1]

theorem slope_j_coefficient1 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow1 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow1, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, lo 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, lo 2 1, lo 2 0, hi 1 6, hi 1 5,
    hi 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, lo 0 6, lo 0 5, lo 0 4, lo 0 3, lo 0 2,
    lo 0 1]

theorem slope_j_coefficient2 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow2 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow2, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, lo 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, lo 2 1, lo 2 0, hi 1 6, hi 1 5,
    hi 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, lo 0 5, lo 0 4, lo 0 3,
    lo 0 2, lo 0 1]

theorem slope_j_coefficient3 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow3 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow3, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, lo 6 1, hi 6 0, lo 5 3, hi 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 6, hi 1 5,
    hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, lo 0 5, lo 0 4, lo 0 3,
    lo 0 2, lo 0 1]

theorem slope_j_coefficient4 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow4 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow4, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, lo 7 0, lo 6 2, hi 6 1, hi 6 0, lo 5 3, hi 5 2, hi 5 1, hi 5 0,
    lo 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 6, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 6, hi 1 5,
    hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, lo 0 4, lo 0 3,
    lo 0 2, lo 0 1]

theorem slope_j_coefficient5 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (0) ≤ ((slopeRow5 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow5, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 8 0, lo 7 1, hi 7 0, lo 6 2, hi 6 1, hi 6 0, lo 5 3, hi 5 2, hi 5 1, hi 5 0,
    hi 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, hi 3 4, hi 3 3, hi 3 2, hi 3 1,
    hi 3 0, hi 2 5, hi 2 4, hi 2 3, hi 2 2, hi 2 1, lo 2 0, hi 1 6, hi 1 5, hi 1 4,
    hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6, hi 0 5, lo 0 4, lo 0 3, lo 0 2,
    lo 0 1]

theorem slope_j_coefficient6 {h j : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 1 / 5) :
    128 * (-30000) ≤ ((slopeRow6 (Polynomial.C h) Polynomial.X).derivative).eval j := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 5 + u := ⟨h - 1 / 5, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 20 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [j0]
  have hv1 : v ≤ 1 / 6 := by linarith only [j1]
  have lo (a b : ℕ) : 0 ≤ u ^ a * v ^ b :=
    mul_nonneg (pow_nonneg hu a) (pow_nonneg hv b)
  have hi (a b : ℕ) : u ^ a * v ^ b ≤ (1 / 20 : ℝ) ^ a * (1 / 6 : ℝ) ^ b :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 a) (pow_le_pow_left₀ hv hv1 b)
      (pow_nonneg hv b) (by positivity)
  norm_num [slopeRow6, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [hi 7 0, hi 6 1, hi 6 0, hi 5 2, hi 5 1, lo 5 0, hi 4 3, hi 4 2, lo 4 1, lo 4 0,
    hi 3 4, hi 3 3, lo 3 2, lo 3 1, hi 3 0, hi 2 5, hi 2 4, lo 2 3, lo 2 2, lo 2 1,
    lo 2 0, hi 1 6, hi 1 5, lo 1 4, lo 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 7, hi 0 6,
    hi 0 5, hi 0 4, hi 0 3, hi 0 2, hi 0 1]

end SmoothedOctagon.HighRatioScale
