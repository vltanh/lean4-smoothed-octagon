module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# Coefficient estimates for boundary concavity

The scale interval has length `1/12`. Direct bounds on its powers control
most coefficients. Four coefficients increase with scale. The remaining
quadratic coefficient is concave and lies below its right tangent.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

theorem boundary_coefficient0_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 0 h ≤ -3180000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 14, lo 13, lo 12, lo 11, lo 10, lo 9, lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2,
    lo 1]

theorem boundary_coefficient1_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 1 h ≤ -3720000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 14, lo 13, lo 12, lo 11, lo 10, lo 9, lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2,
    lo 1]

private theorem coefficient3_increases {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    0 ≤ (boundaryCoefficientPolynomial 3).derivative.eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (boundaryCoefficientPolynomial _) =>
    simp only [boundaryCoefficientPolynomial]
    norm_num only [boundaryCurvatureCoefficient, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [hi 11, hi 10, hi 9, hi 8, hi 7, hi 6, hi 5, hi 4, hi 3, hi 2, hi 1]

theorem boundary_coefficient3_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 3 h ≤ 180000000 := by
  have hm := UnitShape.polynomial_mono (p := boundaryCoefficientPolynomial 3) h1
    (fun s hs0 hs1 => coefficient3_increases (h0.trans hs0) hs1)
  rw [boundary_coefficient_eval, boundary_coefficient_eval] at hm
  have hb : boundaryCurvatureCoefficient 3 (1 / 3 : ℝ) ≤ 180000000 := by
    norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  exact hm.trans hb

private theorem coefficient4_increases {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    0 ≤ (boundaryCoefficientPolynomial 4).derivative.eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (boundaryCoefficientPolynomial _) =>
    simp only [boundaryCoefficientPolynomial]
    norm_num only [boundaryCurvatureCoefficient, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [hi 10, hi 9, hi 8, hi 7, hi 6, hi 5, hi 4, hi 3, hi 2, hi 1]

theorem boundary_coefficient4_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 4 h ≤ -96000000 := by
  have hm := UnitShape.polynomial_mono (p := boundaryCoefficientPolynomial 4) h1
    (fun s hs0 hs1 => coefficient4_increases (h0.trans hs0) hs1)
  rw [boundary_coefficient_eval, boundary_coefficient_eval] at hm
  have hb : boundaryCurvatureCoefficient 4 (1 / 3 : ℝ) ≤ -96000000 := by
    norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  exact hm.trans hb

private theorem coefficient5_increases {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    0 ≤ (boundaryCoefficientPolynomial 5).derivative.eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (boundaryCoefficientPolynomial _) =>
    simp only [boundaryCoefficientPolynomial]
    norm_num only [boundaryCurvatureCoefficient, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 9, lo 8, lo 7, lo 6, lo 5, hi 4, hi 3, hi 2, hi 1]

theorem boundary_coefficient5_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 5 h ≤ -1740000000 := by
  have hm := UnitShape.polynomial_mono (p := boundaryCoefficientPolynomial 5) h1
    (fun s hs0 hs1 => coefficient5_increases (h0.trans hs0) hs1)
  rw [boundary_coefficient_eval, boundary_coefficient_eval] at hm
  have hb : boundaryCurvatureCoefficient 5 (1 / 3 : ℝ) ≤ -1740000000 := by
    norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  exact hm.trans hb

private theorem coefficient6_increases {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    0 ≤ (boundaryCoefficientPolynomial 6).derivative.eval h := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (boundaryCoefficientPolynomial _) =>
    simp only [boundaryCoefficientPolynomial]
    norm_num only [boundaryCurvatureCoefficient, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 6, hi 5, hi 4, hi 3, hi 2, hi 1]

theorem boundary_coefficient6_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 6 h ≤ -5700000000 := by
  have hm := UnitShape.polynomial_mono (p := boundaryCoefficientPolynomial 6) h1
    (fun s hs0 hs1 => coefficient6_increases (h0.trans hs0) hs1)
  rw [boundary_coefficient_eval, boundary_coefficient_eval] at hm
  have hb : boundaryCurvatureCoefficient 6 (1 / 3 : ℝ) ≤ -5700000000 := by
    norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  exact hm.trans hb

theorem boundary_coefficient7_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 7 h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [hi 7, lo 6, lo 5, lo 4, lo 3, lo 2, hi 1]

theorem boundary_coefficient8_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 8 h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [hi 7, lo 6, lo 5, lo 4, lo 3, lo 2, hi 1]

theorem boundary_coefficient9_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 9 h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 6, lo 5, lo 4, lo 3, hi 2, hi 1]

theorem boundary_coefficient10_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 10 h ≤ -1080000000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 5, lo 4, lo 3, hi 2, hi 1]

theorem boundary_coefficient11_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 11 h ≤ 2106000000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 4, lo 3, hi 2, hi 1]

theorem boundary_coefficient12_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 12 h ≤ 1626000000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 3, hi 2, hi 1]

theorem boundary_coefficient13_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 13 h ≤ 474000000 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]
  ring_nf
  linarith only [lo 2, hi 1]

theorem boundary_coefficient14_ceiling (h : ℝ) :
    boundaryCurvatureCoefficient 14 h ≤ 48000000 := by
  norm_num [boundaryCurvatureCoefficient, boundaryCoefficients]

private theorem coefficient2_concave {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    (boundaryCoefficientPolynomial 2).derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (boundaryCoefficientPolynomial _) =>
    simp only [boundaryCoefficientPolynomial]
    norm_num only [boundaryCurvatureCoefficient, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 11, lo 10, lo 9, lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

theorem boundary_coefficient2_ceiling {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    boundaryCurvatureCoefficient 2 h ≤ 60000000 := by
  let p := boundaryCoefficientPolynomial 2
  have hd {s : ℝ} (hs0 : 1 / 4 ≤ s) (hs1 : s ≤ 1 / 3) :
      p.derivative.eval (1 / 3) ≤ p.derivative.eval s :=
    poly_anti (fun v => p.derivative.hasDerivAt v)
      (fun v hv0 hv1 => coefficient2_concave hv0 hv1) hs0 hs1 le_rfl
  have hm := poly_mono
    (fun s => ((p.hasDerivAt s).sub ((hasDerivAt_id s).mul_const
      (p.derivative.eval (1 / 3)))).congr_deriv (by simp))
    (a := 1 / 4) (b := 1 / 3)
    (fun s hs0 hs1 => sub_nonneg.mpr (hd hs0 hs1)) h0 h1 le_rfl
  change p.eval h - h * p.derivative.eval (1 / 3) ≤
    p.eval (1 / 3) - (1 / 3) * p.derivative.eval (1 / 3) at hm
  have hb0 : p.eval (1 / 3) ≤ 54000000 := by
    norm_num [p, boundaryCoefficientPolynomial, boundaryCurvatureCoefficient, boundaryCoefficients]
  have hb1 : -18000000 ≤ p.derivative.eval (1 / 3) := by
    norm_num [p, boundaryCoefficientPolynomial, boundaryCurvatureCoefficient, boundaryCoefficients,
      Polynomial.derivative_mul, Polynomial.derivative_pow]
  have ht := mul_le_mul_of_nonpos_left hb1 (sub_nonpos.mpr h1)
  rw [← boundary_coefficient_eval]
  change p.eval h ≤ 60000000
  nlinarith only [hm, hb0, ht, h0]

end SmoothedOctagon.LowTScale
