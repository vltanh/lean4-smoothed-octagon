module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Analysis

/-!
# The two gap endpoints of the maximum-duration value

On the outer gap, the expansion at scale `1/4` has positive coefficients.
At gap `1/30`, the scale derivative is concave and starts nonnegative.
The minimum therefore lies at one of the two scale endpoints.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

private noncomputable def basePolynomial : Polynomial ℝ :=
  boundaryHorner Polynomial.X (Polynomial.C (1 / 30))

private theorem base_eval (h : ℝ) : (basePolynomial).eval h = boundary h (1 / 30) := by
  rw [← boundaryHorner_eq]
  simpa [basePolynomial] using
    boundaryHorner_map (Polynomial.evalRingHom h) Polynomial.X (Polynomial.C (1 / 30))

private theorem base_third_nonpos {h : ℝ} (h0 : 1 / 4 ≤ h) :
    basePolynomial.derivative.derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  conv in basePolynomial =>
    simp only [basePolynomial, boundaryHorner, boundaryCoefficients]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11]

theorem boundary_small_gap_floor {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    600 ≤ boundary h (1 / 30) := by
  have hf := LowT.polynomial_floor_of_concave_derivative (p := basePolynomial) (m := 600)
    h0 h1 (fun s hs0 _ => base_third_nonpos hs0)
    (by norm_num [basePolynomial, boundaryHorner, boundaryCoefficients,
      Polynomial.derivative_mul, Polynomial.derivative_pow])
    (by norm_num [basePolynomial, boundaryHorner, boundaryCoefficients])
    (by norm_num [basePolynomial, boundaryHorner, boundaryCoefficients])
  rwa [base_eval] at hf

theorem boundary_outer_gap_floor {h : ℝ} (h0 : 1 / 4 ≤ h) :
    (1 + 2 * (5 / 7 * h)) ^ 6 ≤ boundary h (5 / 7 * h) := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  rw [← boundaryHorner_eq]
  norm_num [boundaryHorner, boundaryCoefficients]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11, lo 12,
    lo 13, lo 14, lo 15]

end SmoothedOctagon.LowTScale
