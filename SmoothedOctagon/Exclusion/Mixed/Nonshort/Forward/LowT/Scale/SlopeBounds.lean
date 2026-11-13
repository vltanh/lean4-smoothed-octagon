module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.SlopeData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monomials

/-!
# Scale estimates for the maximum-duration slope

At scale `1/4`, a gap comparison bounds the value and a quadratic Taylor
estimate bounds the first scale derivative. A nonpositive fourth derivative
then gives a cubic upper bound throughout the scale interval.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

theorem slope_fourth_nonpos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    ((Polynomial.derivative^[4]) (slopePolynomial j)).eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = 1 / 4 + u := ⟨h - 1 / 4, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 13 / 60 := by linarith only [hj1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * v ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hv k)
  have hi (i k : ℕ) : u ^ i * v ^ k ≤ (1 / 12 : ℝ) ^ i * (13 / 60 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hv hv1 k)
      (pow_nonneg hv k) (by positivity)
  rw [slope_derivative_horner]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, nltDer, nltDerAux,
    slopeCoefficients, polyHorner]
  ring_nf
  linarith only [lo 9 1, lo 9 0, lo 8 2, lo 8 1, lo 8 0, lo 7 3, lo 7 2, lo 7 1, lo 7 0, lo 6 4, lo 6 3, lo 6 2, lo 6 1, lo 6 0, lo 5 5, lo 5 4, lo 5 3, lo 5 2, lo 5 1, lo 5 0, hi 4 6, hi 4 5, lo 4 4, lo 4 3, lo 4 2, lo 4 1, lo 4 0, hi 3 7, hi 3 6, hi 3 5, lo 3 4, lo 3 3, lo 3 2, lo 3 1, lo 3 0, hi 2 8, hi 2 7, hi 2 6, hi 2 5, hi 2 4, lo 2 3, lo 2 2, lo 2 1, lo 2 0, hi 1 9, hi 1 8, hi 1 7, hi 1 6, hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, hi 0 10, hi 0 9, hi 0 8, hi 0 7, hi 0 6, hi 0 5, hi 0 4, hi 0 3, lo 0 2, lo 0 1]

theorem slope_jet2_ceiling {j : ℝ} (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (slopeJet 2).eval j ≤ 42000000 := by
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 13 / 60 := by linarith only [hj1]
  have lo (n : ℕ) : 0 ≤ v ^ n := pow_nonneg hv n
  have hi (n : ℕ) : v ^ n ≤ (13 / 60 : ℝ) ^ n := pow_le_pow_left₀ hv hv1 n
  rw [slopeJet_eval, slope_derivative_horner]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, nltDer, nltDerAux,
    slopeCoefficients, polyHorner]
  ring_nf
  linarith only [lo 12, lo 11, lo 10, lo 9, lo 8, lo 7, hi 6, hi 5, hi 4, hi 3, hi 2, hi 1]

theorem slope_jet3_ceiling {j : ℝ} (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (slopeJet 3).eval j ≤ 180000000 := by
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 13 / 60 := by linarith only [hj1]
  have lo (n : ℕ) : 0 ≤ v ^ n := pow_nonneg hv n
  have step (n : ℕ) : v ^ (n + 1) ≤ (13 / 60 : ℝ) * v ^ n := nlt_pw hv hv1 n
  rw [slopeJet_eval, slope_derivative_horner]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, nltDer, nltDerAux,
    slopeCoefficients, polyHorner]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11, step 0, step 1, step 2, step 3, step 4, step 5, step 6, step 7, step 8, step 9, step 10]

end SmoothedOctagon.LowTScale
