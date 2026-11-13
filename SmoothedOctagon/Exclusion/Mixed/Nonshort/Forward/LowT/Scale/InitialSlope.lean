module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.SlopeData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monomials

/-!
# Initial values of the maximum-duration slope

The slope numerator decreases with the gap at scale `1/4`. Its first scale
derivative has a quadratic upper bound centered at gap `1/7`.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

private theorem initial_decreases {j : ℝ} (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (slopeJet 0).derivative.eval j ≤ 0 := by
  obtain ⟨v, rfl⟩ : ∃ v, j = 1 / 30 + v := ⟨j - 1 / 30, by ring⟩
  have hv : 0 ≤ v := by linarith only [hj0]
  have hv1 : v ≤ 13 / 60 := by linarith only [hj1]
  have lo (n : ℕ) : 0 ≤ v ^ n := pow_nonneg hv n
  have step (n : ℕ) : v ^ (n + 1) ≤ (13 / 60 : ℝ) * v ^ n := nlt_pw hv hv1 n
  rw [slopeJet_zero]
  conv in (slopeHorner _ _) =>
    simp only [slopeHorner, slopeCoefficients]
    norm_num
    ring_nf
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_ofNat,
    zero_mul, mul_zero, add_zero]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_zero, Polynomial.eval_one]
  ring_nf
  linarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11, lo 12,
    step 0, step 1, step 2, step 3, step 4, step 5, step 6, step 7, step 8, step 9, step 10, step 11]

theorem slope_jet0_ceiling {j : ℝ} (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (slopeJet 0).eval j ≤ -102000 := by
  have hm := poly_anti (fun v => (slopeJet 0).hasDerivAt v) (a := 1 / 30) (b := 1 / 4)
    (fun v hv0 hv1 => initial_decreases hv0 hv1) le_rfl hj0 hj1
  have hb : (slopeJet 0).eval (1 / 30) ≤ -102000 := by
    norm_num [slopeJet_zero, slopeHorner, slopeCoefficients]
  exact hm.trans hb

private theorem first_quadratic {v : ℝ} (hv0 : -(1 / 9) ≤ v) (hv1 : v ≤ 1 / 9) :
    (slopeJet 1).eval (1 / 7 + v) ≤ -750000 := by
  have ha : |v| ≤ 1 / 9 := abs_le.mpr ⟨hv0, hv1⟩
  have rem (n : ℕ) : |v ^ (n + 2)| ≤ (1 / 9 : ℝ) ^ n * v ^ 2 := by
    rw [pow_add, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg v)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg v) ha n) (sq_nonneg v)
  have lo (n : ℕ) : -((1 / 9 : ℝ) ^ n * v ^ 2) ≤ v ^ (n + 2) := (abs_le.mp (rem n)).1
  have hi (n : ℕ) : v ^ (n + 2) ≤ (1 / 9 : ℝ) ^ n * v ^ 2 := (abs_le.mp (rem n)).2
  rw [slopeJet_eval, slope_derivative_horner]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, nltDer, nltDerAux,
    slopeCoefficients, polyHorner]
  ring_nf
  nlinarith only [lo 1, hi 1, lo 2, hi 2, lo 3, hi 3, lo 4, hi 4, lo 5, hi 5,
    lo 6, hi 6, lo 7, hi 7, lo 8, hi 8, lo 9, hi 9, lo 10, hi 10, lo 11, hi 11,
    sq_nonneg (v + 3 / 32), hv0]

theorem slope_jet1_ceiling {j : ℝ} (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (slopeJet 1).eval j ≤ -750000 := by
  have hm := first_quadratic (v := j - 1 / 7)
    (by linarith only [hj0]) (by linarith only [hj1])
  convert hm using 1; congr 2; ring

end SmoothedOctagon.LowTScale
