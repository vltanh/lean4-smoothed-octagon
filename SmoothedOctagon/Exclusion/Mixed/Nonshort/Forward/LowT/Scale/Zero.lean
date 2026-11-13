module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Polynomial

/-!
# The scale derivative at zero duration increment

It decreases with the order gap. The minimum therefore lies at the outer
gap, where its expansion at scale `1/4` has positive coefficients.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

private noncomputable def zeroJ (h : ℝ) : Polynomial ℝ :=
  coefficient 0 (Polynomial.C h) Polynomial.X

private theorem zero_eval (h j : ℝ) : (zeroJ h).eval j = coefficient 0 h j := by
  simp [zeroJ, coefficient, row0]

set_option maxRecDepth 4096 in
private theorem zero_concave {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 1 / 4) : (zeroJ h).derivative.derivative.eval j ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * j ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hj0 k)
  have hi (i k : ℕ) : u ^ i * j ^ k ≤ (1 / 12 : ℝ) ^ i * (1 / 4 : ℝ) ^ k :=
    mul_le_mul (pow_le_pow_left₀ hu hu1 i) (pow_le_pow_left₀ hj0 hj1 k)
      (pow_nonneg hj0 k) (by positivity)
  conv in (zeroJ _) =>
    simp only [zeroJ]
    norm_num only [coefficient]
    simp only [row0]
    norm_num
    ring_nf
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [hi 6 0, hi 5 1, hi 5 0, hi 4 2, hi 4 1, hi 4 0, hi 3 3, hi 3 2, hi 3 1, hi 3 0, hi 2 4, hi 2 3, hi 2 2, hi 2 1, hi 2 0, hi 1 4, hi 1 3, hi 1 2, lo 1 1, hi 1 0, lo 0 4, lo 0 3, lo 0 2, lo 0 1]

private theorem zero_first_nonpos {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    (zeroJ h).derivative.eval 0 ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 12 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [zeroJ, coefficient, row0, Polynomial.derivative_mul, Polynomial.derivative_pow]
  nlinarith only [hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7]

private theorem zero_outer_floor {h : ℝ} (h0 : 1 / 4 ≤ h) :
    1 ≤ coefficient 0 h (5 / 7 * h) := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  norm_num [coefficient, row0]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8]

theorem zero_floor {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 5 / 7 * h) : 1 ≤ value h j 0 := by
  have hb : 5 / 7 * h ≤ 1 / 4 := by linarith only [h1]
  have hd {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 4) : (zeroJ h).derivative.eval s ≤ 0 := by
    have hm := poly_anti (fun v => (zeroJ h).derivative.hasDerivAt v) (a := 0) (b := 1 / 4)
      (fun v hv0 hv1 => zero_concave h0 h1 hv0 hv1) le_rfl hs0 hs1
    exact hm.trans (zero_first_nonpos h0 h1)
  have hm := poly_anti (fun v => (zeroJ h).hasDerivAt v) (a := 0) (b := 1 / 4)
    (fun v hv0 hv1 => hd hv0 hv1) hj0 hj1 hb
  rw [zero_eval, zero_eval] at hm
  have hf := (zero_outer_floor h0).trans hm
  simpa [value, Fin.sum_univ_succ] using hf

end SmoothedOctagon.LowTScale
