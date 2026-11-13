module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.SlopeBounds
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.InitialSlope

/-!
# The duration slope at its right endpoint is negative

A nonpositive fourth scale derivative gives a cubic upper bound from
scale `1/4`. The initial bounds, before the common factor six, are
`-17000`, `-125000`, `7000000`, and `30000000`. On a scale interval of
length `1/12`, this cubic is negative.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

theorem boundaryDerivative_nonpos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) : boundaryDerivative h j ≤ 0 := by
  let p := slopePolynomial j
  have h3 {s : ℝ} (hs0 : 1 / 4 ≤ s) (hs1 : s ≤ 1 / 3) :
      p.derivative.derivative.derivative.eval s ≤ 180000000 := by
    have hm := poly_anti (fun v => p.derivative.derivative.derivative.hasDerivAt v)
      (a := 1 / 4) (b := 1 / 3)
      (fun v hv0 hv1 => by
        simpa only [p, Function.iterate_succ_apply, Function.iterate_zero_apply] using
          slope_fourth_nonpos hv0 hv1 hj0 hj1) le_rfl hs0 hs1
    have hb := slope_jet3_ceiling hj0 hj1
    rw [slopeJet_eval] at hb
    exact hm.trans (by
      simpa only [p, Function.iterate_succ_apply, Function.iterate_zero_apply] using hb)
  have ht := nlt_taylor3 (a := 1 / 4) (b := 1 / 3) (c := -180000000)
    (fun s => (p.hasDerivAt s).neg)
    (fun s => (p.derivative.hasDerivAt s).neg)
    (fun s => (p.derivative.derivative.hasDerivAt s).neg)
    (fun s hs0 hs1 => neg_le_neg (h3 hs0 hs1)) h0 h1
  have hb0 := slope_jet0_ceiling hj0 hj1
  have hb1 := slope_jet1_ceiling hj0 hj1
  have hb2 := slope_jet2_ceiling hj0 hj1
  rw [slopeJet_eval] at hb0 hb1 hb2
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at hb0 hb1 hb2
  have hu : 0 ≤ h - 1 / 4 := sub_nonneg.mpr h0
  have hu1 : h - 1 / 4 ≤ 1 / 12 := by linarith only [h1]
  have hu2 : (h - 1 / 4) ^ 2 ≤ (h - 1 / 4) / 12 := by
    nlinarith only [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hu3 : (h - 1 / 4) ^ 3 ≤ (h - 1 / 4) / 144 := by
    have ha := mul_le_mul_of_nonneg_left hu2 hu
    nlinarith only [ha, hu2]
  have he1 := mul_le_mul_of_nonneg_left hb1 hu
  have he2 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg (h - 1 / 4))
  rw [← slope_eval]
  change p.eval h ≤ 0
  dsimp only [Pi.neg_apply, p] at ht ⊢
  nlinarith only [ht, hb0, he1, he2, hu1, hu2, hu3]

theorem duration_derivative_at_max_nonpos {h j : ℝ}
    (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) :
    (durationPolynomial h j).derivative.eval ((h - j) / (1 + 2 * j)) ≤ 0 := by
  have hd : 0 < 1 + 2 * j := by linarith only [hj0]
  have hb := boundaryDerivative_nonpos h0 h1 hj0 hj1
  rw [← boundaryDerivative_eq h j hd.ne'] at hb
  exact nonpos_of_mul_nonpos_right hb (pow_pos hd 5)

end SmoothedOctagon.LowTScale
