module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Boundary
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Duration
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Slope
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.Zero

/-!
# The low-`t` circuit increases with scale

The third duration derivative of the scale derivative is nonnegative,
and its duration slope at the right endpoint is nonpositive. The minimum
therefore occurs at zero or maximum duration. Both endpoint values are
positive.
-/

@[expose] public section
namespace SmoothedOctagon

/-- The scale derivative is positive throughout the physical low-`t` unit domain. -/
theorem nlt_HS_pos {h j y : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j1 : 1 / 30 ≤ j)
    (j2 : j ≤ 5 / 7 * h) (hy0 : 0 ≤ y) (hy : y * (1 + 2 * j) ≤ h - j) : 0 < polyHorner (nltDer (nltL0 j)) h + polyHorner (nltDer (nltL1 j)) h * y + polyHorner (nltDer (nltL2 j)) h * y ^ 2 + polyHorner (nltDer (nltL3 j)) h * y ^ 3 + polyHorner (nltDer (nltL4 j)) h * y ^ 4 + polyHorner (nltDer (nltL5 j)) h * y ^ 5 + polyHorner (nltDer (nltL6 j)) h * y ^ 6 := by
  have hd : 0 < 1 + 2 * j := by linarith only [j1]
  have hj : j ≤ 1 / 4 := by linarith only [j2, h2]
  have hyb : y ≤ (h - j) / (1 + 2 * j) := (le_div_iff₀ hd).mpr hy
  have hb : (h - j) / (1 + 2 * j) ≤ 9 / 32 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [h2, j1]
  have hf := LowT.polynomial_floor_of_convex_derivative
    (p := LowTScale.durationPolynomial h j) (m := 1) hy0 hyb
    (fun s hs0 hs1 => LowTScale.duration_third_nonneg h1 h2 j1 hj hs0 (hs1.trans hb))
    (LowTScale.duration_derivative_at_max_nonpos h1 h2 j1 hj)
    (by rw [LowTScale.duration_eval]; exact LowTScale.zero_floor h1 h2 (by linarith only [j1]) j2)
    (by rw [LowTScale.duration_eval]; exact LowTScale.boundary_floor h1 h2 j1 j2)
  rw [LowTScale.duration_eval, LowTScale.value_eq] at hf
  linarith only [hf]

end SmoothedOctagon
