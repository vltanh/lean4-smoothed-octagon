module

public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Upper.Sign

/-!
# The symmetric forward sum residual

The original threshold-`1/32` residual is negative on its full physical domain.
Paired reciprocal means and the fixed tangent reduce it to the two factor endpoints.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The symmetric sum residual is negative throughout its physical factor interval. -/
theorem fs_resS_neg {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3)
    (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U))) :
    ff_resS U z z h < 0 := by
  simpa only [fwdSumResidual32, ff_resS] using
    (fwdSumResidual32_original_neg hz hz' hU hU3 hhl hhu)

end SmoothedOctagon
