module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A logarithm bound on the unit interval

* `ra_half_sub_inv_le_log`: `(x - x⁻¹)/2 ≤ log x` for `0 < x ≤ 1` (equivalently `y ≤ sinh y`
  for `y ≥ 0`). This is the sharp second-order lower bound used by the four-piece and five-piece
  density estimates.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `(x - x⁻¹)/2 ≤ log x` on `(0, 1]`: with `y = -log x ≥ 0` this is `y ≤ sinh y`. -/
theorem ra_half_sub_inv_le_log {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (x - x⁻¹) / 2 ≤ Real.log x := by
  have hy : 0 ≤ -Real.log x := neg_nonneg.2 (Real.log_nonpos hx0.le hx1)
  have h := Real.self_le_sinh_iff.2 hy
  rw [Real.sinh_eq, neg_neg, Real.exp_log hx0, Real.exp_neg, Real.exp_log hx0] at h
  linarith

end SmoothedOctagon
