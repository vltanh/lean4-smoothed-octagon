module

public import SmoothedOctagon.Exclusion.Mixed.Comparison

/-!
# Case M2: the common low-scale region `a ≤ 1/2`, by hand

`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` (with `MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE`,
`MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION`, accepted in `MIXED_NONSHORT_LOW_SCALE_HAND_AUDIT`); it
replaces the cover Cert-LOWA (`MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION`), which is not used. No
successor sign is assumed: the boundary comparison `G(b*) < 0` (`m2_comparison`), the shape
monotonicity (`MIXED_NONSHORT_SHAPE_MONOTONICITY`), the domain bounds `t < 7/20`, `x > 3/13` and
six quartic coefficient inequalities exclude every actual window with `a ≤ 1/2`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The low-scale region is empty** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`): every actual
smaller-nonshort window has `a > 1/2`. -/
theorem m2_lowScale_hand (W : M2Window) (ha : W.a ≤ 1 / 2) : False := by
  sorry

end SmoothedOctagon
