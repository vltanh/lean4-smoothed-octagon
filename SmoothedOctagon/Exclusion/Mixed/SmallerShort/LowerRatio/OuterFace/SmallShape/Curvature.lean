module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Curvature.Corner

/-! # A uniform bound for the reciprocal-shape curvature coefficient -/

@[expose] public section
namespace SmoothedOctagon

/-- Norm, displacement and ratio comparisons reduce the bound to a single corner. -/
theorem lro_small_shape_curvature {x C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 4 / 5) (hu : 3 / 4 ≤ u) :
    2 * lrb2 x C u + 5 * lrb3 x C u < -1 / 24 := by
  have hn := LowerRatioCurvature.le_lower_norm hx hx2 hC0 hC1 hu
  have hC := LowerRatioCurvature.le_upper_displacement hx hC1
  have hr := LowerRatioCurvature.le_ratio_corner hx
  have hc : LowerRatioCurvature.value (3 / 2) (4 / 5) (3 / 4) < -1 / 24 := by
    rw [LowerRatioCurvature.lower_norm_eq (by norm_num) (by norm_num)]
    norm_num [LowerRatioCurvature.base, LowerRatioCurvature.baseA, LowerRatioCurvature.baseB,
      LowerRatioCurvature.baseK, LowerRatioCurvature.baseH]
  exact lt_of_le_of_lt (hn.trans (hC.trans hr)) hc

end SmoothedOctagon
