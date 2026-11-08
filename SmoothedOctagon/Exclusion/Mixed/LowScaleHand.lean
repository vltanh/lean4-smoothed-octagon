module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Exclusion.Mixed.Hand.Low
public import SmoothedOctagon.Exclusion.Mixed.Hand.Prereq

/-!
# Case M2: the common low-scale region `a ≤ 1/2`, by hand

`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` (with `MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE`,
`MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION`, accepted in `MIXED_NONSHORT_LOW_SCALE_HAND_AUDIT`); it
replaces the cover Cert-LOWA (`MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION`), which is not used. No
successor sign is assumed: the boundary comparison `G(b*) < 0` (`m2_comparison`), the shape
monotonicity (`MIXED_NONSHORT_SHAPE_MONOTONICITY`), the domain bounds `t < 7/20`, `x > 3/13` and
six quartic coefficient inequalities exclude every actual window with `a ≤ 1/2`.

Since `a²(k - t²) = 4t²`, `a ≤ 1/2` is `k ≥ 17t²`; the scalar argument is `nh_low_core`
(`Hand/Low`): `t < T(x)` and `t < 7/20` (domain reduction), the scalar reverse exclusion
`nh_reverse_core` when `k ≥ 2t + x` (the common order of `MIXED_NONSHORT_REVERSE_HAND_EXCLUSION`
§5), otherwise the unit face (`t ≤ 1/4`) or the high-ratio face `k = 2t + 1/2` (`t ≥ 1/4`). The
window-level inputs are `nh_window_N_neg` (from the upstream `m2_comparison`), the centre gap
`nh_centre_gap_k` and the duration bound `nh_window_dur_x`.

Route: the six signs (9) on both faces are proved by generated Bernstein certificates checked by
`ring` (`Hand/CertLow`), in place of §§4-7 and of `MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The low-scale region is empty** (`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`): every actual
smaller-nonshort window has `a > 1/2`. -/
theorem m2_lowScale_hand (W : M2Window) (ha : W.a ≤ 1 / 2) : False := by
  obtain ⟨ht, ht2, hx, hk1, hq, hqW, hv, hvU, hg, hF, hak⟩ := nh_window_basic W
  -- `a ≤ 1/2` is `k ≥ 17t²`
  have hk17 : 17 * W.nt ^ 2 ≤ W.nk := by
    have ha0 := W.a_pos
    have ha2 : W.a ^ 2 ≤ 1 / 4 := by nlinarith
    have hkt : 0 ≤ W.nk - W.nt ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ha2 hkt]
  have hN := nh_low_core ht ht2 hx hk1.le hk17 (nh_centre_gap_k W) (nh_window_dur_x W) hq hqW hv
    hvU hg hF
  linarith [nh_window_N_neg W]

end SmoothedOctagon
