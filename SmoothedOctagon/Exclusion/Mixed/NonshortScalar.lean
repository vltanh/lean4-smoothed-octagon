module

public import SmoothedOctagon.Exclusion.Mixed.ForwardHand
public import SmoothedOctagon.Exclusion.Mixed.ReverseHand
public import SmoothedOctagon.Exclusion.Mixed.LowScaleHand

/-!
# Case M2: the scalar exclusion of the smaller-nonshort window

`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §§4-5. The first actual switch after `r` is forward or
reverse (CONT §3). A reverse successor is excluded by hand (`m2_reverse_hand`). For a forward
successor is excluded by hand too (`m2_forward_exclusion`: `m2_lowScale_hand` for `a ≤ 1/2`, the
hand forward theorem `MIXED_NONSHORT_FORWARD_HAND_EXCLUSION` for `a > 1/2`).

## Main API

* `m2_forward_exclusion`: no actual window has a forward successor.
* `m2_nonshort_scalar`: no actual window exists.
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates

/-- **The forward successor is excluded** (gate H-N, `MIXED_NONSHORT_FORWARD_HAND_EXCLUSION`):
no interval cover is used. -/
theorem m2_forward_exclusion (W : M2Window) (hF : W.ForwardNext) : False :=
  m2_forward_hand W hF

/-- **No actual smaller-nonshort window** (`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §§4-5): both
successor alternatives of CONT (15) are excluded. -/
theorem m2_nonshort_scalar (W : M2Window)
    (h : W.ForwardNext ∨ W.ReverseNext) : False := by
  rcases h with hF | hR
  · exact m2_forward_exclusion W hF
  · exact m2_reverse_hand W hR

end SmoothedOctagon
