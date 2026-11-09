module

public import SmoothedOctagon.Exclusion.Mixed.ForwardHand
public import SmoothedOctagon.Exclusion.Mixed.ReverseHand

/-!
# Case M2: the scalar exclusion of the smaller-nonshort window

The first actual switch after `r` is forward or reverse. A reverse successor is excluded by hand
(`m2_reverse_hand`), and so is a forward successor (`m2_forward_hand`).

## Main API

* `m2_forward_exclusion`: no actual window has a forward successor.
* `m2_nonshort_scalar`: no actual window exists.
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates

/-- **The forward successor is excluded** (`m2_forward_hand`). -/
theorem m2_forward_exclusion (W : M2Window) (hF : W.ForwardNext) : False :=
  m2_forward_hand W hF

/-- **No actual smaller-nonshort window**: both successor alternatives, forward and reverse, are
excluded. -/
theorem m2_nonshort_scalar (W : M2Window)
    (h : W.ForwardNext ∨ W.ReverseNext) : False := by
  rcases h with hF | hR
  · exact m2_forward_exclusion W hF
  · exact m2_reverse_hand W hR

end SmoothedOctagon
