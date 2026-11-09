module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse

/-!
# Case M2: the scalar exclusion of the smaller-nonshort window

The first actual switch after `r` is forward or reverse. A reverse successor is excluded
(`m2_reverse_exclusion`), and so is a forward successor (`m2_forward_exclusion`).

## Main API

* `m2_nonshort_scalar`: no actual window exists.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **No actual smaller-nonshort window**: both successor alternatives, forward and reverse, are
excluded. -/
theorem m2_nonshort_scalar (W : M2Window)
    (h : W.ForwardNext ∨ W.ReverseNext) : False := by
  rcases h with hF | hR
  · exact m2_forward_exclusion W hF
  · exact m2_reverse_exclusion W hR

end SmoothedOctagon
