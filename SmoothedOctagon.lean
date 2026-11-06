module

public import SmoothedOctagon.Problem
public import SmoothedOctagon.Normalization
public import SmoothedOctagon.BoundaryTrace
public import SmoothedOctagon.SwitchingMargin
public import SmoothedOctagon.StrongSwitching

/-!
# Research toward the Reinhardt conjecture

The conjecture is stated in `SmoothedOctagon.Problem`; it is not asserted as a theorem.
`SmoothedOctagon.SwitchingMargin` supplies a quantitative bound for one explicit scalar
switching expression. See `CHECKLIST.md` for the remaining mathematical obligations.

The actual-minimizer normalization and continuous boundary construction begin the G2
reduction. This source development has not been compiled or kernel-checked.
-/
