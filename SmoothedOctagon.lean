module

public import SmoothedOctagon.Problem
public import SmoothedOctagon.Normalization
public import SmoothedOctagon.BoundaryTrace
public import SmoothedOctagon.SupportNormal
public import SmoothedOctagon.RadialRegularity
public import SmoothedOctagon.ArcLength
public import SmoothedOctagon.BalancedReduction
public import SmoothedOctagon.BalancedTargets
public import SmoothedOctagon.DeterminantClock
public import SmoothedOctagon.ControlTrajectory
public import SmoothedOctagon.ContactLift
public import SmoothedOctagon.SwitchingMargin
public import SmoothedOctagon.StrongSwitching

/-!
# Research toward the Reinhardt conjecture

The conjecture is stated in `SmoothedOctagon.Problem`; it is not asserted as a theorem.
`SmoothedOctagon.SwitchingMargin` supplies a quantitative bound for one explicit scalar
switching expression. See `CHECKLIST.md` for the remaining mathematical obligations.

`BalancedReduction` constructs a balanced circle minimizer from an actual worst disk;
`BalancedTargets` identifies the exact remaining area and rigidity targets. This source
development has not been compiled or kernel-checked.
-/
