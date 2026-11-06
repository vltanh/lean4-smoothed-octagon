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
public import SmoothedOctagon.BalancedClock
public import SmoothedOctagon.CyclicClock
public import SmoothedOctagon.AdmissibleRealization
public import SmoothedOctagon.LowCostWinding
public import SmoothedOctagon.AdmissibleRegularity
public import SmoothedOctagon.ControlBounds
public import SmoothedOctagon.ReverseGeometry
public import SmoothedOctagon.CyclicExtension
public import SmoothedOctagon.ReverseComparison
public import SmoothedOctagon.SingularLocus
public import SmoothedOctagon.SwitchingMargin
public import SmoothedOctagon.StrongSwitching

/-!
# Research toward the Reinhardt conjecture

The conjecture is stated in `SmoothedOctagon.Problem`; it is not asserted as a theorem.
`SmoothedOctagon.SwitchingMargin` supplies a quantitative bound for one explicit scalar
switching expression. See `CHECKLIST.md` for the remaining mathematical obligations.

`BalancedReduction` constructs a balanced circle minimizer from an actual worst disk;
`BalancedTargets` identifies the exact remaining area and rigidity targets.
`AdmissibleRealization` constructs the full forward control realization with exact area cost.
`ReverseComparison` constructs geometric competitors for all admissible controls and proves
the exact global control-minimizer correspondence. The octagon lower bound remains open.
This source development has not been compiled or kernel-checked.
-/
