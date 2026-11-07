module

public import SmoothedOctagon.Foundations.Problem
public import SmoothedOctagon.Foundations.Normalization
public import SmoothedOctagon.Foundations.BoundaryTrace
public import SmoothedOctagon.Foundations.SupportNormal
public import SmoothedOctagon.Foundations.RadialRegularity
public import SmoothedOctagon.Foundations.ArcLength
public import SmoothedOctagon.Foundations.BalancedReduction
public import SmoothedOctagon.Foundations.BalancedTargets
public import SmoothedOctagon.Foundations.DeterminantClock
public import SmoothedOctagon.Foundations.ControlTrajectory
public import SmoothedOctagon.Foundations.ContactLift
public import SmoothedOctagon.Foundations.BalancedClock
public import SmoothedOctagon.Foundations.CyclicClock
public import SmoothedOctagon.Foundations.AdmissibleRealization
public import SmoothedOctagon.Foundations.LowCostWinding
public import SmoothedOctagon.Foundations.AdmissibleRegularity
public import SmoothedOctagon.Foundations.ControlBounds
public import SmoothedOctagon.Foundations.ReverseGeometry
public import SmoothedOctagon.Foundations.CyclicExtension
public import SmoothedOctagon.Foundations.ReverseComparison
public import SmoothedOctagon.Foundations.SingularLocus
public import SmoothedOctagon.Foundations.CircleExclusion
public import SmoothedOctagon.Foundations.SingularArc
public import SmoothedOctagon.Foundations.SwitchingMargin
public import SmoothedOctagon.Foundations.StrongSwitching

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
`SingularLocus` and `SingularArc` identify control independence and its interval rigidity;
`CircleExclusion` rules out only an entirely circular full minimizer.
This source development has not been compiled or kernel-checked.
-/
