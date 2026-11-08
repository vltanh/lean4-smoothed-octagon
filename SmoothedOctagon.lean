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
public import SmoothedOctagon.Main

/-!
# The Reinhardt conjecture

The smoothed octagon has the least greatest packing density among centrally symmetric convex disks
in the plane, `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`, and it is the only such disk up to invertible
affine maps.

The proof is organized by stage:

* `Foundations/`: the geometric reformulation. A worst disk, normalized and parametrized by its
  balanced boundary, is realized by a trajectory of Hales's control problem whose cost is its area;
  conversely every admissible trajectory of cost below `π`, with any measurable control, bounds a
  balanced disk of that area. So the conjecture is equivalent to the control lower bound, and the
  realization of a worst disk is a global control minimizer.
* `Reduction/`: a global minimizer is a normal vertex period with finitely many pieces in the compact
  domain `𝔥**`.
* `Period/`: vertex periods, margins, switch signs and the partition of sign sequences into the
  classes R, F, M3, M1, M2.
* `Exclusion/`: each class is impossible for competitive periods with at least six pieces.
* `Terminal/`: periods with at most five pieces cost at least `A_oct`, with equality only for the
  octagon.
* `LowerBound`, `Equality/`, `Main`: the assembly.
* `Certificates/`: the interval covers used by cases F and M2, named hypotheses until their hand
  replacements are complete.

`Cited/` holds Hales–Vajjha's Definition 5.0.1 of the compact domain `𝔥**`. Their Theorem 5.0.2
is proved in `lean4-smoothed-polygon` (`SmoothedPolygons.theorem5_0_2`) and bridged in
`Reduction/CompactDomain.lean`.
-/
