# Lean 4 research toward the Reinhardt conjecture

This project starts from the concrete smoothed octagon in
[`vltanh/lean4-smoothed-polygon`](https://github.com/vltanh/lean4-smoothed-polygon)
and targets its **global minimality among all centrally symmetric convex disks**, followed
by uniqueness up to affine equivalence.

The current source milestone is a constructive reduction in both directions between the
geometric worst-disk problem and the full integral-form control problem. It includes actual
global control-minimizer existence. The universal octagon lower bound and affine equality
classification remain open, and none of the new source has been kernel-validated.

The current working agreement prioritizes **hand-proof research on the unrestricted
comparison**. New Lean infrastructure is paused. Exploratory computation is permitted
as a research aid, with its domain and limitations recorded; sampled or symbolic output
does not certify an inequality.

The candidate density is

\[
\delta_{\mathrm{oct}}=
\frac{8-\sqrt{32}-\log 2}{\sqrt 8-1}.
\]

## Current hand-proof comparison

The strongest restricted result is a complete hand comparison for **every admissible
trajectory representable with at most five positive-duration vertex-control pieces**,
including asymmetric initial states and unequal durations. Its cost is at least the
octagon's, with equality only in the octagon case under cyclic rebasing and the stated
affine normalization. No Pontryagin or symmetry assumption is imposed on the competitor.

The coverage has three parts. At four pieces, endpoint algebra leaves one family and
a strict integral inequality selects the octagon; see
[docs/FOUR_LINK_HAND_PROOF.md](docs/FOUR_LINK_HAND_PROOF.md). At five pieces, cyclic
rebasing leaves a four-piece merger and two genuine word orbits. A sharp logarithmic
envelope proves strict comparison for the whole asymmetric `01020` orbit in
[docs/FIVE_ARC_PROGRESS.md](docs/FIVE_ARC_PROGRESS.md). The reverse cyclic orbit `02102`
has a stronger uniform bound,

\[
\frac{C}{\sqrt{12}}>\frac{10}{11}>\frac{\pi}{\sqrt{12}}>\delta_{\rm oct},
\]

proved by exact half-angle identities and an elementary logarithm envelope in
[docs/REVERSE_FIVE_ARC.md](docs/REVERSE_FIVE_ARC.md). Its full positive parameter
domain, initial state, and whole-arc star constraints are included.

A sharper follow-up also finds the unique minimum within that entire reverse family:
all five factors equal the golden ratio. Its exact normalized cost is
`5(2√5−2−log φ)/(2(1+2√5))`. The complete asymmetric comparison uses a strictly
concave integral function and an explicit derivative sign; see
[docs/REVERSE_FIVE_MINIMUM.md](docs/REVERSE_FIVE_MINIMUM.md).

A cheaper finite vertex-control competitor must therefore require at least six pieces.
Arbitrary longer words remain open; there is no bound on the number of pieces in an
arbitrary minimizer.

At six pieces, the entire asymmetric orbits `010202` and `012012` also cost strictly
more than the octagon. For `010202`, the bound is sharp as an unattained infimum: an
explicit feasible family converges to the octagon as two durations vanish. The proof
and complete six-piece word classification are in
[docs/SIX_ARC_010202.md](docs/SIX_ARC_010202.md). A concurrent, independently reviewed
proof gives a monotone deformation of every member of that orbit to the compared
five-piece boundary; see [docs/SIX_ARC_REVERSE_BLOCK.md](docs/SIX_ARC_REVERSE_BLOCK.md).

For `012012`, a compact family preserves the actual endpoints and the entire strict
star domain. A negative constrained second variation forces its minimum to one of
two genuine five-piece boundary trajectories; see
[docs/SIX_ARC_012012.md](docs/SIX_ARC_012012.md). The other raw six-piece orbit `010102`
is infeasible by cyclic ordering. Thus `012102` is the only remaining six-piece
comparison, while arbitrary longer words remain open.

For an arbitrary admissible star state `X=[[a,b],[c,-a]]`, put
`m=(c-b)/2` and `n=√(a²+((b+c)/2)²)`. The determinant identity gives `m²-n²=1`,
and the cost is `C=3∫m`. The new hand estimate for `C<π` is

\[
\pi-C\le3\int_0^T n(t)\,dt,
\qquad
C\ge\frac{\pi^2+9T^2}{2\pi}.
\]

In particular, if `n/m≤η₀` throughout the interval, then `C≥π/(1+η₀)`.
Writing `A` for the concrete octagon area, every trajectory with
`η₀<π/A−1` therefore costs strictly more than the octagon. This excludes a precise
class of arbitrary nonsymmetric competitors. It supplies no uniform switch bound and
does not compare the remaining competitors. See
[docs/NEAR_CIRCLE_BOUND.md](docs/NEAR_CIRCLE_BOUND.md) for the complete hand proof and
[CHECKLIST.md](CHECKLIST.md) for the distinction between mathematical exclusions and
earlier formalization substeps.

There is also an endpoint obstruction covering arbitrary measurable controls: no
trajectory confined to one fixed edge of the control simplex can reach `g(T)=R` from
`g(0)=I` while staying in the strict star domain. Thus every admissible control satisfies
`∫u_j>0` for all three coordinates, and every finite vertex word must use all three
vertices. The proof requires neither optimality nor a finite switching description;
see [docs/SWITCHING_WORDS.md](docs/SWITCHING_WORDS.md).

Applying that obstruction after every cyclic time rebase excludes all words with at
most three arcs and all longer words violating `last(j)>first(j−1)`. At four arcs it
leaves only the forward order `0120`, whose full cost comparison is proved above.
[docs/VERTEX_WORD_REDUCTION.md](docs/VERTEX_WORD_REDUCTION.md) also gives exact
continuous-arc feasibility conditions and logarithmic costs for arbitrary words.

A separate local variation excludes **five consecutive arcs alternating between just
two vertices from any global minimizer**, at any total word length. It preserves both
endpoint frames and states exactly and strictly lowers cost by moving the switches;
see [docs/EDGE_SWITCH_BOUND.md](docs/EDGE_SWITCH_BOUND.md). This does not bound the
number of arcs using all three vertices. The shorter proposed `010`-to-two-arc deletion
is actually impossible with both endpoint pairs fixed, as proved in
[docs/LOCAL_SHORTENING_OBSTRUCTION.md](docs/LOCAL_SHORTENING_OBSTRUCTION.md).

The concurrent proof in
[docs/FORWARD_ALTERNATION_EXCLUSION.md](docs/FORWARD_ALTERNATION_EXCLUSION.md)
strengthens the local edge result to every forward four-arc alternation
`i,i+1,i,i+1`. A strictly negative constrained second variation handles the stationary
case. The reverse orientation is not excluded, and this still supplies no total arc bound.

[docs/WORD_HOLONOMY.md](docs/WORD_HOLONOMY.md) removes the initial-state ambiguity for
every noncentral finite word-factor tuple. It excludes hyperbolic/parabolic endpoint
holonomy, determines the unique possible elliptic state, and gives exact full-arc sign
tests. Central holonomies remain explicitly covered by a cone of possible initial
directions; their costs are not silently omitted from future comparison.

The hand argument in [docs/CIRCLE_VARIATION.md](docs/CIRCLE_VARIATION.md) constructs a
balanced convex competitor for any nonempty circle-state subarc. A smooth compactly
supported perturbation decreases its area by exactly `3∫sinh²(εχ)>0`. This recovers
the known singular circular-subarc exclusion with explicit geometric checks. The gain
can vanish as the support shrinks; it gives no uniform exclusion of all nearby or
chattering trajectories.

[docs/GLOBAL_CALIBRATION.md](docs/GLOBAL_CALIBRATION.md) records why several direct
bound strategies fail on their stated domains. In particular, dropping the state
equation permits exact strict-star frame paths cheaper than the octagon. Those paths
are inadmissible for Reinhardt because the state jumps. A successful sharp comparison
must retain the cost of allowed state transitions. The note gives a concrete coupled
calibration problem, with its missing certificate explicit.

## Initial mathematical contribution

For the existing scalar switching expression `SmoothedPolygons.hmaxF`, the new proof gives

\[
f(y,r)\ge
\frac{(r-y)^2(4-r)(r^2+3ry+4y^2)}{4r(r+y)}
+\frac{r(r-y)^3}{4(r+y)}
\ge\frac{(r-y)^3}{8}
\quad(2\le y\le r\le4).
\]

The argument is an exact algebraic certificate using two standard logarithm inequalities.
The reference project already proves the sign of this expression; the new result supplies
a quantitative margin.

The margin is also transported to the actual switching functions. For normalized strong
lifts with `λ_cost = -1`, `1/√3 < y₀ < 1`, and `0 ≤ t ≤ τ = switchTime y₀`,

\[
\chi_{32}(t)\ge\frac{\sqrt3}{2}t^3,
\qquad
\chi_{31}(t)\ge\frac{\sqrt3}{2}(\tau-t)^3.
\]

These estimates cover the specified strong-lift family. They do not bound the number of
switches or compare all smoothed polygons with the octagon.

## Global target and current status

`SmoothedOctagon/Problem.lean` states the conjecture against the existing geometric packing
definitions. The density is the greatest density of packings by congruent copies, with the
upstream theorem relating it to lattice packing. The module reuses the concrete candidate's
exact density, proves the candidate upper bound on the minimax value, and gives equivalent
global lower-bound criteria. In particular, it is enough to prove the candidate lower bound
for one actual worst disk; an upstream theorem supplies existence of such a disk.

`Normalization.lean` now starts with an actual worst disk, constructs an orientation-preserving
linear image with the six critical contact midpoints at the sixth roots of unity, and preserves
its greatest packing density. In that normal position, density is area divided by `2 * √3`.
`BoundaryTrace.lean` then constructs the six continuous contact curves, their common full
period `2π`, simple traversal, boundary coverage, and normalized initial values.
`SupportNormal.lean` and `RadialRegularity.lean` derive a regular positive `C¹` radial
curve from unique supporting lines. `ArcLength.lean` constructs the global Euclidean
arclength parameter. `BalancedReduction.lean` assembles every balanced-pair field and
constructs a balanced circle minimizer from an actual worst disk, preserving its density.
It also proves that a balanced circle area minimizer is an actual packing minimizer.

The resulting exact target transfer is

```lean
FullReinhardtConjecture ↔ BalancedAreaLowerBound ∧ BalancedAffineRigidity
```

The first remaining proposition is an area inequality over all balanced circle competitors;
the second classifies all balanced circle minimizers up to affine equivalence.
`DeterminantClock.lean` constructs the global matrix frame and a time change making its
logarithmic derivative a determinant-one star state with Lipschitz entries. `ContactLift.lean`,
`BalancedClock.lean`, and `CyclicClock.lean` construct uniform cyclic contact time and the
exact terminal conditions. `ControlTrajectory.lean` supplies the measurable control and
integral equations. `AdmissibleRealization.lean` combines these into an actual admissible
trajectory with `cost = normalized area` and `density = cost / √12`.

`AdmissibleRegularity.lean` and `CyclicExtension.lean` derive the global analytic data from
arbitrary integral-admissible controls. `LowCostWinding.lean` and `ReverseGeometry.lean`
construct a simple balanced convex disk of equal area when cost is below `π`; the concrete
octagon handles higher costs. `ReverseComparison.lean` assembles this full reverse comparison,
constructs an actual global control minimizer, and proves every control minimizer reconstructs
a geometric worst disk with `cost / √12 = minimaxDensity`.

The resulting unconditional control target is

```lean
ReinhardtConjecture ↔ ControlLowerBound
```

The inequality covers all admissible controls. It remains open. The actual geometric/control
bridge is supplied in source through G3d; the Pontryagin-lift and later reduction are G3e.

`SingularLocus.lean` identifies the general pointwise control-independent Hamiltonian
locus and confines maximizing controls to a proper simplex edge away from it.
`CircleExclusion.lean` proves entirely circular admissible trajectories cost at least `π`,
so every full minimizer has a noncircular interior state. Proper circular subarcs are
handled separately by the current hand variation, not by this whole-trajectory module.
`SingularArc.lean` proves that an actual Pontryagin extremal with zero reduced costate
on a nonempty interval has `λ < 0`, circle state, and uniform control almost everywhere
on that interval. The actual lift remains an explicit hypothesis. Combining this rigidity
with the hand variation excludes a full-control singular interval; the later Mahler First
formalization remains open.

The global lower bound and affine rigidity remain open. `ReinhardtConjecture` names minimality,
`AffineRigidity` names uniqueness after centering, and `FullReinhardtConjecture` is their
conjunction. None is asserted as an unconditional theorem.

Hales–Vajjha's [2024 book](https://arxiv.org/abs/2405.04331) proves the smoothed-polygon
reduction and leaves octagon selection open. The pinned Lean reference does not implement
all of that later reduction. A finite roadmap also does not imply a uniform finite list
of polygon cases; see [CHECKLIST.md](CHECKLIST.md).

**Source development. Compilation, typechecking, and CI have not been run.**

The hand proofs and source bodies have been reviewed. Documented symbolic exploration
helped find or check finite identities after the workflow change; the mathematical claims
rest on the displayed hand arguments. Source scans introduce no new proof holes or axioms;
this is not a kernel-verification claim.

## Files to read

| File | Purpose |
| --- | --- |
| [SmoothedOctagon/Problem.lean](SmoothedOctagon/Problem.lean) | Concrete candidate, global targets, and equivalent closure criteria |
| [SmoothedOctagon/Normalization.lean](SmoothedOctagon/Normalization.lean) | Actual-minimizer normalization, contact configurations, and area objective |
| [SmoothedOctagon/BoundaryTrace.lean](SmoothedOctagon/BoundaryTrace.lean) | Actual continuous six-contact trace and its global topology |
| [SmoothedOctagon/SupportNormal.lean](SmoothedOctagon/SupportNormal.lean) | Continuous supporting covectors without a smooth-boundary assumption |
| [SmoothedOctagon/RadialRegularity.lean](SmoothedOctagon/RadialRegularity.lean) | Supporting-slope differentiation and the regular positive radial curve |
| [SmoothedOctagon/ArcLength.lean](SmoothedOctagon/ArcLength.lean) | Constructed global Euclidean arclength parameter and its inverse |
| [SmoothedOctagon/BalancedReduction.lean](SmoothedOctagon/BalancedReduction.lean) | Actual-minimizer balanced representation and area minimization in both directions |
| [SmoothedOctagon/BalancedTargets.lean](SmoothedOctagon/BalancedTargets.lean) | Exact unrestricted area and rigidity targets equivalent to the original conjecture |
| [SmoothedOctagon/DeterminantClock.lean](SmoothedOctagon/DeterminantClock.lean) | Global contact frame, determinant-normalizing clock, and successor covariance |
| [SmoothedOctagon/ControlTrajectory.lean](SmoothedOctagon/ControlTrajectory.lean) | Measurable simplex control, curvature, and actual integral state equations |
| [SmoothedOctagon/ContactLift.lean](SmoothedOctagon/ContactLift.lean) | Constructed smooth positive contact successor with an exact sixfold period |
| [SmoothedOctagon/BalancedClock.lean](SmoothedOctagon/BalancedClock.lean) | Full balanced geometry and global derivative bounds after the clock |
| [SmoothedOctagon/CyclicClock.lean](SmoothedOctagon/CyclicClock.lean) | Uniform cyclic time, frame and state shifts, and terminal conditions |
| [SmoothedOctagon/AdmissibleRealization.lean](SmoothedOctagon/AdmissibleRealization.lean) | Actual worst-disk admissible realization with exact area and density cost |
| [SmoothedOctagon/LowCostWinding.lean](SmoothedOctagon/LowCostWinding.lean) | Cost bounds excluding extra reflected-row turns for smooth star arcs |
| [SmoothedOctagon/AdmissibleRegularity.lean](SmoothedOctagon/AdmissibleRegularity.lean) | Interval regularity and a.e. curvature from arbitrary integral trajectories |
| [SmoothedOctagon/ControlBounds.lean](SmoothedOctagon/ControlBounds.lean) | Actual cost/time bounds, high-cost competitor, and exact remaining control targets |
| [SmoothedOctagon/ReverseGeometry.lean](SmoothedOctagon/ReverseGeometry.lean) | One-turn simplicity and a constructed balanced convex disk from cyclic frame data |
| [SmoothedOctagon/CyclicExtension.lean](SmoothedOctagon/CyclicExtension.lean) | Actual global cyclic extension of arbitrary integral-admissible segments |
| [SmoothedOctagon/ReverseComparison.lean](SmoothedOctagon/ReverseComparison.lean) | Full reverse comparison, actual control minimizers, and unconditional target equivalence |
| [SmoothedOctagon/SingularLocus.lean](SmoothedOctagon/SingularLocus.lean) | General singular-control test and maximizing-control support on a proper edge |
| [SmoothedOctagon/CircleExclusion.lean](SmoothedOctagon/CircleExclusion.lean) | Entire-circle cost bound and an actual noncircle state in every full minimizer |
| [SmoothedOctagon/SingularArc.lean](SmoothedOctagon/SingularArc.lean) | Normal circle-state rigidity on a specified zero-reduced-costate interval |
| [SmoothedOctagon/SwitchingMargin.lean](SmoothedOctagon/SwitchingMargin.lean) | Exact scalar certificate and cubic margin |
| [SmoothedOctagon/StrongSwitching.lean](SmoothedOctagon/StrongSwitching.lean) | Quantitative bounds for the actual normalized switching functions |
| [docs/SWITCHING_MARGIN.md](docs/SWITCHING_MARGIN.md) | Complete hand proof of the scalar estimate |
| [docs/STRONG_SWITCHING.md](docs/STRONG_SWITCHING.md) | Complete hand proof of the switching-function transport |
| [docs/NORMALIZATION.md](docs/NORMALIZATION.md) | Construction and source dependencies for the normalized worst disk |
| [docs/BOUNDARY_TRACE.md](docs/BOUNDARY_TRACE.md) | Hand proof of the continuous contact-curve construction |
| [docs/SUPPORT_NORMAL.md](docs/SUPPORT_NORMAL.md) | Support existence, uniqueness, compactness, continuity, and gauge domination |
| [docs/RADIAL_REGULARITY.md](docs/RADIAL_REGULARITY.md) | Bilateral slope proof and exact orientation certificate |
| [docs/ARC_LENGTH.md](docs/ARC_LENGTH.md) | Integrated speed, global inverse, and exact unit-speed proof |
| [docs/BALANCED_REDUCTION.md](docs/BALANCED_REDUCTION.md) | Complete G2 assembly and the remaining global targets |
| [docs/DETERMINANT_CLOCK.md](docs/DETERMINANT_CLOCK.md) | Matrix construction, determinant speed, and clock conjugacy |
| [docs/CONTROL_TRAJECTORY.md](docs/CONTROL_TRAJECTORY.md) | Measurable repair, pointwise curvature, and absolutely-continuous FTC |
| [docs/CONTACT_LIFT.md](docs/CONTACT_LIFT.md) | Geometric successor, winding, and derived smoothness |
| [docs/BALANCED_CLOCK.md](docs/BALANCED_CLOCK.md) | Balanced-pair preservation in determinant time |
| [docs/CYCLIC_CLOCK.md](docs/CYCLIC_CLOCK.md) | Uniform contact translation and the control endpoints |
| [docs/ADMISSIBLE_REALIZATION.md](docs/ADMISSIBLE_REALIZATION.md) | Complete forward assembly and exact real area-cost conversion |
| [docs/LOW_COST_WINDING.md](docs/LOW_COST_WINDING.md) | Logarithmic angle, positive quadratic form, and the exact low-cost turn |
| [docs/ADMISSIBLE_REGULARITY.md](docs/ADMISSIBLE_REGULARITY.md) | Compact control bounds, interval FTC, endpoint regularity, and curvature |
| [docs/CONTROL_BOUNDS.md](docs/CONTROL_BOUNDS.md) | Cost regimes and the explicit reverse-comparison boundary |
| [docs/REVERSE_GEOMETRY.md](docs/REVERSE_GEOMETRY.md) | Determinant winding obstruction and convex radial-hull reconstruction |
| [docs/CYCLIC_EXTENSION.md](docs/CYCLIC_EXTENSION.md) | Seam regularity, global Lipschitz bounds, a.e. transport, and cost preservation |
| [docs/REVERSE_COMPARISON.md](docs/REVERSE_COMPARISON.md) | Complete geometric/control correspondence and the remaining global inequality |
| [docs/SINGULAR_LOCUS.md](docs/SINGULAR_LOCUS.md) | Weighted Hamiltonian identities and the exact control-independent locus |
| [docs/CIRCLE_EXCLUSION.md](docs/CIRCLE_EXCLUSION.md) | Exact circular cost, unit angular speed, and whole-trajectory exclusion |
| [docs/SINGULAR_ARC.md](docs/SINGULAR_ARC.md) | Integral costate regularity, multiplier normality, and circle-state rigidity |
| [docs/PONTRYAGIN_LIFT.md](docs/PONTRYAGIN_LIFT.md) | Exact open lift interface, free-time endpoints, and reduced nontriviality audit |
| [docs/NEAR_CIRCLE_BOUND.md](docs/NEAR_CIRCLE_BOUND.md) | Hand comparison excluding trajectories confined to an explicit circle-state neighborhood |
| [docs/SWITCHING_WORDS.md](docs/SWITCHING_WORDS.md) | Exact endpoint obstruction for every control confined to a fixed simplex edge |
| [docs/CIRCLE_VARIATION.md](docs/CIRCLE_VARIATION.md) | Complete hand construction of a lower-density competitor from a proper circle-state subarc |
| [docs/FOUR_LINK_HAND_PROOF.md](docs/FOUR_LINK_HAND_PROOF.md) | Complete asymmetric four-piece comparison and equality within that class |
| [docs/FIVE_ARC_PROGRESS.md](docs/FIVE_ARC_PROGRESS.md) | Complete five-piece word coverage and strict asymmetric comparison for the `01020` orbit |
| [docs/REVERSE_FIVE_ARC.md](docs/REVERSE_FIVE_ARC.md) | Complete asymmetric reverse-five comparison, with a uniform bound above the circle |
| [docs/REVERSE_FIVE_MINIMUM.md](docs/REVERSE_FIVE_MINIMUM.md) | Exact global minimum within the reverse five-arc family and its unique symmetric equality case |
| [docs/SIX_ARC_010202.md](docs/SIX_ARC_010202.md) | Full asymmetric six-arc `010202` comparison, sharp octagon limit, and remaining six-arc classes |
| [docs/VERTEX_WORD_REDUCTION.md](docs/VERTEX_WORD_REDUCTION.md) | Cyclic word exclusions and exact arbitrary-word dynamics, feasibility, and cost |
| [docs/GLOBAL_CALIBRATION.md](docs/GLOBAL_CALIBRATION.md) | Exact failures of simpler global bounds and the remaining coupled certificate problem |
| [docs/WORD_HOLONOMY.md](docs/WORD_HOLONOMY.md) | Complete arbitrary-word endpoint test, initial-state uniqueness, and central exceptions |
| [docs/EDGE_SWITCH_BOUND.md](docs/EDGE_SWITCH_BOUND.md) | Strict local improvement excluding five alternating edge arcs from every minimizer |
| [docs/FORWARD_ALTERNATION_EXCLUSION.md](docs/FORWARD_ALTERNATION_EXCLUSION.md) | Strict improvement for every forward four-arc alternation, including stationary endpoint fibers |
| [docs/LOCAL_SHORTENING_OBSTRUCTION.md](docs/LOCAL_SHORTENING_OBSTRUCTION.md) | Exact obstruction to deleting a positive three-arc backtrack while fixing both endpoint pairs |
| [CHECKLIST.md](CHECKLIST.md) | Finite list of global obligations and the next bounded task |
| [SOURCE_MAP.md](SOURCE_MAP.md) | Sources, reused results, and declaration map |
| [DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md) | Dependency checks, source scans, and deferred kernel validation |

## Dependencies

Dependencies are pinned to `lean4-smoothed-polygon` commit
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f` and its resolved mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`, with Lean `v4.36.0-rc2`.
Access to the private reference repository is needed to resolve the dependency.
The transitive lock records come from upstream's resolved manifest; Lake resolution has not
been rerun for this initial draft. The root imports implementation modules and excludes the
upstream `Challenge` stubs. See [CREDITS.md](CREDITS.md) for attribution.
