# Lean 4 research toward the Reinhardt conjecture

This project starts from the concrete smoothed octagon in
[`vltanh/lean4-smoothed-polygon`](https://github.com/vltanh/lean4-smoothed-polygon)
and targets its **global minimality among all centrally symmetric convex disks**, followed
by uniqueness up to affine equivalence.

The candidate density is

\[
\delta_{\mathrm{oct}}=
\frac{8-\sqrt{32}-\log 2}{\sqrt 8-1}.
\]

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

The reverse comparison with every admissible control is still open. The forward realization
alone does not make the constructed control a global control minimizer. This comparison,
the extremal-lift bridge, and the later reduction are tracked in G3d–G3e of the ledger.

The global lower bound and affine rigidity remain open. `ReinhardtConjecture` names minimality,
`AffineRigidity` names uniqueness after centering, and `FullReinhardtConjecture` is their
conjunction. None is asserted as an unconditional theorem.

Hales–Vajjha's [2024 book](https://arxiv.org/abs/2405.04331) proves the smoothed-polygon
reduction and leaves octagon selection open. The pinned Lean reference does not implement
all of that later reduction. A finite roadmap also does not imply a uniform finite list
of polygon cases; see [CHECKLIST.md](CHECKLIST.md).

**Source development. Compilation, typechecking, and CI have not been run.**

The hand proofs and source bodies have been reviewed. No numerical search or external
computation was used to establish the new inequalities. Source scans introduce no new
proof holes or axioms; this is not a kernel-verification claim.

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
