# Mathematical and declaration map

## Fixed sources

1. Hales and Vajjha, [*Packings of Smoothed Polygons*, arXiv:2405.04331v1](https://arxiv.org/html/2405.04331v1).
   Sections 2.1–2.4 define the problem and normalization; Section 7.5 supplies the candidate
   family and the scalar switching expression. The abstract and Appendix B.4 distinguish
   Mahler First, octagon selection, and the absent uniform edge bound.
2. [`lean4-smoothed-polygon` at `8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`](https://github.com/vltanh/lean4-smoothed-polygon/tree/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f).
   This is the actual imported Lean source, not a floating reference to `main`.
3. [mathlib at `9d581dfff2e41de989072ea63abf3daf69311520`](https://github.com/leanprover-community/mathlib4/tree/9d581dfff2e41de989072ea63abf3daf69311520).
   This is the reference project's resolved mathlib revision.

## Existing results reused

All names in this table belong to namespace `SmoothedPolygons`.

| Input | Upstream file | Role here |
| --- | --- | --- |
| `IsCCSDisk`, `greatestPackingDensity`, `IsBalancedPair` | `SmoothedPolygons/Defs.lean` | Concrete geometric comparison class and packing density |
| `minimaxDensity`, `IsWorstDisk`, `ch2_isWorstDisk_iff` | `SmoothedPolygons/Ch2/Density.lean` | Global minimax problem and lower-bound criterion |
| `theorem2_1_3`, `ch2_isWorstLatticeDisk_iff_isWorstDisk` | `SmoothedPolygons/Ch2/Density.lean` | Lattice versus congruent-copy packing bridge |
| `rein_exists_worst` | `SmoothedPolygons/Ch2/Reinhardt.lean` | Nonvacuous existence of a worst disk |
| `greatestPackingDensity_of_isBalancedPair` | `SmoothedPolygons/Ch2/BalancedDensity.lean` | Area-to-density conversion with the fixed `√12` denominator |
| `smoothedPolygonDisk`, `smoothedPolygonDisk_isBalancedPair`, `smoothedOctagon_volume` | `SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean` | Actual octagon, admissibility, and exact density |
| `hmaxF`, `chi32_eq`, `chi31_eq_chi32` | `SmoothedPolygons/Ch7/StrongTransversality.lean` | Existing scalar expression and its actual switching-function interpretation |
| `hmaxF_nonneg`, `hmaxF_pos` | `SmoothedPolygons/Ch7/HMaxInequality.lean` | Existing qualitative result, strengthened by the new margin |
| `hmax_y_mem`, `hmax_W_mem` | `SmoothedPolygons/Ch7/HMax.lean` | Domain bounds for the explicit strong-lift arcs |

The last two rows are not global classification or switch-count theorems. The regular
candidate family and arbitrary smoothed polygons remain different comparison classes.

## New global interface: `SmoothedOctagon/Problem.lean`

All new names belong to namespace `SmoothedOctagon`.

| Declaration | Exact status / content |
| --- | --- |
| `octagon`, `octagonDensity` | Definitions referencing the existing body and its candidate value |
| `ReinhardtConjecture` | Open minimality proposition |
| `AffineRigidity` | Open uniqueness proposition for centered affine images |
| `FullReinhardtConjecture` | Conjunction of the two open targets |
| `octagon_isBalancedPair`, `octagon_isCCSDisk`, `octagon_density` | Wrappers around the concrete upstream results |
| `reinhardtConjecture_iff_density_lower_bound` | Equivalence to a lower bound for every centrally symmetric convex disk |
| `reinhardtConjecture_iff_minimax` | Equivalence to the exact minimax value |
| `minimaxDensity_le_octagonDensity` | Upper bound provided by the admissible candidate |
| `exists_worst_disk` | Existing worst-disk theorem transported to the chosen density convention |
| `reinhardtConjecture_of_worst_disk` | A lower bound on one actual worst disk suffices |
| `reinhardtConjecture_iff_worst_disk_lower_bound` | Equivalent minimizer-only comparison, with existence used in the reverse direction |

These proofs use the already formalized candidate and existence facts. They do not prove
the required new global lower bound.

## Actual-minimizer normalization: `SmoothedOctagon/Normalization.lean`

| Declaration | Mathematical content |
| --- | --- |
| `worstDisk_normalization_at` | Normalizes an actual worst disk at a prescribed boundary contact, preserving density and worst status |
| `worstDisk_normalization` | Chooses the initial contact automatically |
| `exists_normalized_worst_disk` | Nonempty class of actual worst disks in `rein_Std` position |
| `normalized_leastAreaHexagon_isMultiPoint` | Normalized determinant and midpoint identities for every critical hexagon |
| `normalized_leastAreaHexagon_area` | Critical-hexagon area `2 * √3` |
| `normalized_density_eq_area` | Greatest packing density equals area divided by `2 * √3` |
| `normalized_worstDisk_boundary_contacts` | Pointwise existence of a normalized six-contact configuration through any boundary point |

The geometric inputs are `bdy_exists_hexagon`, `rein_normalize`,
`rein_isLeastAreaHexagon_comp`, and `bdy_isWorstLatticeDisk_image`. The objective uses
`rein_glpd_eq` and `rein_volume_std`. These all come from the pinned Chapter 2 implementation.
The hand proof and exact scope are in [docs/NORMALIZATION.md](docs/NORMALIZATION.md).

## Continuous boundary trace: `SmoothedOctagon/BoundaryTrace.lean`

| Declaration | Mathematical content |
| --- | --- |
| `criticalHexagonAtAngle`, `criticalHexagonAtAngle_spec`, `criticalHexagonAtAngle_unique` | Construct the unique indexed critical hexagon whose first midpoint is the polar boundary point |
| `criticalBoundaryTrace`, `criticalBoundaryTrace_zero` | Its six moving midpoints, with curve zero equal to `rein_bd K` |
| `criticalBoundaryTrace_continuous`, `criticalBoundaryTrace_mem_frontier` | Six continuous boundary-valued curves |
| `criticalBoundaryTrace_isMultiPoint` | Constant normalized contact determinant and midpoint relations |
| `criticalBoundaryTrace_periodic` | Common full period `2π` |
| `criticalBoundaryTrace_injOn`, `criticalBoundaryTrace_image_Ico`, `criticalBoundaryTrace_range` | Simplicity and exhaustive boundary traversal on every half-open full period |
| `criticalBoundaryTrace_circleRepresentation` | Initial values equal the sixth roots of unity |
| `exists_continuous_normalized_boundary_trace` | Assemble the construction starting only with `IsWorstDisk K` and `rein_Std K` |

The inputs `rein_mem_Θ`, `rein_continuous_V`, `rein_V_unique`, `rein_unique`,
`rein_bd_inj`, and `rein_exists_bd_Ico` are in the pinned `Ch2/Reinhardt.lean`.
No regular boundary curve is assumed or asserted at this step. See
[docs/BOUNDARY_TRACE.md](docs/BOUNDARY_TRACE.md) for the hand argument.

## Continuous supports: `SmoothedOctagon/SupportNormal.lean`

| Declaration | Mathematical content |
| --- | --- |
| `planeDot`, `IsNormalizedSupport` | Coordinate pairing and level-one supporting covector predicate |
| `exists_normalizedSupport`, `normalizedSupport_unique`, `existsUnique_normalizedSupport` | Pointwise construction and uniqueness from unique support lines |
| `exists_support_coordinate_bound`, `continuous_normalizedSupport` | Uniform compact box and continuity along any continuous boundary curve |
| `normalizedSupport_le_gauge` | Domination of the gauge on the entire plane |
| `radialSupport`, `radialSupport_spec`, `radialSupport_continuous`, `radialSupport_periodic` | Concrete continuous periodic covector field along the radial boundary |
| `exists_continuous_radial_support_of_unique_support`, `exists_continuous_radial_support` | Constructed field from explicit unique support or actual worst-disk hypotheses |

The pointwise inputs are `irr_exists_normal` and `irr_eq_of_line_eq` in upstream
`Ch2/Irreducible.lean`; compactness uses mathlib's
`IsCompact.tendsto_nhds_of_unique_mapClusterPt`. The full hand proof is in
[docs/SUPPORT_NORMAL.md](docs/SUPPORT_NORMAL.md).

## Radial regularity: `SmoothedOctagon/RadialRegularity.lean`

| Declaration | Mathematical content |
| --- | --- |
| `hasDerivAt_of_continuous_supporting_family` | Bilateral slope-squeeze derivative theorem from continuous supports |
| `radialDirectionDerivative`, `hasDerivAt_rein_dir`, `det2_rein_dir_radialDirectionDerivative` | Unit direction derivative and its determinant |
| `radial_support_contact`, `hasDerivAt_radialGauge_of_support`, `radialGauge_contDiff_of_support` | Gauge contact, derivative, and `C¹` regularity |
| `rein_bd_contDiff_of_support`, `hasDerivAt_rein_bd_of_support`, `rein_bd_det2_deriv_of_support` | Radial curve regularity and the exact determinant formula |
| `rein_bd_isPositiveBoundaryParam_of_support`, `rein_bd_isPositiveBoundaryParam_of_unique_support`, `rein_bd_isPositiveBoundaryParam_of_isWorstDisk` | Positive regular parametrization, culminating in a theorem about an actual worst disk |
| `rein_bd_det2_deriv_of_unique_support`, `rein_bd_det2_deriv_of_isWorstDisk` | Orientation identity with the support field hypotheses discharged |

The calculus inputs include mathlib's `hasDerivAt_iff_tendsto_slope`, order squeeze,
and `contDiff_one_iff_deriv`, inspected at the exact pinned revision. The hand proof is in
[docs/RADIAL_REGULARITY.md](docs/RADIAL_REGULARITY.md).

## Arclength: `SmoothedOctagon/ArcLength.lean`

| Declaration | Mathematical content |
| --- | --- |
| `euclideanSpeed`, `euclideanSpeed_pos`, `euclideanSpeed_sq` | Explicit Euclidean speed, its positivity, and squared-speed identity |
| `continuous_euclideanSpeed`, `periodic_euclideanSpeed` | Continuity and inherited period of the speed |
| `exists_inverse_integral_reparam` | Construct the global `C¹` inverse of the integral of a positive periodic function |
| `exists_unitSpeed_reparam` | Construct an increasing global periodic arclength change of parameter fixing zero |

The mathlib inputs are the fundamental theorem of calculus, positive periodic integral
limits, `Continuous.surjective`, `StrictMono.orderIsoOfRightInverse`, and
`HasDerivAt.of_local_left_inverse`. All are at the pinned revision. See
[docs/ARC_LENGTH.md](docs/ARC_LENGTH.md) for the complete hand proof and exact source paths.

## Balanced reduction: `SmoothedOctagon/BalancedReduction.lean`

| Declaration | Mathematical content |
| --- | --- |
| `positiveBoundaryParam_reparam` | Positive regular boundary curves survive an increasing regular global reparametrization |
| `normalized_worstDisk_exists_balanced_circle` | Construct every balanced-pair field and circle representation from an actual normalized worst disk |
| `isBalancedCircleMinimizer_of_isWorstDisk` | A balanced representative of a worst disk minimizes balanced circle area |
| `worstDisk_balanced_normalization` | Construct a density-preserving normalized balanced circle minimizer from any actual worst disk |
| `exists_balancedCircle_worst_disk` | Nonvacuous existence of a global packing minimizer in the balanced class |
| `balancedCircleMinimizer_isWorstDisk` | Converse: every balanced circle minimizer is an actual worst disk |

The assembly applies upstream Lemmas 2.4.2, 2.4.3, 2.4.5, and 2.4.6, with their
parametrization, unit-speed, and Lipschitz inputs constructed in this project. The objective
comparison uses `greatestPackingDensity_of_isBalancedPair` and finiteness of compact area.

## Exact balanced targets: `SmoothedOctagon/BalancedTargets.lean`

| Declaration | Mathematical content |
| --- | --- |
| `BalancedAreaLowerBound`, `BalancedAffineRigidity` | Open unrestricted area and equality-classification propositions |
| `octagon_isCircleRepresentation` | Existing candidate initial-value property |
| `reinhardtConjecture_iff_balancedCircleMinimizer` | Minimality is equivalent to the concrete octagon minimizing balanced circle area |
| `reinhardtConjecture_iff_balancedAreaLowerBound` | Equivalent universal area lower bound |
| `reinhardtConjecture_iff_balancedMinimizer_area_lower_bound` | Equivalent lower bound restricted to actual balanced circle minimizers |
| `affineRigidity_iff_balancedAffineRigidity` | Equality classification transfers through inverse normalization |
| `fullReinhardtConjecture_iff_balancedTargets` | The two original targets are equivalent to the two open balanced targets |

The full assembly and target-transfer argument is in
[docs/BALANCED_REDUCTION.md](docs/BALANCED_REDUCTION.md). No theorem in these modules proves
the remaining area inequality or classifies its equality cases.

## Matrix and determinant clock: `SmoothedOctagon/DeterminantClock.lean`

| Declaration | Mathematical content |
| --- | --- |
| `contactFrame`, `contactFrame_action`, `contactFrame_unique`, `contactFrame_det` | Explicit global frame, full contact action, uniqueness, and determinant one |
| `contactFrame_initial`, `contactFrame_contDiff`, `contactFrame_hasDerivAt`, `contactFrame_periodic` | Circle initial value and global regularity/periodicity |
| `contactLogDerivative`, `contactFrame_dynamics`, `contactLogDerivative_properties` | Raw logarithmic state, its frame equation, trace, and positive star/determinant conditions |
| `continuous_contactLogDerivative`, `contactLogDerivative_periodic`, `contactLogDerivative_det` | Continuity, period, and determinant relation with the ordinary frame derivative |
| `determinantSpeed` and its positivity, square, continuity, and period lemmas | The actual clock density `sqrt(det X)` |
| `contactFrame_shift_of_contacts`, `determinantSpeed_contact_shift` | Frame and density covariance under a positive contact successor |
| `inv_sqrt_smul_isStarState`, `normalizedContactState` | Exact determinant normalization and preserved star signs |
| `balanced_exists_determinant_clock` | Construct the inverse clock, normalized star state, global Lipschitz state, and frame dynamics from a balanced pair |
| `determinantClock_conjugates_successor` | A positive sixfold successor becomes a uniform shift by `P / 6` in the constructed time |

The geometric inputs are upstream `corollary3_1_6`, `proposition3_1_9`, and matrix
derivative rules. The scalar clock is constructed by `ArcLength.lean`. See
[docs/DETERMINANT_CLOCK.md](docs/DETERMINANT_CLOCK.md).

## Forward control construction: `SmoothedOctagon/ControlTrajectory.lean`

| Declaration | Mathematical content |
| --- | --- |
| `UsableCurvatures`, `repairedCurvatureControl`, `controlVariables_mem_of_usable` | Normalize nonnegative nonzero curvature vectors and repair all other values |
| `repairedCurvatureControl_mem`, `measurable_repairedCurvatureControl` | Simplex membership everywhere and Borel measurability |
| `boundaryControl`, `measurable_stateCurvature`, `measurable_boundaryControl`, `boundaryControl_mem` | Explicit measurable control from the normalized state and its entrywise derivative |
| `boundaryControl_denominator_neg` | Strict dynamical denominator sign, including exceptional times |
| `positiveBoundary_curvature_nonneg`, `stateCurvature_nonneg_of_boundary` | Pointwise convex curvature and its almost-everywhere state version |
| `frame_velocity_lipschitz`, `lipschitzOnEntrywise_univ_of_periodic`, `frame_velocity_lipschitz_periodic` | Local velocity regularity and its global periodic extension |
| `integralCurve_of_lipschitz_ae`, `boundaryControl_eq_raw_ae` | Absolutely-continuous integral equations and agreement with raw curvature control |
| `normalized_boundary_isStateTrajectory` | Full integral trajectory from normalized boundary geometry |
| `positiveBoundaryParam_of_balanced`, `balanced_determinantClock_isStateTrajectory` | Supply actual positive boundary curves after the determinant clock |
| `balanced_exists_stateTrajectory`, `normalized_worstDisk_exists_stateTrajectory` | Construct trajectories from balanced circle data and from an actual normalized worst disk |

The dynamics inputs are upstream Lemma 3.3.1 and Theorem 3.4.2; matrix FTC and
mathlib's absolutely-continuous FTC supply the integral formulation. The exact
exceptional-set and comparison boundaries are in
[docs/CONTROL_TRAJECTORY.md](docs/CONTROL_TRAJECTORY.md).

## Actual contact successor: `SmoothedOctagon/ContactLift.lean`

| Declaration | Mathematical content |
| --- | --- |
| `successorAngle`, `successorAngle_continuous`, `successorAngle_strictMono`, `successorAngle_add_two_pi` | Actual increasing polar successor and its period drift |
| `successorAngle_bounds`, `successorAngle_twice_lt_add_pi` | One and two contacts advance by less than a half turn |
| `criticalBoundaryTrace_successor`, `criticalBoundaryTrace_successor_iterate` | The entire contact configuration shifts coherently |
| `rein_bd_add_pi_of_isCCSDisk`, `successorAngle_iterate_three`, `successorAngle_iterate_six` | Antipodal and exact full-turn identities |
| `contDiff_pos_of_positive_curve_comp` | Derive a positive `C¹` parameter change from its continuous action on positive regular curves |
| `exists_positive_cyclic_contact_lift` | Construct the positive smooth successor in the actual balanced parameter, with all six contact equations and exact sixth iterate |

The geometry uses the pinned Chapter 2 indexed uniqueness, polar-angle, and critical-hexagon
results. Smoothness uses the pinned scalar inverse-composition derivative theorem. See
[docs/CONTACT_LIFT.md](docs/CONTACT_LIFT.md).

## Balanced clock assembly: `SmoothedOctagon/BalancedClock.lean`

| Declaration | Mathematical content |
| --- | --- |
| `lipschitz_mulVec_of_entrywise` | A fixed vector converts entrywise matrix bounds into a global plane Lipschitz bound |
| `contact_derivatives_lipschitz_of_frame_velocity` | All contact derivatives inherit the velocity bound |
| `balancedPair_reparam_of_derivatives_lipschitz` | Preserve every balanced-pair clause under a positive global clock with exact period drift |
| `balancedPair_determinantClock_reparam` | Supply the derivative bound from the actual constructed determinant clock |

The proof uses periodic velocity regularity from `ControlTrajectory.lean` and the upstream
balanced curvature and star lemmas. See [docs/BALANCED_CLOCK.md](docs/BALANCED_CLOCK.md).

## Uniform cyclic time: `SmoothedOctagon/CyclicClock.lean`

| Declaration | Mathematical content |
| --- | --- |
| `state_cyclic_of_frame` | Differentiate a cyclic determinant-one frame and obtain `Y(t+T)=R⁻¹Y(t)R` |
| `balanced_exists_cyclic_determinant_clock` | Construct the positive clock, balanced circle representation, uniform contact shift, global state dynamics, and both terminal conditions from an actual worst disk |

This assembly applies the actual contact lift and determinant clock together; their
existence is not an additional premise. See [docs/CYCLIC_CLOCK.md](docs/CYCLIC_CLOCK.md).

## Exact forward realization: `SmoothedOctagon/AdmissibleRealization.lean`

| Declaration | Mathematical content |
| --- | --- |
| `cost_eq_area_of_balanced_cyclic` | Real cost equals area, using positivity before converting the upstream extended-real identity |
| `normalized_worstDisk_admissible_realization` | Construct all balanced, cyclic, control, integral, and terminal witnesses for an actual normalized worst disk |
| `worstDisk_admissible_realization` | Construct the density-preserving normalization and its complete admissible realization for an arbitrary worst disk |
| `exists_worstDisk_admissible_realization` | Supply an actual worst-disk witness and exact area-cost realization from the existing existence theorem |

The exact cost is obtained from upstream `eqn_cost`; the density uses
`greatestPackingDensity_of_isBalancedPair`. All geometry and timing inputs are constructed
in the preceding modules. See [docs/ADMISSIBLE_REALIZATION.md](docs/ADMISSIBLE_REALIZATION.md).

## Low-cost winding: `SmoothedOctagon/LowCostWinding.lean`

| Declaration | Mathematical content |
| --- | --- |
| `continuous_logDeriv_of_contDiff`, `hasDerivAt_log_of_contDiff`, `hasDerivAt_angle_of_contDiff`, `toComplex_eq_exp_log_of_contDiff` | Construct and differentiate a continuous angle for any nonvanishing `C¹` curve |
| `starRowQuadratic`, `starRowQuadratic_pos`, `starRowQuadratic_le_trace` | Positive quadratic form and the exact trace bound for a star state |
| `reflectedFirstRow` and its regularity, nonvanishing, derivative, and cross lemmas | The row adapted to right matrix dynamics |
| `reflectedFirstRow_angularSpeed_bounds`, `reflectedFirstRow_angle_strictMono`, `reflectedFirstRow_angle_le_cost` | Positive angular speed and its integrated cost bound |
| `lowCost_reflectedFirstRow_angle`, `lowCost_first_matrix_entry_pos` | Exact `π/3` endpoint angle and positive first coordinate below cost `π` |

The logarithmic proof adapts upstream `Basic/Analysis/Convex/StarCurve.lean`, removing
unused simplicity and periodicity premises. The trajectory hypotheses are explicitly
global and smooth in this module. See [docs/LOW_COST_WINDING.md](docs/LOW_COST_WINDING.md).

## Integral-trajectory regularity: `SmoothedOctagon/AdmissibleRegularity.lean`

| Declaration | Mathematical content |
| --- | --- |
| `controlCommutator`, `isCompact_controlSimplex`, `continuous_controlMatrix` | Actual state velocity and compact control parameter space |
| `continuousOn_controlCommutator`, `controlCommutator_bounded` | Joint continuity and uniform bounds along a continuous star-state segment |
| `integralCurve_lipschitz_of_bounded`, `integralCurve_ae_hasDerivAt` | Lipschitz and Lebesgue-FTC consequences of integral equations |
| `stateTrajectory_continuous`, `stateTrajectory_state_lipschitz` | Derived continuity and state Lipschitz regularity on the full closed interval |
| `stateTrajectory_frame_hasDerivWithinAt`, `stateTrajectory_frame_hasDerivAt`, `stateTrajectory_frame_contDiffOn` | Endpoint and interior frame equations and `C¹` entries |
| `stateTrajectory_state_ae_hasDerivAt`, `stateTrajectory_stateCurvature_nonneg` | Actual a.e. state dynamics and nonnegative normalized curvature |
| `sixthRoot_curvature_nonneg_of_stateCurvature`, `stateTrajectory_contactCurvature_nonneg` | All six geometric contact curvatures from the three state inequalities |
| `stateTrajectory_regularity` | Consolidated output from an arbitrary integral-form state trajectory |

The matrix FTC, upstream `oct_stateCurvature_eq`, and exact pinned mathlib Lebesgue
differentiation theorem supply the main inputs. See
[docs/ADMISSIBLE_REGULARITY.md](docs/ADMISSIBLE_REGULARITY.md).

## Cost regimes and open control targets: `SmoothedOctagon/ControlBounds.lean`

| Declaration | Mathematical content |
| --- | --- |
| `star_costDensity_ge_three`, `stateTrajectory_cost_ge_three_mul`, `stateTrajectory_cost_pos` | Pointwise cost-density bound and positive cost at least `3T` for every integral trajectory |
| `stateTrajectory_terminalTime_lt_pi_div_three` | Low cost implies `T < π/3` |
| `octagon_area_lt_pi`, `worstDisk_realization_cost_le_octagon`, `exists_worstDisk_lowCost_realization` | Concrete area threshold and a constructed actual worst realization below it |
| `AdmissibleBalancedComparison`, `LowCostBalancedComparison` | Named reverse-comparison interfaces, discharged downstream in `ReverseComparison.lean` |
| `highCost_balanced_competitor`, `admissibleBalancedComparison_iff_lowCost` | The concrete octagon discharges high costs, leaving exactly the low-cost regime |
| `controlMinimizer_of_worstDisk_realization` | Conditional full control minimality with the reverse comparison kept explicit |
| `LowCostControlLowerBound`, `reinhardtConjecture_of_lowCostControlLowerBound` | Unrestricted low-cost inequality and its sufficient connection to geometric minimality |
| `reinhardtConjecture_iff_lowCostControlLowerBound` | Conditional equivalence, explicitly assuming the reverse comparison |

The integral estimate generalizes the bound in upstream `Ch4/TerminalTime.lean`; the
strict octagon threshold is inherited from the existing exact candidate proof. See
[docs/CONTROL_BOUNDS.md](docs/CONTROL_BOUNDS.md).

## Constructed reverse geometry: `SmoothedOctagon/ReverseGeometry.lean`

| Declaration | Mathematical content |
| --- | --- |
| `frameContact`, `cyclicFrame_add_nat`, `cyclicFrame_periodic` | Actual contact curves and full cyclic frame period |
| Contact regularity, star, cross, and shift lemmas | Derive positive regular contacts and all cyclic identities from the frame |
| `angle_strictMono_of_cross_pos`, `continuous_angle_of_contDiff` | Angle properties without simplicity assumptions |
| `reflectedFirstRow_shift`, `angle_add_of_rotated_period`, `lowCost_reflectedFirstRow_full_angle` | The reflected row makes exactly one full turn |
| `firstContact_angle_ne_row_add_pi`, `lowCost_firstContact_full_angle` | Determinant obstruction and the resulting exact first-contact winding |
| `curve_injOn_of_full_angle` | Simplicity from strict angular growth and one full turn |
| `cyclicFrameDisk`, `lowCost_cyclicFrame_isBalancedPair` | Construct the convex centrally symmetric radial hull and every balanced-circle clause |

The geometric closure uses upstream `PlaneCurve.IsStarCurve.convex_radialHull` and
the radial-hull frontier, compactness, and interior results. All simplicity and curvature
inputs are supplied. See [docs/REVERSE_GEOMETRY.md](docs/REVERSE_GEOMETRY.md).

## Actual cyclic extension: `SmoothedOctagon/CyclicExtension.lean`

| Declaration | Mathematical content |
| --- | --- |
| `cyclicMatrixExtension` and its period, agreement, shift, continuity, derivative, and Lipschitz lemmas | Six twisted matrix copies and a global periodic extension with all seam regularity derived |
| `ae_of_periodic_ae_on_Ioo` | Extend a periodic a.e. property by measure-preserving translations and exclusion of the countable seam grid |
| `contactCurvature_ae_of_cyclic_shift` | All-contact curvature is periodic under the cyclic shift, including totalized derivatives |
| `cyclicFrameExtension`, `cyclicStateExtension` | Concrete frame and state extensions with the correct conjugation direction |
| `exists_cyclic_extension_of_isReinhardtAdmissible` | Supply every global analytic input from arbitrary integral admissibility and preserve the closed original segment and exact cost |

The construction reuses upstream `poly_pw` integral gluing and `oct_red`, together with
the interval regularity proved in `AdmissibleRegularity.lean`. See
[docs/CYCLIC_EXTENSION.md](docs/CYCLIC_EXTENSION.md).

## Full comparison: `SmoothedOctagon/ReverseComparison.lean`

| Declaration | Mathematical content |
| --- | --- |
| `lowCost_admissible_balanced_realization` | Construct an equal-area balanced circle disk from any low-cost integral-admissible control |
| `lowCostBalancedComparison`, `admissibleBalancedComparison` | Discharge the low-cost and full reverse-comparison interfaces |
| `normalized_worstDisk_controlMinimizer` | The actual worst disk's constructed realization minimizes over every admissible control |
| `exists_worstDisk_controlMinimizer` | Actual existence, with exact geometric cost, density, and strict cost/time bounds |
| `controlMinimizer_density_eq_minimax`, `controlMinimizer_balanced_worstDisk` | Every control minimizer has the geometric minimax value and reconstructs a worst disk |
| `ControlLowerBound`, `controlLowerBound_iff_lowCost` | The remaining unrestricted global inequality and its exact low-cost reduction |
| `reinhardtConjecture_iff_controlLowerBound` | Unconditional equivalence to original geometric minimality, with both comparison directions constructed |

This module supplies the previously separate comparison interface. It does not prove
`ControlLowerBound` or affine rigidity. See [docs/REVERSE_COMPARISON.md](docs/REVERSE_COMPARISON.md).

## Pointwise singular-control locus: `SmoothedOctagon/SingularLocus.lean`

| Declaration | Mathematical content |
| --- | --- |
| `traceForm_controlMatrix_eq_vertex_sum`, `eq_zero_of_traceForm_control_vertices_eq_zero` | Vertex-coordinate linearity and separation of traceless matrices |
| `hamiltonian_denominator_mul_eq_vertex_sum`, `hamiltonian_gap_eq_vertex_sum` | Exact weighted Hamiltonian and nonnegative-gap identities |
| `hamiltonian_le_of_vertex_le`, `hamiltonian_isMax_iff_vertexwise` | Vertexwise upper bounds and the full maximum condition |
| `maximizing_control_support` | Every positive coordinate of a maximizing control uses a maximizing vertex |
| `hamiltonian_vertices_equal_iff_reducedCostate_eq_zero`, `hamiltonian_constant_on_simplex_iff_reducedCostate_eq_zero` | General pointwise control-independence test under explicit star/perpendicularity hypotheses |
| `hamiltonian_maximizers_in_proper_edge` | A nonzero reduced costate excludes one fixed vertex from the support of every maximizer |

This implements Hales–Vajjha Lemma 8.2.1 by direct matrix and weighted-gap algebra,
using the pinned star-denominator and trace-square results. It supplies no lift-existence
or finite-switch theorem. See [docs/SINGULAR_LOCUS.md](docs/SINGULAR_LOCUS.md).

## Entire-circle exclusion: `SmoothedOctagon/CircleExclusion.lean`

| Declaration | Mathematical content |
| --- | --- |
| `reinhardtCost_eq_three_mul_of_circle` | Circle-state equality on the open interval gives exact cost `3T` |
| `reflectedFirstRow_angularSpeed_eq_one`, `reflectedFirstRow_angle_eq_terminalTime_of_circle` | Unit angular speed and its integrated angle for the explicit smooth-frame interface |
| `lowCost_admissible_not_circle`, `admissible_circle_cost_ge_pi` | Actual integral-admissible entirely circular trajectories cost at least `π` |
| `controlMinimizer_cost_lt_pi`, `controlMinimizer_not_circle`, `controlMinimizer_exists_non_circle_state` | Every full minimizer has strict low cost and an interior noncircle state |

The actual admissible extension supplies the analytic interface. This result does not
require a Pontryagin lift and does not exclude proper circular subarcs. See
[docs/CIRCLE_EXCLUSION.md](docs/CIRCLE_EXCLUSION.md).

## Singular-interval rigidity: `SmoothedOctagon/SingularArc.lean`

| Declaration | Mathematical content |
| --- | --- |
| `commuting_perpendicular_eq_zero`, `costate_eq_cost_of_zero_reduced_derivative` | Centralizer and trace-form algebra identify the first costate |
| `starState_eq_J_of_commutator_zero`, `circle_control_unique` | Star signs select the circle state; its stationary control is uniform |
| `pontryagin_costate_eq_on_zero_reducedCostate` | Upgrade integral/a.e. costate information to a pointwise first-costate identity on the open interval |
| `pontryagin_zero_reducedCostate_rigidity` | An actual extremal with zero reduced costate on a nonempty interval is normal, circular, and uniformly controlled there |
| `pontryagin_controlIndependent_interval_rigidity` | Full-simplex control independence implies the same local rigidity |
| `controlMinimizer_reducedCostate_not_identically_zero` | A full minimizer with an actual lift cannot have zero reduced costate on its entire interval |

This develops the interval argument of Hales–Vajjha Lemma 8.2.2 and Theorem 8.2.3 from
the pinned integral extremal predicate. It supplies neither lift existence nor exclusion
of proper singular subarcs. See [docs/SINGULAR_ARC.md](docs/SINGULAR_ARC.md).

## New quantitative inequality: `SmoothedOctagon/SwitchingMargin.lean`

| Declaration | Mathematical content |
| --- | --- |
| `hmaxF_margin_identity` | Exact residual identity for the original expression |
| `hmaxF_rational_lower_bound` | Full rational bound for `2 ≤ y ≤ r` |
| `hmaxF_cubic_lower_bound` | `r(r-y)³/(4(r+y)) ≤ hmaxF y r` on `2 ≤ y ≤ r ≤ 4` |
| `hmaxF_uniform_cubic_lower_bound` | `(r-y)³/8 ≤ hmaxF y r` on the same triangle |
| `hmaxF_nonneg_from_margin` | Existing sign conclusion recovered from the stronger bound |
| `hmaxF_pos_from_margin` | Strict positivity away from the diagonal |
| `hmaxF_eq_zero_iff_from_margin` | The exact diagonal zero set |

The logarithmic inputs are `Real.le_log_one_add_of_nonneg` and
`Real.log_le_sub_one_of_pos` in mathlib's `Analysis/SpecialFunctions/Log/Basic.lean`.
The remaining certificate is rational algebra with explicit denominator signs.
The full hand proof is in [docs/SWITCHING_MARGIN.md](docs/SWITCHING_MARGIN.md).

## New transport: `SmoothedOctagon/StrongSwitching.lean`

| Declaration | Mathematical content |
| --- | --- |
| `strong_chi32_cubic_lower_bound` | `χ₃₂(t) ≥ √3 t³/2` for the explicit strong lift on its full segment |
| `strong_chi31_cubic_lower_bound` | Reflected bound `χ₃₁(t) ≥ √3 (t_sw-t)³/2` |
| `normalizedStrongLift_switching_cubic_lower_bounds` | Both bounds for any `IsStrongLift` with multiplier `-1`, using upstream uniqueness |

The bridge uses `chi32_eq`, `chi31_eq_chi32`, `strongLift_unique`, `hmax_y_mem`, and
`hmax_W_mem` from the pinned source. Its elementary analytic input is
`Real.add_one_le_exp`. The hand proof and normalization restrictions are in
[docs/STRONG_SWITCHING.md](docs/STRONG_SWITCHING.md).

## Validation

[docs/WORD_HOLONOMY.md](docs/WORD_HOLONOMY.md) develops the tangent/state products used
in the four-link proof into a complete fixed-factor theorem for arbitrary finite words.
The real two-dimensional centralizer gives the exact holonomy classification; explicit
vertex flows turn prefix signs into full-arc feasibility. The central cases retain
their initial-direction cone and exact quadratic cost quotient. No general cost
comparison or word bound is inferred from this reduction.

[docs/GLOBAL_CALIBRATION.md](docs/GLOBAL_CALIBRATION.md) derives exact obstructions to
state-only, separable phase/state, and frame-only certificates. The strict-star frame
relaxation has an exact finite endpoint and a rational cost separation below the octagon;
its discontinuous state is explicitly outside actual admissibility. The three coupled
vertex residuals use the same positive margins and pinned state equations, and remain
an unsolved certificate problem. No numerical or symbolic output is used in these proofs.

[docs/VERTEX_WORD_REDUCTION.md](docs/VERTEX_WORD_REDUCTION.md) derives the exact
time-rebase permutation from the pinned `R` conjugation convention and applies the
fixed-edge hand proof in every window. Its margin updates and cost follow by direct
integration of the pinned constant-control equations. The accompanying
[exploratory script](explorations/vertex_word_algebra.py) preserves an earlier symbolic
three-arc calculation; its outputs are not premises of the hand exclusions.

[docs/FOUR_LINK_HAND_PROOF.md](docs/FOUR_LINK_HAND_PROOF.md), added in the concurrent
commit `2ea4e93`, covers all reduced four-piece vertex trajectories. Its displayed
tangent factors, shape identity, positive-margin sequence, exact cost formula, and
integral monotonicity argument form the hand certificate. The published control equations
are the input; a general link-reduction theorem is not assumed. Independent reviews
checked each stage and the strict equality case. There is no new Lean implementation.

[docs/CIRCLE_VARIATION.md](docs/CIRCLE_VARIATION.md) recovers Hales–Vajjha Theorem 8.2.7
by an explicit hyperbolic deformation with exact area deficit. The hand proof supplies
the periodic splice, compact positivity margins, winding, convexity, and the complete
balanced competitor. The pinned `eqn_cost` and balanced-density identity do not require
the raw perturbed logarithmic derivative to have determinant one. This is a known
local exclusion with quantitative details, not a new global octagon comparison or a
new Lean implementation.

[docs/SWITCHING_WORDS.md](docs/SWITCHING_WORDS.md) integrates the fixed-edge equations
in Hales–Vajjha §8.1 and the pinned half-plane conventions, including measurable-control
regularity. The initial and terminal group matrices force a forbidden boundary state.
The exact `R_conj_controlMatrix_vertex` permutation covers all three edges. This is a
hand exclusion of arbitrary measurable controls, with no new Lean declaration.

The current hand comparison in [docs/NEAR_CIRCLE_BOUND.md](docs/NEAR_CIRCLE_BOUND.md)
uses the determinant identity, the actual reflected-row angle, ordinary and integral
Cauchy–Schwarz, and the exact octagon upper bound. It proves an excluded class of
arbitrary trajectories; it has no new Lean declaration under the updated workflow.

The separate [Pontryagin-lift audit](docs/PONTRYAGIN_LIFT.md) maps the open arbitrary-
minimizer lift to the exact pinned extremal fields and distinguishes the available
coordinate transformations and explicit polygon lifts from a general existence result.

Every mapped Lean theorem has a source proof body; the later hand results are documented
separately. The new Lean files have **not** been compiled.
See [DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md) for source scans, dependency scope,
and the checks that remain deferred.
