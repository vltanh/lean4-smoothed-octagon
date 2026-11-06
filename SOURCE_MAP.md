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

Every theorem above has a source proof body. The new Lean files have **not** been compiled.
See [DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md) for source scans, dependency scope,
and the checks that remain deferred.
