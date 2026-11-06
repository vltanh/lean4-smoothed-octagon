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
