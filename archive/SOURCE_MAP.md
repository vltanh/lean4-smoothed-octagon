# Source map for the completed hand proof

The [final theorem](notes/HAND_COST_EQUALITY_THEOREM.md) is the main
statement. [Accepted status](notes/HAND_PROOF_STATUS.md),
[finite gate record](notes/HAND_ONLY_COMPLETION_PLAN.md), and
[active reading map](notes/ACTIVE_MAP.md) identify the current proof.
All hand gates are closed under the theorem's explicit external premises.

## Global dependency map

| Stage | Primary hand sources | Review or scope record |
|---|---|---|
| Geometric realization and comparison with arbitrary measurable controls | [Realization](notes/ADMISSIBLE_REALIZATION.md), [reverse comparison](notes/REVERSE_COMPARISON.md), [winding](notes/LOW_COST_WINDING.md), [geometry](notes/REVERSE_GEOMETRY.md) | [Final global review, Section 1](notes/HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md) |
| Uniform strict-star margins | [Compact-domain source audit](notes/COMPACT_DOMAIN_SOURCE_AUDIT.md) | [Final dependency audit](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md) |
| Free-initial-state, twisted global PMP | [Global periodic PMP](notes/GLOBAL_PERIODIC_PMP.md) | [Finite-period review](notes/HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md) |
| Finiteness before normality | [Singular budget](notes/SINGULAR_COST_BUDGET.md), [measurable-edge theorem](notes/MEASURABLE_EDGE_PMP_BOUND.md), [switch bound](notes/QUANTITATIVE_REGULAR_SWITCH_BOUND.md), [normality](notes/GLOBAL_NORMALITY.md) | [Finite-period review](notes/HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md) |
| Reverse periods and mixed reverse-run structure | [Reverse exclusion](notes/GLOBAL_REVERSE_PERIOD_EXCLUSION.md), [minimum structure](notes/MIXED_GLOBAL_MINIMUM_STRUCTURE.md), [small-forward-minimum hand proof](notes/SMALL_FORWARD_MINIMUM_HAND_PROOF.md) | [Final dependency audit](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md) |
| H-F: all-forward periods | [Forward hand theorem](notes/HAND_FORWARD_PERIOD_EXCLUSION.md) | [Norm review](notes/HAND_FORWARD_NORM_AUDIT.md) |
| H-N: smaller-nonshort, next actual switch forward | [Forward hand exclusion](notes/MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md) | [Forward review](notes/MIXED_NONSHORT_FORWARD_HAND_AUDIT.md) |
| H-N: smaller-nonshort, next actual switch reverse | [Reverse hand exclusion](notes/MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md) | [Reverse review](notes/MIXED_NONSHORT_REVERSE_HAND_AUDIT.md) |
| H-S: smaller-short actual period | [Short hand period theorem](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md) | [Period review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md), [scope review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md) |
| Direct terminal coverage and analytic costs | [Terminal hand count](notes/HAND_TERMINAL_COVERAGE.md), [terminal costs, Sections 2--3](notes/SMALL_PERIOD_COST_EQUALITY_AUDIT.md) | [Final global review, Sections 2--3](notes/HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md) |
| Unrestricted inequality and affine equality of the original disk | [Final theorem](notes/HAND_COST_EQUALITY_THEOREM.md) | [Global dependency audit](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md), [finite-period review](notes/HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md), [final equality review](notes/HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md) |

## Complete smaller-short hand chain

Every row refers to the actual competitive period and its common
covector unless a scalar comparison is explicitly stated.

| Gate | Conclusion | Primary proof and separate review |
|---|---|---|
| S0 | \(x<12/5,\ D>0,\ E_L>0\) | [Large ratio](notes/MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md), [positive pairing](notes/MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md), [interface review](notes/MIXED_SMALLER_SHORT_LARGE_RATIO_INTERFACE_AUDIT.md) |
| S1 | \(x>2\) | [Lower ratio](notes/MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md), [review](notes/MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_AUDIT.md) |
| S2 | \(x<13/6\) | [Sharp upper ratio](notes/MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md), [review](notes/MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_AUDIT.md) |
| S3 | \(0\le\delta=\beta/x-1<1/19\) | [Displacement exclusion](notes/MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md), [face review](notes/MIXED_SMALLER_SHORT_DISPLACEMENT_FACE_AUDIT.md) |
| S4 | \(\alpha\le1+3\delta,\ \Gamma_{\rm actual}>1829/10000\) on the full required interval | [Upper order](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md), [extended floor](notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md), [six derivative signs](notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md), [review](notes/MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md) |
| S5 | The actual descending root gives \(h<0,\ -hR>5A/2\) | [Root-to-shear theorem](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md), [review](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR_AUDIT.md) |
| S6 | The original period has \(C_{\rm period}>A_{\rm oct}\) | [Physical-cost theorem](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md), [review](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_AUDIT.md) |
| S7 | H-S is excluded uniformly | [Whole-period theorem](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md), [period review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md), [scope review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md) |

S1's [sharp corrected cap](notes/MIXED_SMALLER_SHORT_SHARP_LOW_RATIO_CORRECTED_CAP.md),
[central face](notes/MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md) and
[outer faces](notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md) print
the complete finite polynomial identities used in their signs.
The [lower-order theorem](notes/MIXED_SMALLER_SHORT_STRONG_ORDER.md)
and S4 give \(13/5\le\eta\le3\) in \(\alpha=1+\eta\delta\).
At \(\delta=0\), \(\alpha=1\), and no division by displacement is needed.

The new S4 signs cover \(2\le x\le13/6\), including the former gap
beyond \(15/7\). They replace the older extracted coefficient groups.
S5 and S6 are applied only after their hypotheses are established.
The [finite acceptance record](notes/HAND_ONLY_COMPLETION_PLAN.md)
gives the exact dependency order.

## External premises and historical material

Section 7 of the [final theorem](notes/HAND_COST_EQUALITY_THEOREM.md)
identifies the classical existence, balanced normalization,
critical-hexagon density, earlier geometric area and maximum-principle
inputs. The later published numerical basin and finite bang-bang results
are not inputs. The final reviews distinguish these premises from the
repository's hand deductions.

The completed hand route does not require an executable cover,
unexplained coefficient minimum or terminal word generator. When a
historical note contains both retained hand identities and later
computer-assisted work, its precise retained sections are listed in
[the active map](notes/ACTIVE_MAP.md) and
[global dependency audit](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md).

The earlier [computational global theorem](notes/GLOBAL_COST_EQUALITY_ASSEMBLY.md),
[dependency audit](notes/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md),
[certificate replay guide](notes/CERTIFICATE_REPLAY.md) and
[legacy index](notes/legacy/INDEX.md) preserve the original arithmetic
records and rejected approaches. Earlier progress maps remain in
repository history and [legacy snapshots](notes/legacy/snapshots/SOURCE_MAP.md).

All reviews are internal mathematical reviews. No external peer review,
Lean kernel certificate, Lean compilation, Lake, typechecking or CI is
claimed. Formalization files and dependency pins are unchanged.
