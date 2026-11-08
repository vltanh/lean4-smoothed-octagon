# Active map of the completed hand proof

Date: 2026-11-08 UTC. **H-F, both H-N successors, H-S and H-A are
closed under the declared external mathematical inputs.** The
[final theorem](HAND_COST_EQUALITY_THEOREM.md) is the entry point.
The [status](HAND_PROOF_STATUS.md) and
[finite acceptance record](HAND_ONLY_COMPLETION_PLAN.md) are authoritative.

For a separate, still-open attempt to replace large-coefficient sign
arguments with short analytic bounds, see the
[small-coefficient refactor record](HAND_COEFFICIENT_REFACTOR.md).
It does not change the accepted proof or delete a certificate.

## 1. Global theorem and final reviews

Read [HAND_COST_EQUALITY_THEOREM](HAND_COST_EQUALITY_THEOREM.md) alongside:

- [Global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md).
- [Finite-before-normal and whole-period review](HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md).
- [Unrestricted inequality and original-disk equality review](HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md).

These notes specify the original integral admissible class, the retained
geometric minimizer, the same PMP lift, the complete period split and
the equality disk that is carried through the argument.

## 2. Foundations, in dependency order

| Step | Hand source |
|---|---|
| Realize a geometric worst disk and compare it with every measurable competitor | [Admissible realization](ADMISSIBLE_REALIZATION.md), [reverse comparison](REVERSE_COMPARISON.md), [low-cost winding](LOW_COST_WINDING.md), [geometric reconstruction](REVERSE_GEOMETRY.md) |
| Establish an all-control compact strict-star domain | [Compact-domain source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md) |
| Obtain the free-initial-state twisted PMP lift without normality | [Global periodic PMP](GLOBAL_PERIODIC_PMP.md) |
| Obtain singular clearance and a finite vertex representation | [Singular cost budget](SINGULAR_COST_BUDGET.md), [measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md), [regular-switch bound](QUANTITATIVE_REGULAR_SWITCH_BOUND.md) |
| Normalize the same lift after finiteness | [Global normality](GLOBAL_NORMALITY.md) |
| Locate a mixed global minimum at a reverse centre | [Minimum structure](MIXED_GLOBAL_MINIMUM_STRUCTURE.md), [small-forward-minimum hand proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md) |

The large finite switch bound selects a finite minimizing representation.
It is not an instruction to enumerate lengths. The earlier geometric
area theorem is an external premise; later numerical basin and published
finite bang-bang results are not.

## 3. Uniform period exclusions

Apply these exclusions to an eligible competitive finite normal
minimizing period with \(N\ge6\) positive pieces.

Entirely reverse periods are excluded by
[GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md).
Entirely forward periods with at least six positive pieces are excluded
by [HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md)
and its [norm review](HAND_FORWARD_NORM_AUDIT.md).

For a mixed period, choose the smaller adjacent turn at a global reverse
minimum. The actual alternatives are:

1. A short forward run:
   [H-S theorem](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md),
   [period review](MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md), and
   [scope review](MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md).
2. A nonshort run with next actual switch forward:
   [H-N forward theorem](MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md)
   and [review](MIXED_NONSHORT_FORWARD_HAND_AUDIT.md).
3. A nonshort run with next actual switch reverse:
   [H-N reverse theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
   and [review](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md).

The [actual continuation interface](MIXED_SMALLER_TURN_CONTINUATION.md)
justifies the last two choices. Equal turns, unequal positive factors
and seam crossings remain in scope. The short choice includes periods
whose forward runs are all short.

For the complete S0--S7 chain, use the
[finite acceptance record](HAND_ONLY_COMPLETION_PLAN.md). Its key new
bounds are \(2<x<13/6\), \(0\le\delta<1/19\),
\(13/5\le\eta\le3\), and
\(\Gamma_{\rm actual}>1829/10000\) on the entire required strip.
The actual root gives the physical shear, and the completion score
contradicts the original whole-period budget.

## 4. Terminal count and equality

The [direct terminal count](HAND_TERMINAL_COVERAGE.md) uses the twisted
label congruence to reduce \(N\le5\) to \(0120\) and \(01020\).
Sections 2--3 of
[SMALL_PERIOD_COST_EQUALITY_AUDIT](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
supply the analytic cost comparisons for arbitrary positive factors.

Sections 2 and 6 of the [final theorem](HAND_COST_EQUALITY_THEOREM.md)
then give the inequality for every original competitor and transport
the equality state, frame and full boundary back to the original disk.
The [final equality review](HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md)
checks this implication separately.

## 5. Exact scope of retained historical notes

Some earlier notes contain both useful hand identities and later
computational completions. Their retained scope is explicit:

- [Smaller-short six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md):
  Sections 1--5 supply the actual interface. Its later directed cover
  is historical.
- [Small-shape Casimir floor](MIXED_SMALLER_SHORT_SMALL_SHAPE_CASIMIR_FLOOR.md):
  only the analytic reductions in Sections 1--3 are retained. The
  [extended floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md) and
  [six-sign proof](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
  replace the old coefficient-group signs on the full interval.
- [Terminal audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md):
  the analytic comparisons in Sections 2--3 are retained. The direct
  terminal count replaces its historical word enumeration.
- The older nonshort boundary covers and sufficient all-short assignment
  are not required by the current direct smaller-turn partition.

The [historical computational theorem](GLOBAL_COST_EQUALITY_ASSEMBLY.md),
[baseline dependency audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md),
[replay guide](CERTIFICATE_REPLAY.md), and [legacy index](legacy/INDEX.md)
preserve the earlier evidence. They do not add executable premises to
the hand route. [SOURCE_MAP](../SOURCE_MAP.md) provides the compact
dependency index.

Internal mathematical acceptance is not external peer review or kernel
verification. Existing Lean sources and dependency pins remain intact;
no Lean, Lake, typechecking or CI was run.
