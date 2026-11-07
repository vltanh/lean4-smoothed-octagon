# Current theorem source map

Read the **[authoritative handoff](docs/HANDOFF.md)** before following any historical cross-reference. The pre-reorganization long source map is preserved in [legacy snapshots](docs/legacy/snapshots/SOURCE_MAP.md).

**Active work:** the user now requests a proof without computer assistance.
[HAND_PROOF_STATUS](docs/HAND_PROOF_STATUS.md) records the open hand-only
replacement gates; [HAND_PROOF_REFINEMENTS](docs/HAND_PROOF_REFINEMENTS.md)
contains the new analytic bounds. The table below maps the completed
computer-assisted baseline and does not assert hand-only completion.

The [nonshort gap](docs/MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md) replaces the
old corner calculation. [Forward lemmas](docs/HAND_FORWARD_LEMMAS.md)
and the [short-side envelope](docs/MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md)
are accepted conditional reductions. Their
[hand review](docs/HAND_REDUCTION_REVIEW.md) identifies the exact remaining
sign arguments and removes the optional both-sides-short theorem from
the proposed dependency chain.

The next analytic reductions are [shape monotonicity](docs/MIXED_NONSHORT_SHAPE_MONOTONICITY.md),
[reverse weighted-secant concavity](docs/MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md),
and the [short-side root/angle comparison](docs/MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
Their linked hand audits accept the reductions; the resulting endpoint
exclusions are not claimed proved.

The [small-forward-minimum hand replacement](docs/SMALL_FORWARD_MINIMUM_HAND_PROOF.md),
its [cubic sign proof](docs/HAND_H5_INTEGRAL_RATIONAL_BOUND.md), and
[independent audit](docs/SMALL_FORWARD_MINIMUM_HAND_AUDIT.md) remove the
large H5 coefficient table from the shared minimum-structure dependency.

The [nonshort hand ratio exclusion](docs/MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md)
and [scale bound](docs/MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md) establish
t<2/5 and a<4/5; their [audit](docs/NONSHORT_HAND_SCALE_AUDIT.md) also
accepts the [retained central cap](docs/MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md).
The [explicit turn floor](docs/EXPLICIT_TURN_NORM_FLOOR.md),
[short nonpositive-floor lemma](docs/MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md),
and [exact forward targets](docs/HAND_FORWARD_OPEN_TARGET.md) have their
[own review](docs/HAND_FURTHER_REFINEMENTS_AUDIT.md).

The hand neighbor theorem consists of the
[symmetric integral proof](docs/HAND_FORWARD_NEIGHBOR_INTEGRAL.md),
[asymmetric completion](docs/HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md), and
[audit](docs/HAND_FORWARD_NEIGHBOR_AUDIT.md). F is now closed by the
[complete hand theorem](docs/HAND_FORWARD_PERIOD_EXCLUSION.md), using
the [two-norm criterion](docs/HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md),
[sum initial/low-D proof](docs/HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md),
[high-D completion](docs/HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md), and
[larger-norm proof](docs/HAND_FORWARD_LARGER_NORM_HAND_PROOF.md).
Their [scalar audit](docs/HAND_FORWARD_NORM_AUDIT.md) records the
independent checks; neither forward interval cover is used.

Further mixed reductions are the [single reverse shape endpoint](docs/MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON.md),
[short shear/cost candidates](docs/MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md),
and [short floor endpoints](docs/MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md),
accepted with their explicit remaining signs in the
[endpoint review](docs/HAND_ENDPOINT_REDUCTIONS_AUDIT.md).
The separate opposite-floor face is now excluded by hand. Reverse
refinements retain the [exact secant](docs/MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON.md)
and the [actual-floor order constraint](docs/MIXED_NONSHORT_REVERSE_ORDER_BOUND.md).


The [reverse order face](docs/MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md)
is now excluded by a complete hand proof, including ties. The
[unit-shape face](docs/MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md)
is also excluded, with its
[independent audit](docs/MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md).
Only the scale lower face remains in that reverse partition. The same
unit theorem closes the d<=c part of the common low-scale problem. The
[fixed outer-norm comparison](docs/MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
reduces the nonnegative-pairing part of the short w=3/4 face to further
endpoints, retaining the actual outgoing norm floor in its cost score.
The negative-pairing part and the terminal signs remain open.


Both actual stationary-control slacks also survive the first short
root comparison, by their explicit positive derivatives in
[MIXED_SMALLER_SHORT_SLACK_RETENTION](docs/MIXED_SMALLER_SHORT_SLACK_RETENTION.md).
All three terminal faces may therefore retain them. On w=3/4 the
middle slack has a short quadratic-in-scale expression. Its retention
during the further pairing deformation is conditional on J>=0, or
requires an additional zero-slack stop; no uniform sign is presumed.


For the common region a<=1/2, the
[low-scale domain bounds](docs/MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION.md)
give t<7/20 and x>3/13 without any successor or Casimir premise.
The [forward scale-Casimir reduction](docs/MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md)
writes the boundary determinant as a concave quadratic in squared
physical scale. A compact eligible-set argument retains the stronger
outgoing norm floor and reduces the lower endpoint to shape boundary
faces or the existing stronger upper endpoint. Their final signs remain
open; these are hand reductions, not completed exclusions.

| Scope | Active sources |
| --- | --- |
| Geometric/control correspondence, twisted PMP | [ADMISSIBLE_REALIZATION](docs/ADMISSIBLE_REALIZATION.md), [REVERSE_COMPARISON](docs/REVERSE_COMPARISON.md), [GLOBAL_PERIODIC_PMP](docs/GLOBAL_PERIODIC_PMP.md), [final dependency review](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) |
| Common compact state domain and all-control margins | [COMPACT_DOMAIN_SOURCE_AUDIT](docs/COMPACT_DOMAIN_SOURCE_AUDIT.md), [GLOBAL_MINIMIZER_COMPACTNESS](docs/GLOBAL_MINIMIZER_COMPACTNESS.md) |
| Sufficient whole-period sign coverage | [GLOBAL_COST_EQUALITY_ASSEMBLY, Section 4](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md#4-the-sufficient-complete-period-partition), [FORWARD_ALTERNATION_EXCLUSION](docs/FORWARD_ALTERNATION_EXCLUSION.md) |
| Quantitative clearance and finite representation | [SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md), [MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md), [QUANTITATIVE_REGULAR_SWITCH_BOUND](docs/QUANTITATIVE_REGULAR_SWITCH_BOUND.md) |
| Normality/switch rules | [GLOBAL_NORMALITY](docs/GLOBAL_NORMALITY.md), [NORMAL_TIE_BRANCHING](docs/NORMAL_TIE_BRANCHING.md), [NORMAL_SWITCH_RIGIDITY](docs/NORMAL_SWITCH_RIGIDITY.md) |
| Costate and whole-period Casimir | [MIXED_GLOBAL_COSTATE_ELLIPTIC](docs/MIXED_GLOBAL_COSTATE_ELLIPTIC.md), [GLOBAL_SPECTRAL_COST_CASIMIR](docs/GLOBAL_SPECTRAL_COST_CASIMIR.md), [GLOBAL_ENDPOINT_DEFECT_TEST](docs/GLOBAL_ENDPOINT_DEFECT_TEST.md) |
| R closed | [GLOBAL_REVERSE_PERIOD_EXCLUSION](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| M3 closed | [MIXED_GLOBAL_MINIMUM_STRUCTURE](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md) |
| Sufficient M1 closed | [MIXED_GLOBAL_SHORT_RUN_PERIOD](docs/MIXED_GLOBAL_SHORT_RUN_PERIOD.md), [MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](docs/MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) |
| F closed | [GLOBAL_FORWARD_PERIOD_EXCLUSION](docs/GLOBAL_FORWARD_PERIOD_EXCLUSION.md), [GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT](docs/GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md), [MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](docs/MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md), [GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](docs/GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md), [GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT](docs/GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT.md), [GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](docs/GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md) |
| M2 closed: whole-period implication | [MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION](docs/MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md), [independent whole-period audit](docs/MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md), [smaller-short exclusion](docs/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md) |
| M2 nonshort boundary proof | [reverse exclusion and comparison](docs/MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md), [common low-a theorem](docs/MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md), [forward concavity reduction](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md), [both endpoint exclusions](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md) |
| M2 nonshort source and record acceptance | [reverse audit](docs/MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md), [low-a audit](docs/MIXED_NONSHORT_LOW_A_BOUNDARY_AUDIT.md), [forward audit](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md), [four-record verifier](explorations/mixed_nonshort_boundary_records_verify.py) |
| Actual constrained cost Hessian | [MIXED_GLOBAL_AUGMENTED_INDEX](docs/MIXED_GLOBAL_AUGMENTED_INDEX.md), [MIXED_GLOBAL_SCALAR_DUAL](docs/MIXED_GLOBAL_SCALAR_DUAL.md) |
| Terminal cost/equality and global assembly closed | [GLOBAL_COST_EQUALITY_ASSEMBLY](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md), [SMALL_PERIOD_COST_EQUALITY_AUDIT](docs/SMALL_PERIOD_COST_EQUALITY_AUDIT.md) |

**Current verification is complete:** the [same-covector continuation interface](docs/MIXED_SMALLER_TURN_CONTINUATION.md), [boundary source/domain audits](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md), complete original/fresh replay records and [whole-period audit](docs/MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) close M2. [CERTIFICATE_REPLAY](docs/CERTIFICATE_REPLAY.md) gives all current commands. The old [three-root chain method](docs/EXACT_COVER_CHAIN.md) remains a superseded valid approach whose incomplete executions are not proof premises. Historical diagnostics are in [explorations/legacy](explorations/legacy/README.md).

Companion _AUDIT notes and exact certificate scripts remain available. Superseded plans, local comparisons, rejected shortcuts and weaker reduction estimates are [legacy](docs/legacy/INDEX.md); their old paths remain short pointers to preserve inbound links. Lean sources and dependency pins are unchanged.

The [certificate replay guide](docs/CERTIFICATE_REPLAY.md) gives the
current arithmetic commands and full-cover acceptance conditions. The
final assembly begins with an actual geometric minimizer, obtains a
finite representation before normalizing its PMP lift, and then applies
the sufficient whole-period partition. Historical finite-window and
numerical basin plans are not additional premises of this route.

## Current cost and continuation refinement

[GLOBAL_SPECTRAL_COST_CASIMIR](docs/GLOBAL_SPECTRAL_COST_CASIMIR.md) strengthens the whole-period bound and classifies equality. [GLOBAL_ENDPOINT_DEFECT_TEST](docs/GLOBAL_ENDPOINT_DEFECT_TEST.md) removes the conjugator from the exact window-angle calculation. These are internally audited hand results; F is closed by the exact minimum-domain obstruction; M2 is closed by the subsequent smaller-turn and boundary endpoint exclusions.

## Forward minimum refinement

[GLOBAL_FORWARD_LINEAR_BUDGET](docs/GLOBAL_FORWARD_LINEAR_BUDGET.md), [GLOBAL_FORWARD_NEIGHBOR_CONTRACTION](docs/GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md), and [GLOBAL_FORWARD_CENTERED_SYSTEM](docs/GLOBAL_FORWARD_CENTERED_SYSTEM.md) reduce the remaining pure-forward minimum domain. The linear polynomial certificate, the 8,183-node exact rational neighbor certificate, and the centered identities have independent internal checks. The complementary Casimir exclusion is now complete: 20,999 exact nodes, 10,501 excluded leaves, zero unresolved boxes. Its theorem and independent audit are linked in the F row above.

## Mixed-minimum continuation interfaces

The [short-bridge endpoint formulas](docs/MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md), [six-variable necessary domain](docs/MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md), and [nonshort next-switch alternative](docs/MIXED_SMALLER_TURN_CONTINUATION.md) have a joint [independent interface audit](docs/MIXED_MINIMUM_CONTINUATION_INTERFACE_AUDIT.md). The [radial completion bound](docs/GLOBAL_RADIAL_COMPLETION_BOUND.md) strengthens the cost needed outside a selected window. The [smaller-short exclusion is now complete](docs/MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md); both smaller-nonshort successor alternatives are closed by the boundary theorems listed above.

The [directed interval engine](docs/INTERVAL_ARITHMETIC_ENGINE.md) and smaller-short caller have an [independent completion audit](docs/MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md). Its full cover discharged 53,989 leaves in 107,977 nodes, with zero unresolved boxes. The separate 116,914 engine checks are implementation regression evidence; the completed full cover and mathematical interface supply the branch exclusion.

For the nonshort branch, the [regular five-variable charts](docs/MIXED_NONSHORT_BLOWUP_REDUCTION.md) and [uniform small-parameter exclusion](docs/MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md) have exact coefficient checks and a [caller/domain audit](docs/MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md). The later boundary comparison replaces the original three-root task with four completed two-root exclusions, including the branch-independent low-a reduction. Their original and independent replay records are accepted. The [final dependency review](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) closes the global cost and equality chain.
