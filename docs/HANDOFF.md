# Authoritative handoff — hand proof now in progress

**Active request (2026-11-07): find a hand proof that does not depend on computer assistance.** The finite replacement ledger is [HAND_PROOF_STATUS](HAND_PROOF_STATUS.md). New explicit inequalities are in [HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md). That goal is not yet complete: the interval exclusions below are the completed computational baseline, not hand-only premises. Preserve the baseline and replace its indispensable computational dependencies by readable arguments.

**Latest hand progress:** the [small-forward-minimum hand proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md)
replaces the hard H5 coefficient table by an integral estimate and an
elementary cubic sign argument, with an
[independent audit](SMALL_FORWARD_MINIMUM_HAND_AUDIT.md). This supplies
the shared minimum-structure prerequisite for F and the mixed cases.
The [nonshort duration-ratio gap](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md)
removes the old small-parameter coefficient table from the actual refined
route. The [forward lemmas](HAND_FORWARD_LEMMAS.md) and
[short-side outer envelope](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md) have
accepted conditional reductions with their remaining hypotheses stated.
See the [independent hand review](HAND_REDUCTION_REVIEW.md); no final
F, short-side or nonshort successor exclusion is claimed from these
refinements alone.

Further accepted hand work reduces the nonshort residual by
[shape monotonicity](MIXED_NONSHORT_SHAPE_MONOTONICITY.md) and the reverse
successor by [weighted secant concavity](MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md).
The [short-side root and angle reduction](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
preserves a relaxed necessary cost test on four boundary faces. Their
endpoint exclusions remain open; their audits do not certify those
unproved signs.

The [nonshort high-ratio exclusion](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md)
now proves t<2/5 by hand; combined with the
[scale estimate](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md), it gives
a<4/5 throughout the actual smaller-nonshort case. The
[retained central bound](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md)
and [explicit turn floor](EXPLICIT_TURN_NORM_FLOOR.md) give further
necessary restrictions. See [their audit](NONSHORT_HAND_SCALE_AUDIT.md).
The [forward target note](HAND_FORWARD_OPEN_TARGET.md) preserves the
genuine exterior floors and records exact obstructions to dropping them.

The forward neighbor bound is now complete by hand: the
[symmetric integral proof](HAND_FORWARD_NEIGHBOR_INTEGRAL.md) and
[asymmetric completion](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md)
prove both ratios below 4/3, with their
[independent audit](HAND_FORWARD_NEIGHBOR_AUDIT.md). F still needs the
stationary norm-sum or direct Casimir sign.

For the mixed cases, the [affine reverse comparison](MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON.md)
leaves one upper shape endpoint, and the
[short shear/cost formulas](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md)
list all possible scale minima. The
[short floor analysis](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
removes both the root-interval and outer-scale endpoints, leaving one
central-duration sign for the separate opposite-floor face. Their
[review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md) does not close the remaining
whole-case exclusions.

**Baseline status (2026-11-07): the hand/computer-assisted proof of the sharp Reinhardt cost inequality and affine uniqueness is COMPLETE, with independent internal review.** F, M2, G4 and G5 are closed under the declared geometric/PMP inputs and arithmetic execution trust boundary. Existing Lean drafts are not kernel-verified; no Lean compilation, Lake, typechecking or CI was run.

## 1. Exact completed statement

For

\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1},
\]

every trajectory in the original integral Reinhardt admissible class,
including measurable controls, has cost

\[
C\ge\sqrt{12}\,\delta_{\rm oct}.
\]

Every centrally symmetric planar convex disk has greatest packing
density at least \(\delta_{\rm oct}\), with equality exactly for affine
images of the concrete smoothed octagon. The [final assembly](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
proves these quantifiers and classifies the original equality disk;
its [independent dependency audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md)
records acceptance and the external premises.

## 2. Closed finite proof gates

| Gate | Accepted result |
| --- | --- |
| G1–G3 | Actual twisted PMP with free initial state; singular clearance; measurable-edge finiteness and finite representation before normality |
| R | [Entirely reverse exclusion](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| M3 | [Every surviving reverse run has exactly two switches](MIXED_GLOBAL_MINIMUM_STRUCTURE.md) |
| M1 | [Sufficient all-short mixed-period exclusion](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md), including the two-centre base |
| F1/F2 | [Uniform all-forward exclusion](GLOBAL_FORWARD_PERIOD_EXCLUSION.md) and [independent audit](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md) |
| M2.0 | [Smaller-short exclusion](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md) and nonshort [hand corner](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md) |
| M2.1-R | [Reverse-next boundary exclusion](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) and [audit](MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md) |
| M2.1-F | [Common low-a theorem](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md), [concavity reduction](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md), [forward endpoint exclusion](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md) and their independent audits |
| M2.1-V | Four frozen boundary sources/domains with complete original executions, independent fresh replays and verified two-root accounting |
| M2.2 | [Uniform whole-M2 theorem](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) and [independent audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) |
| G4 | [Sharp global cost and original-disk affine equality](GLOBAL_COST_EQUALITY_ASSEMBLY.md), using the audited through-five comparison |
| G5 | [Final dependency and scope audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) |

No hand/computer-assisted proof gate remains open. Further changes must
preserve the established interfaces and be reviewed against their stated
quantifiers. Lean formalization and external peer review are separate
activities; neither is claimed completed here.

## 3. Final M2 mechanism

The finite normal minimizing-period reduction supplies one actual
continuous covector, all twisted endpoints, a global active-margin
minimum, compact bounds and the whole-period Casimir cap. A minimum in
mixed structure is a reverse centre. Its smaller adjacent turn belongs
to a short or nonshort run, an exhaustive choice including equal turns.
The accepted smaller-short theorem excludes the first case.

For the nonshort case, fix actual `a,c,d,r,v` and solve first-forward
stationarity while increasing the scalar `b` to `b*=K/(a+c)-a`.
The root coefficient remains negative; a linear differential identity
preserves the strict incident upper-norm inequality and decreases `w`.
This comparison does not assert a deformation of a physical trajectory.

At the boundary, recompute `epsilon'=max(delta1,delta2)` with `l0=0`.
The hand corner covers `epsilon'<=1/32`; two four-variable charts cover
the complement. This covers points originally in all three charts,
including the old delta0-maximal region.

The reverse successor retains its extended secant ceiling after `w`
decreases. For the forward successor, stationarity makes the diagonal
affine in `w`, the next norm decreases affinely, and the squared Casimir
is concave. The actual `w` lies between `w*` and the endpoint where the
next norm is `3/4`, so its actual Casimir cap forces one endpoint cap.
Both enlarged endpoint domains are excluded. The common `a>1/2` theorem
uses neither successor restriction, so its use in the forward roots is
not circular.

The actual first successor is forward or reverse even across the seam.
The whole-M2 audit checks unequal factors, arbitrary run lengths,
repeated minima, weak third ties, analytic zero-duration limits and rank
defects. Short-side cost/angle estimates charge only the two actual turn
arcs, a proper subperiod for `N>=6`; extended PMP displays may wrap but
do not multiply that cost budget.

## 4. Complete arithmetic records

| Quantified domain | Roots | Nodes N | Excluded leaves L | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| F neighbor contraction | 1 | 8,183 | 4,092 | 20 |
| F complementary Casimir | 3 | 20,999 | 10,501 | 23 |
| M2 smaller-short | 1 | 107,977 | 53,989 | 37 |
| Nonshort reverse boundary | 2 | 106,134 | 53,068 | 26 |
| Common nonshort a<=1/2 boundary | 2 | 74,772 | 37,387 | 23 |
| Nonshort forward lower endpoint | 2 | 37,940 | 18,971 | 27 |
| Nonshort forward upper endpoint | 2 | 60,976 | 30,489 | 32 |

Every accepted cover has an empty final frontier, zero unresolved boxes,
and `N=2L-roots`. The four new boundary covers each have separate fresh
replays agreeing with the original mathematical counts. Their full logs,
source/header hashes, domains and commands are in the published JSON
receipts. The [replay guide](CERTIFICATE_REPLAY.md) supplies all commands.
The portable record check is:

```sh
python explorations/mixed_nonshort_boundary_records_verify.py
```

Supplementary exact checks include 20 boundary-transfer/contractor
identities, nine forward endpoint identities, 24 compact-source checks,
and 72 terminal cost/equality checks. The arithmetic engine's 116,914
regression checks are separate from the quantified covers.

The old three-root nonshort caller and [cover-chain method](EXACT_COVER_CHAIN.md)
remain available as superseded methods. Their interrupted/paused forests
were never completed and are not premises of this proof. Do not treat
their large processed-box totals as completed certificates or as a
remaining task after the boundary proof.

## 5. Dependency and trust boundary

The final argument begins with an actual geometric minimizer and the
[arbitrary-control reverse comparison](REVERSE_COMPARISON.md). It obtains
a finite representation before [normalizing the same PMP lift](GLOBAL_NORMALITY.md).
The sufficient complete-period partition R/M3/M1/F/M2 reduces the
minimizer to at most five pieces. The [terminal audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
checks arbitrary four-piece factors, strict mixed-five comparison,
terminal word coverage and equality transport. Classifying minimizers
then bounds every competitor and classifies the original equality disk.

External geometric inputs are worst-disk existence, balanced-boundary
regularity/normalization, the area-density identity and the explicitly
reviewed compact-domain result; standard endpoint-submanifold and
fixed-time Pontryagin principles are the analytic inputs. The
[compact-domain source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md) checks its
entire-trajectory scope, exact separation and all-control margin units.

Directed covers trust the frozen C++17 sources, reviewed interval/LP
verification, MPFR/GMP and execution platform. Native floating-point
arithmetic only proposes subdivisions or nonnegative weights; directed
bounds verify every exclusion. This is an internally reviewed
hand/computer-assisted proof, not external peer review or a Lean kernel
certificate.

## 6. Maintenance instructions

Preserve the true state/frame and costate twist, free initial state,
actual external switches and same normalized covector. Do not revive the
refuted unconditional local L3 shortening assertion, replace a whole
period by a local witness, or enumerate increasing word lengths.

Keep [CHECKLIST](../CHECKLIST.md), [ACTIVE_MAP](ACTIVE_MAP.md),
[SOURCE_MAP](../SOURCE_MAP.md) and the replay guide consistent with this
completion record. If an accepted proof premise is materially changed,
reopen the affected gate, review its domain and rerun its necessary
certificate before closing it again. Existing Lean sources and dependency
pins remain untouched until a different workflow is explicitly requested.
