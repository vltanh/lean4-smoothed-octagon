# Assembly of the sharp cost bound and affine equality case

Date: 2026-11-07. Completed hand/computer-assisted assembly, with an
internal independent dependency audit. No Lean, Lake, typechecking or CI.

**Accepted conclusion:** the unrestricted sharp cost bound and affine
equality classification follow from the retained classical geometric
and maximum-principle inputs, the five completed whole-period exclusions,
and the reviewed directed-interval certificates. The exact external
premises and arithmetic trust boundary are listed in Section 7 and checked
in [the final dependency audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md).
This is a completed hand/computer-assisted proof at that stated level;
it is not a Lean-kernel or external peer-review verification.

## 1. Sharp inequality and equality theorem

Let

\[
\delta_{\rm oct}
=\frac{8-4\sqrt2-\log2}{2\sqrt2-1},\qquad
A_{\rm oct}=\sqrt{12}\,\delta_{\rm oct}.
\]

The cost assertion is

\[
 C(T,X)\ge A_{\rm oct}
\tag{1}
\]

for every trajectory in the original integral-form Reinhardt admissible
class, including measurable controls. Its geometric consequence is

\[
 \delta(K)\ge\delta_{\rm oct}
\tag{2}
\]

for every centrally symmetric planar convex disk, where \(\delta(K)\)
is its greatest packing density. Equality in (2) holds exactly for the
invertible affine images of the concrete smoothed octagon. The classical
Fejes Toth theorem identifies greatest packing density with greatest
lattice-packing density in this class; see Hales--Vajjha,
[*Packings of Smoothed Polygons*, Theorem 2.1.3](https://arxiv.org/html/2405.04331v1#Ch2).
Neither a finite-control hypothesis nor a Pontryagin hypothesis is part
of (1) or (2); these are conclusions about arbitrary competitors.

## 2. Why it suffices to classify actual global minimizers

The geometric existence and normalization results supply an actual worst
disk. The forward realization and the low-cost reverse reconstruction in
[REVERSE_COMPARISON](REVERSE_COMPARISON.md) identify its trajectory as a
global minimizer of the **unrestricted** admissible control problem.
The concrete octagon is an admissible competitor, so its minimum cost
\(A_*\) satisfies

\[
A_*\le A_{\rm oct}<\pi.
\tag{3}
\]

The reverse comparison applies to arbitrary admissible controls, not
only finite splines. It constructs a balanced disk of area at most the
control cost, and gives equality in the low-cost range. Thus the
geometric minimizer competes against the entire class in (1).

Consequently a lower bound \(C\ge A_{\rm oct}\) for every actual global
minimizer gives \(A_*=A_{\rm oct}\). The definition of global minimizer
then gives (1) for every admissible competitor. This step does not
approximate arbitrary controls by finite words or assume that a sequence
of local replacements terminates.

For equality rigidity, start with the realization of an **arbitrary**
disk attaining the geometric minimum, rather than replacing it by some
preferred worst disk. Its own realization is a global control minimizer
by the same comparison. Classifying that realization therefore
classifies the given disk.

## 3. Finite normal representation, without a finite-word hypothesis

Every minimizing realization in (3) lies in one common explicit compact
strict-star domain, with all three physical margins at least \(2/15\),
including inactive margins. The
[compact-domain source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md) verifies the
entire-trajectory quantifier and gives an exact repair of the printed
sector and numerical separation in the source, using its earlier
geometric area bound. No finite-switch or normality premise enters this
compactness step. The standard endpoint-submanifold maximum principle
supplies the actual
free-time lift, with a free initial state and both twisted cotangent
endpoints; see [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md).

The [singular cost budget](SINGULAR_COST_BUDGET.md) gives normalized
clearance \(D>10^{-11}\). The direct
[measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md), followed by the
[three-guard count](QUANTITATIVE_REGULAR_SWITCH_BOUND.md), gives a finite
vertex representation with \(N<10^{56}\). This route does not use the
published finite bang-bang theorem or its numerical basin analysis.
Changing controls on null sets leaves the same absolutely continuous
state, frame, cost and geometric boundary.

Delete zero-duration pieces and merge equal adjacent controls, also
across the twisted seam when needed. The fixed-edge endpoint obstruction
in [the terminal audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md) excludes an
unswitched period, so a cut at an actual switch is available. The
[normality theorem](GLOBAL_NORMALITY.md) then supplies the
normalization \(\lambda=-1\) for this same period. Weak or third-control
ties remain covered by the actual switching rules. No assumption of
simple roots, a minimum dwell time, or full endpoint rank is introduced.

## 4. The sufficient complete-period partition

Suppose the resulting description has \(N\ge6\). Read its switch signs
cyclically through the actual twist.

| Complete-period class | Required exclusion |
| --- | --- |
| Every switch reverse | [R](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| Mixed, with a reverse run of length other than two | [M3](MIXED_GLOBAL_MINIMUM_STRUCTURE.md) |
| Mixed, all reverse runs length two and all forward runs length one | [M1](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md), including its two-centre base |
| Every switch forward | [F](GLOBAL_FORWARD_PERIOD_EXCLUSION.md) |
| Mixed, all reverse runs length two and some forward run length at least two | [M2](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) |

The table exhausts cyclic sign sequences. These are sufficient
assignments of an entire minimizing period. A short local window inside
an M2 period is not reassigned to M1. In particular, the disproved
unconditional local L3 replacement assertion is not a premise.

For M2, the actual global active-margin minimum must be a reverse
centre. Choose its smaller adjacent turn, with ties allowed. A short
forward run on that chosen side is excluded by the
[smaller-short theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).
Otherwise the [actual continuation alternative](MIXED_SMALLER_TURN_CONTINUATION.md)
gives the next genuine switch as forward or reverse. The accepted
[forward endpoint exclusion](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md)
and [reverse boundary exclusion](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md)
exclude those two alternatives. The forward theorem includes the
branch-independent [low-scale exclusion](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md).
This partition permits one adjacent run to be short and preserves the
same actual PMP lift across the twisted seam. It covers arbitrary run
lengths, unequal factors, weak ties and endpoint-rank defects.

The scalar boundary comparisons have their own complete two-chart
covers and hand corner theorem. They do not assume that the artificial
boundary point is a physical period or that its Casimir equals the
actual one. Their complete records and independent interface/source
audits are checked in Section 5 of
[the final dependency audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md).

Every row is therefore impossible, and hence

\[
N\le5.
\tag{4}
\]

No enumeration up to the enormous theoretical switch bound is needed.
The finite bound is used only to choose an actual minimum margin and
make the cyclic classification legitimate.

## 5. The terminal comparison and all equality branches

The terminal argument for minimizing periods uses
[the four-piece proof](legacy/FOUR_LINK_HAND_PROOF.md),
[five-piece coverage and the mixed comparison](legacy/FIVE_ARC_PROGRESS.md),
and the already proved R exclusion. The cost comparisons retain
arbitrary unequal positive factors and the initial states forced by
the full endpoints. The [independent terminal audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
checks the calculations, coverage and equality transport, with 72 exact
supplementary identities independently replayed.

The fixed-edge exclusion and twisted rebasing eliminate descriptions
with fewer than four positive pieces. Every four-piece trajectory has
the unique surviving word, up to relabeling, and its asymmetric cost
has its unique minimum at the octagon parameters. Among the five-piece
descriptions, one class rebases and merges to four pieces. The mixed
five-piece class has strict cost greater than \(A_{\rm oct}\).

The entirely reverse five-piece class is excluded by R, whose
normal-PMP theorem has no lower bound on the period length. This route
does not assert a cost comparison for arbitrary non-PMP reverse-five
trajectories. Their separate [historical comparison](legacy/REVERSE_FIVE_ARC.md)
is available but is not a premise of the present assembly.

Thus (4) implies \(C\ge A_{\rm oct}\), and equality forces four
positive pieces with factors \(\sqrt2\), the specified initial state,
and the cyclic octagon word. Section 2 then gives (1) and (2).

## 6. Equality determines the original disk

Let \(K\) be any disk with \(\delta(K)=\delta_{\rm oct}\).
The inequality already proved and the concrete octagon show that this
\(K\) is itself a worst disk. Apply the balanced normalization and
realization to this very disk. Section 2 makes its own trajectory an
actual global control minimizer, and Section 5 fixes its equality data.
The scalar boundary comparisons in the exclusions are not substituted
for this geometric realization.

Put \(N_0=2\sqrt2-1\). In the rational basis of the four-piece proof,
the equality state is

\[
X_0=\begin{pmatrix}0&-\sqrt{N_0}\\1/\sqrt{N_0}&0\end{pmatrix},
\qquad a_i=2/\sqrt{N_0}.
\]

Each factor is \(\sqrt2\); hence each physical duration is
\(\log2/(2\sqrt{N_0})\). Undoing the rational-coordinate conjugation
gives \(\Phi(0,\sqrt{N_0/3})\). These are the actual concrete
octagon state and durations. Uniqueness of successive constant-vertex
flows identifies the entire state and frame, including their endpoints.

Retain the original disk \(K\), its initial normalization \(e\), the
rebase cut \(s\), and the cyclic relabeling \(C=R^r\). The classified
frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

The six contact arcs and their cyclic endpoint relation give the whole
boundary of the normalized disk. Equality of these arcs with the
octagon arcs gives equality of their compact convex radial hulls, and
therefore

\[
K=e^{-1}G(s)C(K_{\rm oct}).
\tag{5}
\]

The map in (5) is invertible and linear. Restoring the original centre
allows a translation, giving affine equivalence. Conversely an
invertible linear map sends a lattice packing to a lattice packing and
multiplies disk area and lattice covolume by the same absolute determinant
factor. Applying the inverse map proves invariance of the greatest
lattice-packing density. The Fejes Toth equality of greatest and lattice
density in this class then proves equality for every affine octagon;
translations do not affect density. The boundary and normalization
details are reviewed in
[MINIMIZER_WINDOW_AUDIT, Section 6](MINIMIZER_WINDOW_AUDIT.md).

## 7. Named premises, validation and trust boundary

The remaining external mathematical inputs are explicit:

- The classical geometric facts recorded in Hales--Vajjha,
  [Chapter 2](https://arxiv.org/html/2405.04331v1#Ch2): Fejes Toth's
  greatest/lattice density theorem (Theorem 2.1.3), existence and
  regularity of a worst disk (Lemma 2.2.5 and Lemmas 2.4.2--2.4.3),
  balanced normalization (Definition 2.4.7 and the following discussion),
  and the critical-hexagon area/density identity. The geometric
  realization retains the particular minimizing disk being classified.
- The earlier geometric area lower bound of Theorem 5.0.6 in
  [Chapter 5](https://arxiv.org/html/2405.04331v1#Ch5). Together with the
  elementary exact argument in
  [COMPACT_DOMAIN_SOURCE_AUDIT](COMPACT_DOMAIN_SOURCE_AUDIT.md), it supplies
  the uniform compact-domain conclusion of Theorem 5.0.2. The printed
  sector typo and decimal comparison are not unreviewed premises.
- The standard free-time endpoint-submanifold Pontryagin maximum
  principle and the separate fixed-time edge maximum principle, with
  the hypotheses and multiplier conventions verified in
  [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md) and
  [MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md), together with
  the standard ODE and absolutely continuous analysis used there.

The subsequent finite representation, normality, five whole-period
exclusions and terminal comparison are supplied by the linked repository
proofs and their mathematical/source audits. The published finite
bang-bang theorem and its numerical escape/basin analysis are not
premises of this route.

The computer-assisted exclusions use the reviewed C++17 directed
MPFR/GMP interval engine and its compiler/runtime trust. Native
floating-point proposals select subdivisions or candidate nonnegative
dyadic combinations; each rejection requires a fresh outward-rounded
interval bound. Every accepted forest has a full original-root
execution, zero pending and unresolved boxes, and the recorded
root/leaf accounting for its exact frozen source. The four new boundary
forests each have both an original execution and a separate fresh
replay, retained full logs and source/header hashes; the portable
[record verifier](../explorations/mixed_nonshort_boundary_records_verify.py)
checks their agreement. Exact algebra scripts supplement the hand
identities and source audits; they do not supply the missing geometric
or quantifier arguments.

The [final independent dependency audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md)
accepts the complete chain, including arbitrary measurable competitors,
actual twisted endpoints, the exhaustive M2 implication, and both
directions of affine equality. At this hand/computer-assisted level the
sharp Reinhardt inequality and affine uniqueness are proved. Existing
Lean drafts have not been compiled or kernel-checked, and this internal
review is not a claim of external peer review.
