# Assembly of the sharp cost bound and affine equality case

Date: 2026-11-07. Hand-proof assembly. No Lean, Lake, typechecking or CI.

**Current status: conditional on the remaining M2 exclusion.** This note
records the final implication and its precise dependencies. It does not
mark M2, G4 or G5 complete. The current status is in [HANDOFF](HANDOFF.md).

## 1. Statement to be concluded

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

for every centrally symmetric planar convex disk. Equality in (2) must
hold exactly for the affine images of the concrete smoothed octagon.
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

Every minimizing realization in (3) lies in the explicit compact
strict-star domain from the published compact-domain theorem. The
standard endpoint-submanifold maximum principle supplies the actual
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

Delete zero-duration pieces, merge equal adjacent controls, and choose
the cut at an actual switch, also merging across the twisted seam when
needed. The [normality theorem](GLOBAL_NORMALITY.md) then supplies the
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
| Mixed, all reverse runs length two and some forward run length at least two | M2 — still open |

The table exhausts cyclic sign sequences. These are sufficient
assignments of an entire minimizing period. A short local window inside
an M2 period is not reassigned to M1. In particular, the disproved
unconditional local L3 replacement assertion is not a premise.

Once M2 is proved, every row is impossible and hence

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
allows a translation, giving affine equivalence. Conversely invertible
affine maps preserve the greatest packing density in the centrally
symmetric convex class, so every affine octagon has equality. The
boundary and normalization details are reviewed in
[MINIMIZER_WINDOW_AUDIT, Section 6](MINIMIZER_WINDOW_AUDIT.md).

## 7. Remaining acceptance boundary

This logical assembly uses the actual geometric realization, the
compact-domain input, the standard maximum principle, the complete
finite normal representation, the five sufficient exclusions, and the
small-period cost/equality calculation. The final dependency audit must
check that each premise has the stated scope and that each computational
exclusion has a complete successful cover for its audited source.

At present M2 is still open. No statement in this note changes that
status or supplies a Lean proof. The conclusion becomes available only
after that remaining theorem and the final mathematical audit are
complete.
