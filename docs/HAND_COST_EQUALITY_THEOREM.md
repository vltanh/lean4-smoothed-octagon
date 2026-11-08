# The sharp smoothed-octagon theorem by hand

Date: 2026-11-08 UTC. **Complete hand proof, with independent internal
mathematical review.** All hand gates H-F, H-N, H-S and H-A are closed.
The [finite-period review](HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md),
[unrestricted inequality and equality review](HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md)
and [global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md) accept
the full chain. The explicitly listed external geometric and
maximum-principle results in Section 7 remain premises. No interval
cover, executable sign test or Lean verification is a premise.

## 1. Statement

Let

\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1},
\qquad A_{\rm oct}=\sqrt{12}\,\delta_{\rm oct}.
\]

Every trajectory in the original integral-form Reinhardt admissible
class, including arbitrary measurable controls, satisfies

\[
\boxed{C(T,X)\ge A_{\rm oct}.}
\tag{1}
\]

Every centrally symmetric planar convex disk K has greatest packing
density

\[
\boxed{\delta(K)\ge\delta_{\rm oct},}
\tag{2}
\]

with equality precisely for the invertible affine images of the
concrete smoothed octagon. No finite-control or Pontryagin hypothesis
is imposed on the arbitrary competitors in (1) or the disks in (2).

## 2. Retain a geometric minimizer and compare with every control

The classical existence and balanced-normalization results supply an
actual worst disk. Its
[admissible realization](ADMISSIBLE_REALIZATION.md) has its physical
area cost. The [reverse comparison](REVERSE_COMPARISON.md) applies to
the entire integral admissible class: in the range below pi it
reconstructs a balanced disk of equal area; above that range the
explicit octagon already supplies the required comparison.
Consequently the retained realization is a global control minimizer
against arbitrary measurable admissible controls.

The concrete octagon is an admissible competitor, so the minimum
cost \(A_*\) satisfies

\[
A_*\le A_{\rm oct}<\pi.
\tag{3}
\]

It is enough to classify these actual minimizers. Once their cost
is shown to equal \(A_{\rm oct}\), the definition of a global
minimum gives (1) directly. No approximation by finite words or
iteration of local replacements is needed.

After (1)--(2) have been proved, a disk with density delta_oct is
itself a worst disk. For the equality assertion, begin with the
realization of that given disk. The same comparison makes its own
realization a global control minimizer. That disk is retained until
Section 6; it is not exchanged for another minimizer.

## 3. Obtain a finite representation before proving normality

The [compact-domain source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md)
places each minimizing realization in a common compact strict-star
state domain with all three physical margins at least 2/15.
This holds at every point, for inactive as well as active controls.
It uses the earlier geometric area bound, without importing the
later computer-assisted singular-basin analysis.

Apply the free-time endpoint-submanifold maximum principle as in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md). The initial state is
free and both cotangent endpoints have the actual twist. No normality
assumption is made at this step.

The [singular cost budget](SINGULAR_COST_BUDGET.md) supplies positive
clearance for unit-normalized lifts, including abnormal ones. The
[measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md) then gives
at most four vertex pieces on each interval with a missing control.
Its integrating-factor switching equation has derivative equal to a
positive factor times a quadratic, so Rolle's theorem gives the
finite local count, including the nontriviality exception.
The [quantitative regular-switch theorem](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
combines this with the clearance to give a finite vertex
representation. Its large bound is used for finite minimum selection,
not for enumerating words.

Changes of control on null sets, deletion of zero durations and
merging equal adjacent controls preserve the actual state, frame,
cost and boundary. The merging includes the twisted seam. The
fixed-edge endpoint obstruction excludes the unswitched case.
Now the [normality theorem](GLOBAL_NORMALITY.md) applies to the
finite representation and normalizes the same lift to lambda=-1.
Thus finiteness precedes normality. No new independently chosen
covector is introduced for the exclusion arguments.

## 4. Exclude every minimizing period with at least six pieces

Let N be the number of positive pieces after the preceding
normalizations, and suppose N>=6. Read switch signs through the
genuine twisted extension of the state, frame and common covector.

An entirely reverse period is impossible by
[the reverse-period theorem](GLOBAL_REVERSE_PERIOD_EXCLUSION.md),
which applies at a cyclic active-margin minimum. An entirely forward
period is impossible by
[the all-forward hand theorem](HAND_FORWARD_PERIOD_EXCLUSION.md)
and its [norm audit](HAND_FORWARD_NORM_AUDIT.md).
The forward twist forces N=1 modulo 3, hence N>=7 in this case;
its seven cost-budget indices are therefore distinct. Its genuine
exterior norm floors and stationary inequalities imply a Casimir
strictly above the original competitive cap.

Suppose the period is mixed. The
[minimum-structure theorem](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
forces every maximal reverse run to contain exactly two switches.
The [small-forward-minimum hand theorem](SMALL_FORWARD_MINIMUM_HAND_PROOF.md),
together with the reverse-centre scale bound, places a global
active-margin minimum at a reverse centre.

Choose the smaller adjacent turn at that centre. At a tie either
choice is allowed. Reflection combined with reversal of time, as
proved in Sections 1--3 of the minimum-structure theorem, gives the
required orientation while preserving all physical and cotangent
endpoints. The alternatives are now exhaustive:

| Actual chosen side | Hand contradiction |
|---|---|
| The turn lies on a short forward run | [Smaller-short hand period exclusion](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md) |
| The turn lies on a nonshort run and its next genuine switch is forward | [Nonshort forward hand exclusion](MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md) |
| The turn lies on a nonshort run and its next genuine switch is reverse | [Nonshort reverse hand exclusion](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md) |

The actual continuation alternative in
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md)
justifies the last two rows, including a successor through the seam.
The first row applies also when both adjacent runs are short. There
is therefore no need for the historical large coefficient tables
that first tried to prove one neighboring run nonshort.

The final short theorem establishes, in order,

\[
2<x<13/6,\quad 0\le\delta:=\beta/x-1<1/19,
\quad1+\tfrac{13}{5}\delta\le\alpha\le1+3\delta,
\quad\Gamma_{\rm actual}>1829/10000.
\]

Its actual descending root supplies the negative shear needed by the
physical completion-score comparison. That comparison makes the
original full-period cost strictly greater than \(A_{\rm oct}\),
contradicting (3). Each restriction is proved on the full domain
needed by the next one; the extension from 15/7 to 13/6 and the
delta=0 boundary are included explicitly.

All three mixed rows retain the actual common covector, arbitrary
unequal positive factors, genuine first switches and the whole-period
budget. Scalar comparisons receive no unproved closure or transported
competitive cap. These are uniform complete-period exclusions,
without a growing word-length catalogue or the refuted unconditional
local shortening claim. Hence

\[
N\le5.
\tag{4}
\]

## 5. A direct terminal count and its strict cost comparison

The [terminal hand count](HAND_TERMINAL_COVERAGE.md) uses the exact
label twist \(i_{j+N}=i_j+1\pmod3\). Thus the switch signs obey

\[
\sum_{j=0}^{N-1}\epsilon_j\equiv1\pmod3.
\tag{5}
\]

For N<=5 the reverse-period theorem removes the entirely reverse
case. In the all-forward case, (5) gives N=1 or N=4. The fixed-edge
obstruction removes N=1, leaving the four-piece word 0120 up to a
genuine rebase and cyclic relabeling.

In a mixed period let m be the number of reverse runs and F the
number of forward switches. The two-switch reverse-run theorem
gives N=2m+F and F>=m. Hence N>=3m, so m=1 when N<=5.
Equation (5) now gives F-2=1 modulo 3. Since 1<=F<=3, one has
F=3 and N=5, with representative 01020. This is a direct count;
no finite-word enumerator is needed.

The analytic comparisons in
[SMALL_PERIOD_COST_EQUALITY_AUDIT, Sections 2--3](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
complete both cases. In four pieces, tangent closure forces the
alternating factors and the state endpoint fixes the initial state.
The asymmetric derivative/integral inequality has its unique minimum
at four factors sqrt(2), giving exactly \(A_{\rm oct}\).
In five mixed pieces, the strict logarithmic-envelope comparison
and positive middle duration give a strictly larger cost. Its
zero-middle-duration boundary reduces to the four-piece case after
deletion.

Every actual minimizer therefore has the octagon equality data and
cost \(A_{\rm oct}\). Section 2 gives the unrestricted control
inequality (1) and its geometric consequence (2).

## 6. Equality identifies the original disk

For a given equality disk, retain its original balanced realization,
initial normalization e, genuine rebase cut s and cyclic relabeling
matrix \(C=R^r\). The classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

Put \(N_0=2\sqrt2-1\). In the rational coordinates of the
four-piece calculation the equality state is

\[
X_0=\begin{pmatrix}0&-\sqrt{N_0}\\1/\sqrt{N_0}&0\end{pmatrix},
\qquad a_i=2/\sqrt{N_0}.
\]

Every factor is sqrt(2), and each physical duration equals
\(\log2/(2\sqrt{N_0})\). Undoing that coordinate conjugation
gives the concrete octagon state \(\Phi(0,\sqrt{N_0/3})\).
ODE uniqueness on the successive constant-control arcs identifies
the full state and frame, not just a scalar cost or terminal product.

Their six cyclic contact arcs give the complete boundary of the
retained disk. Consequently

\[
K=e^{-1}G(s)C(K_{\rm oct}).
\tag{6}
\]

This is an invertible linear map; restoring the original centre
permits a translation. Conversely, an invertible linear map gives
a bijection of lattice packings and scales disk area and lattice
covolume by the same factor. Greatest lattice-packing density is
therefore affine invariant. The classical Fejes Toth theorem
identifies it with greatest packing density for this planar centrally
symmetric class, proving equality for every affine octagon.

## 7. External premises and what has been verified

The external mathematical inputs are retained explicitly:

1. The classical planar convex-disk facts recorded in Hales--Vajjha,
   [Chapter 2](https://arxiv.org/html/2405.04331v1#Ch2): Fejes Toth's
   greatest/lattice packing-density theorem (Theorem 2.1.3), worst-disk
   existence and regularity (Lemma 2.2.5 and Lemmas 2.4.2--2.4.3),
   balanced normalization and the critical-hexagon area/density identity
   (Theorem 2.2.2). Its parallelogram exception causes no gap: such a
   disk tiles with density one and cannot be a worst or equality disk
   because the octagon has density less than one.
2. The earlier geometric area lower bound, Theorem 5.0.6 in
   [Chapter 5](https://arxiv.org/html/2405.04331v1#Ch5), together with
   the exact compact-domain argument in the repository's
   [source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md).
3. The standard free-time endpoint-submanifold and fixed-time edge
   maximum principles, with their hypotheses checked in the linked
   PMP notes, and standard ODE, absolute-continuity and calculus results.

The subsequent finite representation, same-lift normality, uniform
period exclusions, direct terminal count and affine transport use
the repository's hand arguments. The published later finite
bang-bang/basin results and the repository's historical executable
covers are not premises. Numerical exploration and symbolic
reconstruction may check discovery and transcription; every invoked
finite sign argument is given by explicit algebra and elementary
inequalities in its theorem note.

The [global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md) and
the separate scalar/interface reviews record internal mathematical
acceptance. This is not external peer review or Lean kernel
verification. No Lean, Lake, typechecking or CI has been run, and
the existing formalization sources and dependency pins remain
untouched.
