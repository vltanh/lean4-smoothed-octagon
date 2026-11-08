# Independent audit of the final cost and equality dependency chain

Date: 2026-11-07. Internal mathematical review. No Lean, Lake,
typechecking or CI.

**Acceptance:** the complete dependency chain has the required scope
for the unrestricted sharp cost inequality and the affine equality
classification. The uniform M2 theorem, all four new boundary covers,
their independent source/interface audits, and their separate fresh
replays are accepted. The terminal through-five comparison and equality
transport complete the argument under the explicit classical geometric,
maximum-principle and directed-arithmetic premises below.

This is internal independent mathematical/source review of a
hand/computer-assisted proof. It does not assert Lean-kernel or external
peer-review verification.

The final implication is
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md).
The terminal calculations have their separate
[small-period audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md). The new scalar
certificates have separate source and domain audits; the present review
checks how their conclusions apply to the original problem.

## 1. The reduction really starts with arbitrary competitors

The starting geometric input is existence of an actual worst centrally
symmetric convex disk. Its balanced normalization and the construction
in [ADMISSIBLE_REALIZATION](ADMISSIBLE_REALIZATION.md) retain that disk
and give an admissible trajectory with its exact normalized area as
physical cost.

The comparison in [REVERSE_COMPARISON](REVERSE_COMPARISON.md) has the
quantifier needed to turn this realization into a global control
minimizer: it accepts every trajectory in the original integral
admissible class, including measurable controls. At cost below pi it
constructs a balanced disk of equal area. At larger cost the explicit
octagon supplies a cheaper balanced competitor. Thus the realized
geometric minimum is no more expensive than every admissible control
competitor.

The low-cost reverse construction is not inferred from the matrix
endpoint alone. The regularity and cyclic extension first give a C1
frame and Lipschitz state from the integral equations. The reflected
first-row angle has positive speed and is bounded by the cost. Its
endpoint lift is therefore exactly pi/3 at low cost. Cyclic repetition
gives one full row turn. A determinant-one obstruction prevents the
first contact from being antipodal to that row; continuity then bounds
the contact winding, which is exactly one positive turn. This proves
simplicity before the a.e. curvature theorem supplies convexity of the
radial hull. The contact shift supplies the area identity with the
required sixth-period normalization.

This ordering avoids two circular arguments: simplicity is not used to
prove its own winding premise, and control-minimizer existence is not
used to prove the reverse comparison that establishes it.

It suffices to classify these actual global minimizers. Once their cost
is shown to be the octagon cost, their minimizing inequality immediately
bounds every admissible competitor. Arbitrary competitors need not be
finite, normal, geometrically parametrized, or individually subjected to
the subsequent case partition.

## 2. External premises and finite-before-normal ordering

The retained external geometric inputs are Fejes Toth's equality of
greatest and greatest lattice-packing density, worst-disk existence,
balanced-boundary regularity and normalization, and the balanced
area/density identity. Their source is Hales--Vajjha,
[*Packings of Smoothed Polygons*, Chapter 2](https://arxiv.org/html/2405.04331v1#Ch2):
Theorem 2.1.3, Lemma 2.2.5, Lemmas 2.4.2--2.4.3, Definition 2.4.7 and
the following balanced-disk discussion. This identifies the packing
density being bounded and the particular geometric minimizer being
retained throughout the realization.

The compact-domain input is the conclusion of
[Theorem 5.0.2](https://arxiv.org/html/2405.04331v1#Ch5), with the domain
in Definition 5.0.1. Its explicit quantifier is any point of the
trajectory of a balanced disk competitive with the octagon, so one
common compact region contains every point of every minimizing
realization. It does not assume finitely many controls. The source
repair below uses only the earlier geometric area lower bound of
Theorem 5.0.6, not the later finite bang-bang theorem. Standard free-time
endpoint-submanifold and fixed-time Pontryagin principles, and the
standard ODE/absolutely continuous analysis used in the linked hand
proofs, are the other external analytic inputs.

The [compact-domain source audit](COMPACT_DOMAIN_SOURCE_AUDIT.md) checks
this entire-trajectory quantifier, repairs the v1 sector display, and
replaces the decimal separation by exact bounds using the earlier geometric
area theorem 5.0.6. It also verifies `p_i>=2/15` for all three controls,
including inactive controls, in the physical normalization used below.

The proof route uses the following dependency order:

| Step | Scope needed and supplied |
| --- | --- |
| Actual global PMP | Free positive terminal time; free initial state; coupled twisted endpoints; measurable simplex controls |
| Singular cost budget | All initial unit-normalized lifts, including abnormal lifts; no finite-word premise |
| Direct measurable-edge theorem | A restriction of the actual global minimizer; a separate fixed-endpoint edge PMP; both normal and abnormal multipliers |
| Three-guard count | The preceding clearance and edge theorem give a finite vertex representation, with `N<10^56` |
| Global normality | Applied only after that finite representation; excludes every abnormal lift of the same twisted period |
| Normal rescaling | Positive rescaling gives the single physical convention `lambda=-1` used in the scalar identities |

In particular the separate edge PMP is not obtained by assuming that a
restriction of an arbitrary full-system lift remains a useful edge
multiplier. Its nontriviality and its zero-count argument are established
on the actual fixed-endpoint edge problem. The integrating-factor proof
starts with merely measurable controls and includes both abnormal cases.

The current route does not import the published finite bang-bang theorem
or the numerical escape/basin steps in its proof. Historical references
to that theorem in earlier compactness/window notes are not premises of
the replacement route through
[SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md),
[MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md), and
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md).
Only the stated compact state bounds from those older notes are retained.

## 3. Endpoint, cotangent and normalization checks

The complete-period endpoints are

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\]

The endpoint-submanifold variation, with its free initial state, gives
the corresponding reduced state-covector twist. Left invariance gives
conservation of the spatial primary costate and the same twist for the
body primary costate. These are distinct statements; the primary
costate is not required to commute with R at the initial time.

The extension across every seam transports the state, control labels
and both costates together. Rebasing retains one actual lift and its
complete-period cost. Reflection together with reversal of time is an
actual symmetry of the positive-control problem and preserves the cost
multiplier, the maximum inequalities and the endpoints. Formal backward
word reading alone would not have this property; it is not the operation
used in the minimum and smaller-turn arguments.

The normalization dictionary used throughout the final route is

\[
C=\sqrt{12}\,\delta,\qquad
\lambda=-1,\qquad
\kappa^2=\det\Lambda_1=12\gamma^2.
\]

The active margins satisfy
`p_j=-sqrt(3) tr(Z_j X)` and
`p0*p1+p1*p2+p2*p0=4`. A vertex factor q and its physical duration
satisfy `t=a log(q)/2`. The compact lower bound is therefore `a>=2/15`
in the same margin units used by both interval reductions. No factor of
eight in the switch norms is absorbed into the Casimir or the cost.

The spectral cost bound and endpoint defect test use that same primary
costate. They establish the primary polar increment and the available
completion budget from the whole-period endpoints. A local endpoint
angle is not chosen independently of that lift or of its winding.

## 4. The complete-period partition and the minimum window

After null-set modifications, zero-duration deletions and twisted-seam
merging, the actual finite period has positive vertex pieces. The
fixed-edge endpoint obstruction excludes an unswitched period, so the
cut may be placed at an actual switch. Its sign sequence is cyclic even
though its labels repeat with the prescribed shift. The sufficient
partition in the final assembly exhausts this cyclic sign sequence.

The purely reverse exclusion has no length restriction and uses
necessary same-lift needle inequalities. The mixed minimum theorem
removes every reverse run except length two. The all-short mixed case
then uses its whole-period winding identity, including the separately
treated two-centre base. These results are entire-period assignments;
they do not assert the disproved unconditional local six-window
replacement statement.

For the entirely forward case with `N>=6`, the twist forces `N>=7`.
The selected five minimum-window margins and three interior stationarity
equations consequently have the distinct indices required by the F
reduction. The seven-entry lower cost comparison and exterior switching
floors come from the actual whole period, with no assertion that a
comparison array closes its frame. Its accepted exact certificate is
reviewed in [GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md).

I reviewed the full-period implication in
[MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md).
In a remaining mixed period, an actual reverse centre has active square
below 4/3. Hence the global active minimum also has square below 4/3.
The minimum-structure theorem permits only a reverse centre or the
four-forward-switch pattern there; the small-forward-minimum theorem
excludes the latter. Its three interior indices are distinct when
N>=6. This argument does not presuppose the later refined scale bound.

Choose either smaller adjacent turn at that minimum, including equality.
The proved physical reflection/time-reversal symmetry puts it in the
required orientation. Its adjacent forward run is short or nonshort.
The completed [smaller-short theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md)
excludes the first possibility. The other gives exactly the consecutive
actual same-lift data and next-switch alternatives of
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
This permits the smaller side to be short even when the other side is
nonshort. The short-bridge minimum theorem supplies the stated
existence of an adjacent nonshort run but is not used to assume that
both sides are nonshort.

In the nonshort case the next actual switch after the displayed arc r
exists by finiteness and cyclic continuation. After adjacent equal
controls are merged, its direction is exactly forward or reverse. The
forward branch uses the transported next-switch norm >=3/4. The reverse
branch uses the actual next reverse-centre value A>=a and its genuine
secant to deduce w<=Sec(a,r,d) and r^2>=ad, retaining A=a. These are
the conditions of the two accepted boundary exclusions. Neither
alternative chooses a later stationary root, supplies a new local
costate, or assumes a closed six-piece trajectory. The six consecutive
arc positions are legitimate for N>=6, and their next switch may cross
the actual twisted seam. This exhausts M2 uniformly in all run lengths.

The finite bound is used to choose a global margin minimum and to justify
the cyclic partition. No catalogue up to that bound is part of the
proof. Rank defects cause no omitted case in the first-order scalar
reductions, since no endpoint Jacobian is inverted to choose a new
costate.

## 5. Boundary comparison, complete covers and arithmetic acceptance

Every actual vertex duration is positive after merging and deletion.
Weak switching derivatives and third-control ties remain legitimate
PMP data. The scalar certificates enlarge such inequalities to closed
conditions; an actual point still satisfies every retained condition.
Coincident secant endpoints use analytic divided-difference limits.
The nonshort charts retain all maximal-parameter ties, and their
desingularization extends the actual solved root continuously to the
simultaneous zero-duration face.

The accepted F replay processed 20,999 nodes and excluded 10,501 leaves,
with three roots, zero unresolved boxes and an empty final stack. The
identity `20999=2*10501-3` accounts for its complete cover. Its circular
region is supplied by a separate audited hand lemma.

The accepted smaller-short replay processed 107,977 nodes and excluded
53,989 leaves from one root, again with zero unresolved boxes and an
empty stack. The identity `107977=2*53989-1` accounts for its cover.
Its mathematical interface, arithmetic engine and frozen caller have
the separate [independent audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md).

For the nonshort case, the scalar equation for the actual first forward
root is solved while b increases to b*=(a^2+4)/(a+c)-a, keeping a,c,d,r
and the actual incoming secant v fixed. The coefficient R_u stays
strictly negative, including at the endpoint. The continuous linear
equation for j=u-U(a/(a+b)) preserves j<0, and the exact derivative
formula gives w*<w_actual. The independent
[reverse audit](MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md) checks these
signs, all retained contractors and the frozen caller. Only the proved
upper incident-norm and upper outgoing-norm comparisons are used.
No lower norm, outgoing derivative, acuteness, physical endpoint or
Casimir cap is silently transferred to this artificial boundary.

The new central parameter is delta0=0. Recompute
epsilon'=max(delta1,delta2), where
delta1=(d-a)/(a+c) and delta2=(c+d)(d+r)/(d^2+4)-1.
The hand theorem
[MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
uses only the retained a/c order and scale and nonnegative maximal
weights, so it applies with l0=0 to exclude epsilon'<=1/32. This covers
original points whose old maximum was delta0, even when that old
maximum exceeded 1/32. The remaining points lie in the two closed
charts l1=1 or l2=1 with epsilon' in [1/32,15]. All ties and zero-weight
faces are included. The chart-2 restriction d<=c comes from the
unchanged incoming missing-control inequality, not from an unpreserved
outgoing condition.

The [common low-a theorem](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md),
with its [independent audit](MIXED_NONSHORT_LOW_A_BOUNDARY_AUDIT.md),
excludes a<=1/2 using only common necessary data. It imposes neither
successor alternative. Consequently the forward covers may start at
the closed overlap a=1/2 without a circular appeal to a forward cap.
The reverse comparison instead directly preserves
w*<w_actual<=Sec(a,r,d), which is its retained successor inequality.

For the forward branch, stationarity writes the diagonal as H(w),
affine in w. The transported norm T(w) has derivative -B<0, with
B>0 supplied by the unchanged compact inactive-margin inequality.
Since T(w_actual)>=3/4, the actual w lies between w* and wcap, where
T(wcap)=3/4. The squared Casimir Gamma(w) is a strictly concave
quadratic. Therefore the actual cap Gamma(w_actual)<23/125 implies
that at least one of Gamma(w*) or Gamma(wcap) is <=23/125. The two
endpoint caps are separate enlarged necessary alternatives. The
upper-endpoint source clears only the positive B^2, rather than dividing
by a potentially small interval. The exact algebra and both callers
are accepted in the
[forward boundary audit](MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md).
This step uses the cap on the actual covector; it does not claim a cap
is preserved by the b comparison.

The four complete new two-root forests have the following independent
original/fresh-replay accounting. Each row has zero pending boxes,
zero unresolved boxes, and the identity N=2L-2.

| Necessary domain | Nodes N | Excluded leaves L | Maximum depth |
| --- | ---: | ---: | ---: |
| Reverse-next boundary | 106,134 | 53,068 | 26 |
| Common low-a boundary | 74,772 | 37,387 | 23 |
| Forward lower endpoint w* | 37,940 | 18,971 | 27 |
| Forward upper endpoint wcap | 60,976 | 30,489 | 32 |

The original and independent executions agree on every mathematical
counter and rejection-reason count. The full logs and JSON receipts
are retained under `explorations/results` and `explorations`. I read
and ran the portable
[boundary record verifier](../explorations/mixed_nonshort_boundary_records_verify.py):
all four cases passed. It checks the frozen caller and header hashes,
exact two-root domains, both complete fresh-domain logs, branch and
depth counters, reason sums, zero frontier, successful replay exit and
artifact hashes. The source/interface audits and the fresh executions
remain distinct evidence; hash/accounting replay is not a substitute
for executing a caller. The earlier incomplete three-root nonshort
forest is not a premise and is not being declared completed.

Directed-interval conclusions retain the explicit reviewed C++17,
MPFR/GMP and compiler/runtime trust boundary. Native floating-point
calculations only propose nonnegative dyadic weights or choose
subdivisions; a fresh outward-rounded bound must verify every rejection.
The exact symbolic checkers supplement the hand identities but do not
establish the global quantifiers. Complete root coverage, source-domain
agreement, and the hand small-parameter comparison are all required
and are supplied separately. These are computer-assisted hand
certificates, not Lean kernel proofs.

## 6. Terminal cost and affine equality

The [terminal review](SMALL_PERIOD_COST_EQUALITY_AUDIT.md) supplies the
needed arbitrary-factor comparison for at most five pieces. Fewer than
four pieces are excluded by the fixed-edge endpoint obstruction and
twisted rebasing. Four-piece tangent closure forces alternating factors,
and state closure forces the initial state. The asymmetric cost formula
has its unique minimum at the octagon parameters. The mixed five-piece
comparison is strict. The entirely reverse five-piece minimizer is
excluded by R, so the separate long arbitrary-trajectory reverse-five
comparison is not required in this minimizer-only chain.

For an arbitrary K satisfying delta(K)=delta_oct, the now-proved
inequality and the octagon competitor first show that K is a worst
disk. Its own balanced normalization and realization are then a global
control minimizer by the unrestricted comparison in Section 1. The
equality argument retains that realization and its contact boundary.
It does not replace K by a chosen minimizer or by an artificial scalar
boundary point. At the four-piece equality parameters, the initial
state and each physical duration agree with the concrete octagon. Successive
constant-control flow uniqueness gives equality of the actual state and
frame; the cyclic six contact arcs then give the complete boundary.

If e is the original linear normalization, s the rebase cut, and
`C=R^r` the cyclic relabeling, the classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

Equality of its contact boundary with the octagon boundary gives

\[
K=e^{-1}G(s)C(K_{\rm oct}).
\]

The displayed map is invertible and linear. Restoring an arbitrary
original centre permits a translation. Conversely an invertible linear
map carries lattice packings bijectively to lattice packings and scales
area and covolume equally. Greatest lattice-packing density is therefore
affine invariant. The external Fejes Toth theorem identifies it with
greatest packing density in this centrally symmetric convex class,
which proves equality for every affine octagon. This avoids an
unjustified assertion that arbitrary rotated congruent packings remain
congruent packings under a general affine map. The terminal theorem
therefore supplies both directions of the affine classification.

## 7. Audit conclusion

No additional normalization, endpoint, measurable-control, case-partition
or equality-transport gap was found in this dependency review. The
uniform M2 theorem has now been independently checked as a statement
about each actual competitive minimizing period. Its two successor
alternatives are closed by accepted hand reductions, frozen-source
audits and complete original-root replays. All five sufficient
whole-period assignments for N>=6 are consequently excluded.

The terminal comparison then gives the octagon cost and its unique
four-piece equality parameters. Existence and unrestricted reverse
comparison transfer this minimum to every original measurable-control
competitor. Applying the same classification to the realization of
each arbitrary equality disk, retaining its normalization and boundary,
gives exactly the affine octagons.

I therefore accept G4 and G5 at the stated hand/computer-assisted level,
under the external inputs in Section 2 and the arithmetic trust in
Section 5. This closes the unrestricted sharp Reinhardt cost inequality
and affine equality classification within that explicit proof scope.
It makes no claim that existing Lean drafts elaborate or pass the
kernel, and no claim of external peer review.
