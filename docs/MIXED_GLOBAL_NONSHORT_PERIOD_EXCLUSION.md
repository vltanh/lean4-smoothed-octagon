# Uniform exclusion of the remaining mixed whole-period class

Date: 2026-11-07. Hand assembly of the smaller-turn exclusions and their
complete directed interval certificates. No Lean, Lake, typechecking or CI.

**Status:** the smaller-short exclusion and all four new boundary covers
have complete independent source/domain and fresh-replay acceptance.
The [independent whole-period audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md)
accepts the exhaustive M2 implication below. The retained record verifier
and individual source audits are linked in Section 5; no unfinished
original three-root execution is used as a premise.

## 1. The uniform M2 theorem

Let a trajectory be an actual competitive minimizing period in the
retained Reinhardt admissible class, with its true frame, state and
cotangent endpoint twists and free initial state. Use its established
finite normal vertex representation, delete zero-duration pieces, and
merge equal adjacent controls, including across the twisted seam.
Assume that the resulting representation has at least six positive
pieces.

**Theorem.** Its cyclic switch signs cannot be mixed with every reverse
run of length two and some forward run of length at least two. Thus the
entire remaining M2 assignment is excluded, uniformly in the number of
pieces, the number and lengths of forward runs, and all unequal positive
arc factors.

Here a run length counts consecutive switch signs. A short forward run
has one forward switch; a nonshort forward run has at least two. The
statement is about a complete minimizing period. Every local identity
used below is obtained by restricting its actual normal PMP lift.

The retained actual-period inputs are the ones already used in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md),
[GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md), and
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md). In particular, competitiveness
means that the actual physical cost is no larger than the concrete
octagon cost. The resulting compact-state, negative-elliptic and
whole-period spectral/angle inequalities are the proved inputs in
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md),
[GLOBAL_SPECTRAL_COST_CASIMIR](GLOBAL_SPECTRAL_COST_CASIMIR.md), and
[MIXED_GLOBAL_REVERSE_ANGLE_DENSITY](MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md).

The finite normal representation is a conclusion of the unrestricted
minimizer chain: the [singular-cost clearance](SINGULAR_COST_BUDGET.md)
and the [measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md) give the finite
representation through
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md),
then global normality supplies the same period's normal lift. The
present theorem does not add a finite-control or PMP hypothesis to the
original admissible competitor class; it closes the remaining case of
that established minimizing-period reduction.

## 2. Locate a global active-margin minimum

Suppose such an M2 period exists. Its finite cyclic sequence of positive
active margins has a smallest value a. The actual twist permutes labels
and state margins together, so active values and switch directions
continue cyclically through any chosen cut.

The minimum structure in
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
gives two possible patterns at a global active minimum: four consecutive
forward switches, or the centre of a two-switch reverse run. A mixed
period has a reverse centre. Its established phase/scale bound puts
some reverse-centre active square below 4/3, so the global minimum also
has a^2<4/3. The
[small-forward-minimum theorem](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md)
excludes the four-forward-switch pattern. Its three interior indices
are distinct in the present at-least-six-piece representation.
Consequently a is at a reverse centre.

The uniform
[reverse-centre scale theorem](MIXED_REVERSE_CENTRE_SCALE_BOUND.md)
and compact-state theorem give

\[
\frac{2}{15}\le a,\qquad a^2<\frac{12}{17}.
\tag{1}
\]

The same actual covector has the normalized squared Casimir bounds

\[
\frac{27}{256}<\gamma^2<\frac{23}{125}.
\tag{2}
\]

The upper bound is a consequence of the complete-period cost and true
twisted endpoint. It is not an independent fit of a covector to a local
window. Different branches below use different subsets of these inputs.

The
[short-bridge minimum theorem](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md)
excludes short forward runs on both sides of a global minimum reverse
centre. Hence a touches a nonshort forward run. This does not require
both adjacent forward runs to be nonshort.

## 3. Choose the smaller adjacent turn

Choose the smaller of the two turn margins beside a, allowing either
choice when they are equal. The reflection combined with reversal of
time proved in Sections 1--3 of
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
is an actual symmetry of the positive-control problem: it preserves
physical cost, the normal multiplier normalization, all Hamiltonian
inequalities, and the complete twisted endpoints. Use it and a cyclic
relabeling to orient the chosen turn as required by the corresponding
continuation theorem.

There are now two exhaustive possibilities.

- If the chosen smaller turn belongs to a short forward run, the
  [smaller-short period theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md)
  gives a contradiction. Its six-variable scalar domain was excluded
  by a complete 107,977-node cover with 53,989 leaves, zero pending or
  unresolved boxes, and the
  [independent source/completion audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md).
  It retains the actual exterior reverse switch and full-period
  cost/angle budget, including either bridge-diagonal sign.
- Otherwise the chosen smaller turn belongs to a nonshort forward run.
  Apply the actual same-covector
  [continuation alternative](MIXED_SMALLER_TURN_CONTINUATION.md), whose
  [interface audit](MIXED_MINIMUM_CONTINUATION_INTERFACE_AUDIT.md)
  checks this precise orientation and switch interpretation.

Thus the only remaining possibility has actual consecutive margins and
labels

\[
0(p),\quad1(b),\quad0(a),\quad2(c),\quad0(d),\quad1(r),
\]
\[
a<b,\qquad a<c\le b,\qquad p>a,\qquad d>a,\qquad r\ge a.
\tag{3}
\]

These are consecutive arcs of the original period, possibly continued
through its twisted seam. They are not assumed to form a closed
six-piece competitor.

## 4. The next actual switch has exactly two alternatives

All quantities in the continuation interface come from the same actual
primary covector. Set

\[
K=a^2+4,\quad S=a+b,\quad T=a+c,\quad Q=d^2+4,
\quad W=c+d,\quad Z=d+r,\quad Y=W^2-T^2.
\]

The incident turn norms are actual secants, central stationarity fixes
h, and exact transport gives

\[
h_d=h+vY/8,\qquad
w=\frac{uK^2+16hY+vY^2}{Q^2}.
\]

The actual first forward root at d satisfies

\[
R_d=C_d-Wv-Zw+16d h_d/Q=0.
\tag{4}
\]

The genuine switches supply the incident upper norms and incoming
missing-control inequality used by both boundary reductions. The
compact lower bound applies to inactive state margins too; with
m=2/15 it gives

\[
cd+m(c+d)\le4,\qquad dr+m(d+r)\le4.
\tag{5}
\]

These use the compact bound m on inactive margins, not the chosen
minimum a of the active-margin sequence.

Finiteness and positive durations supply the next actual switch after
arc r. Equal adjacent controls have already been merged, so its direction
is forward or reverse. The continuation theorem proves:

| Next actual switch | Necessary condition | Uniform contradiction |
| --- | --- | --- |
| Forward | \(t=(Q^2v-16h_dZ^2+wZ^4)/(r^2+4)^2\ge3/4\) | [Forward boundary endpoint exclusion](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md) |
| Reverse | \(w\le\operatorname{Sec}(a,r,d)\), with \(r^2\ge ad\) | [Reverse boundary exclusion](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) |

In the reverse case the actual next reverse centre A satisfies A>=a.
The actual turn secant on [A,d], its outgoing derivative inequality and
strict turn log-concavity give the displayed extended secant on [a,d].
The equality A=a is retained. In the forward case the actual next
switching derivative gives t>=g_r(s)>=3/4, regardless of the later
active margin s or the remaining run length.

This table refers to the first actual successor of r. Neither branch
replaces it with an arbitrary later stationary root, chooses another
costate, or prescribes how the omitted trajectory must continue.

## 5. Why the completed boundary covers exhaust those alternatives

The two boundary theorems use the scalar comparison b→b*=K/T-a along
the unique solution of (4), holding a,c,d,r and the actual incoming
secant v fixed. Its root coefficient stays strictly negative up to b*,
and its linear differential identity preserves the incident upper-norm
inequality. It also gives w*<w_actual. These are proved scalar
comparisons; the artificial boundary point need not be a trajectory.
No physical endpoint, lower incident norm, outgoing switching floor or
Casimir cap is implicitly transported to it.

At b* the central reverse factor is one. Define the **new** maximum

\[
\varepsilon'=\max\left\{
\delta_1=\frac{d-a}{a+c},\quad
\delta_2=\frac{(c+d)(d+r)}{d^2+4}-1\right\}.
\tag{6}
\]

This replaces the original three-parameter maximum; the artificial
central parameter is delta0=0. The
[hand small-parameter theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
applies directly with l0=0 and excludes epsilon'<=1/32 from the
preserved upper norm. It therefore covers original configurations in
which delta0 was maximal, including those with original delta0>1/32.
Every remaining comparison point belongs to one of the two closed
charts where l1=1 or l2=1, epsilon' in [1/32,15]. In chart 2 the retained
incoming condition gives d<=c. All maximal-parameter ties are covered.

The
[common low-a boundary theorem](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md)
excludes a<=1/2 without imposing either next-switch alternative. It
permits the forward endpoint covers to start at the closed overlap
a=1/2. Its complete two-root execution has 74,772 nodes and 37,387
excluded leaves, with zero pending or unresolved records.

For the reverse-next branch, the comparison preserves
w*<w_actual<=Sec(a,r,d). The reduced reverse necessary domain was fully
excluded by 106,134 nodes and 53,068 leaves. It imposes neither the
original Casimir cap nor any outgoing actual-norm constraint at the
artificial boundary.

For the forward-next branch, the
[concave endpoint reduction](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md)
eliminates the diagonal using (4). The transported norm is affine
strictly decreasing in w, and the squared Casimir Gamma(w) is a concave
quadratic. Thus

\[
w_*\le w_{\rm actual}\le w_{\rm cap},\qquad
\min\{\Gamma(w_*),\Gamma(w_{\rm cap})\}
\le\Gamma(w_{\rm actual})<23/125,
\tag{7}
\]

where the upper endpoint has transported next norm exactly 3/4. The
two enlarged endpoint domains were separately excluded: 37,940 nodes
and 18,971 leaves for the lower endpoint, and 60,976 nodes and 30,489
leaves for the upper endpoint. Each has zero pending or unresolved
records. This concavity argument uses the cap on the actual covector;
it does not assert that the cap is preserved by b→b*.

Each new two-root forest satisfies N=2L-2 individually. The independent
[reverse](MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md),
[common low-a](MIXED_NONSHORT_LOW_A_BOUNDARY_AUDIT.md), and
[forward endpoint](MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md) audits accept
the exact residuals, boundary domains, frozen sources and fresh replays.
The [record verifier](../explorations/mixed_nonshort_boundary_records_verify.py)
checks the retained hashes, full-root records and per-forest accounting;
all four records pass. No unfinished prefix of an older five-variable
cover is used as a mathematical premise.

Both rows of the actual-next-switch table are therefore impossible.
Together with the smaller-short contradiction, this exhausts the chosen
global minimum and contradicts the assumed M2 period. This proves the
theorem.

## 6. Boundary, seam and rank coverage

The proof uses no positive lower bound on an individual arc duration and
no bound on the length of a nonshort run. The active-margin and factor
inequalities in the scalar reductions retain unequal factors, repeated
global minima, equal adjacent-turn order, weak third-control ties and
all relevant closed comparison faces. In particular:

- Positive actual durations are obtained by deleting zero pieces before
  choosing the finite cyclic representation. Vanishing-duration
  comparison limits use analytic secant/divided-difference extensions
  and the exactly cancelled root formula. At simultaneous
  epsilon'=0 there is no positive-duration actual window; the hand
  corner controls all nearby positive epsilon' and the regular
  directional extension. No free choice of a singular root norm is
  introduced.
- Every actual state remains in the retained compact strict-star set.
  Its positive lower margin bound keeps the reconstructed denominators
  away from their excluded state-boundary singularities. Measurable or
  edge-valued controls enter through the upstream finite-representation
  theorem, not through an unproved approximation by a word catalogue.
- Cyclic continuation across the true twisted seam conjugates the same
  actual cotangent data and permutes labels/margins together. The
  orientation change is the proved physical reflection/time-reversal
  symmetry. The selected minimum, either adjacent turn and the next
  actual switch may all cross the chosen cut.
- The short-side cost and polar-angle budget is applied only to its two
  consecutive actual turn arcs. With at least six positive pieces these
  arcs are distinct and form a proper subinterval of one period, after
  moving the cut if needed; their complement has positive duration.
  Longer padded displays, including the next switch after r, may meet an
  already named cyclic index when continued through the seam. They are
  used only for necessary identities of the same actual PMP lift, so
  repeated indices impose additional equalities and cannot create a
  missing case in an enlarged scalar domain. No multi-period display is
  charged to the one-period cost or angle budget.
- No step assumes full rank of an endpoint Jacobian, inverts an endpoint
  differential, or infers descent from an unconstrained Hessian. The
  only scalar root inversion has the explicit strict sign R_u<0 in
  the continuation theorem. Rank-deficient minimizing periods are
  therefore included under the same actual-PMP premises.

These are properties of one complete minimizing period and restrictions
of its actual lift. The scalar boundary comparisons require no spliced
competitor, geometric re-eligibility assertion or endpoint correction.

## 7. Consequence for the sufficient whole-period partition

For at least six positive pieces, the five sufficient assignments are:
all reverse (R), a forbidden mixed reverse run (M3), all short forward
runs in the surviving mixed structure (M1), all forward (F), and M2.
The first four have their retained uniform exclusions, and the theorem
above supplies the fifth. The fixed classification is by complete
periods; it does not grow with the switch count or treat a short local
window inside M2 as an M1 period.

This supplies the M2 premise in
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md).
All five at-least-six-piece assignments are excluded, so the already
audited terminal cost/equality argument applies to the remaining
at-most-five-piece minimizing representation. The external
geometric/compact/PMP inputs, arithmetic execution trust boundary and
deferred Lean verification remain explicit in that final assembly.
