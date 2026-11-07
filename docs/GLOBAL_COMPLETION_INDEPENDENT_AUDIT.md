# Independent audit of the final cost and equality dependency chain

Date: 2026-11-07. Internal mathematical review. No Lean, Lake,
typechecking or CI.

**Current acceptance boundary:** the final assembly is valid conditional
on completion of both smaller-nonshort continuation covers and their
final source/interface review. The smaller-short branch, the terminal
through-five comparison and the affine equality transport have the
required scope. This document does not yet close M2 or assert the
unrestricted inequality.

The proposed final implication is
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

The retained external geometric inputs are worst-disk existence,
balanced-boundary regularity and normalization, the balanced area/density
identity, and the compact-domain theorem. The last is Hales--Vajjha,
[*Packings of Smoothed Polygons*, Theorem 5.0.2](https://arxiv.org/html/2405.04331v1#Ch5),
with the domain in Definition 5.0.1. Its stated scope is a balanced disk
whose boundary trajectory is competitive with the octagon; it does not
assume finitely many controls. That is exactly the minimizing
realization used in the assembly. Ordinary endpoint-submanifold and
fixed-time Pontryagin principles are the other external analytic inputs.

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
merging, the actual finite period has positive vertex pieces. Its sign
sequence is cyclic even though its labels repeat with the prescribed
shift. The sufficient partition in the final assembly exhausts this
cyclic sign sequence.

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

In a remaining mixed period, the small-forward-minimum theorem forces a
global minimum to be a reverse centre. Choose either smaller adjacent
turn, including equality. Its adjacent forward run is short or nonshort.
The completed [smaller-short theorem](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md)
excludes the first possibility. The other gives exactly the nonshort
same-lift data and next-actual-switch alternatives of
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
This does not assume that both sides of the minimum belong to long runs.

The finite bound is used to choose a global margin minimum and to justify
the cyclic partition. No catalogue up to that bound is part of the
proof. Rank defects cause no omitted case in the first-order scalar
reductions, since no endpoint Jacobian is inverted to choose a new
costate.

## 5. Boundary coverage and the current certificate boundary

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

The nonshort corner `epsilon<=1/32` is excluded by the hand theorem
[MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md),
which keeps the entire shape fibre and proves a positive cleared
residual margin. The complementary region must still be covered in
**both** next-switch branches by the final reviewed source. The current
nonshort [source/interface audit](MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md)
is a pending-cover record. No incomplete run, sampled probe or heuristic
LP result supplies the missing conclusion.

Directed-interval conclusions have an explicit MPFR/GMP/compiler trust
boundary. Native floating-point calculations only propose nonnegative
dyadic weights or choose subdivisions; a new outward-rounded bound
must verify every rejection. These are computer-assisted hand
certificates, not Lean kernel proofs. Source hashes and complete
successful replay records must correspond to the final accepted
mathematical domains.

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

The equality argument retains the realization of the given minimizing
disk. It does not replace that disk by a different minimizer having the
same cost. At the four-piece equality parameters, the initial state and
each physical duration agree with the concrete octagon. Successive
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
original centre permits a translation. Conversely affine invariance of
greatest packing density in the centrally symmetric convex class gives
equality for every affine octagon. Thus the terminal theorem has both
directions of the requested affine equality classification.

## 7. Audit conclusion

No additional normalization, endpoint, measurable-control, case-partition
or equality-transport gap was found in this dependency review. The
conditional final assembly has the correct logical form: classify actual
global minimizers, then use their minimizing property for all competitors
and their retained contact boundary for equality rigidity.

The remaining acceptance condition is concrete: complete and audit the
two complementary smaller-nonshort covers for their frozen final source.
Until that condition is met, this document does not mark the unrestricted
Reinhardt cost inequality or affine uniqueness proved. It also makes no
claim that the existing Lean source drafts elaborate or pass the kernel.
