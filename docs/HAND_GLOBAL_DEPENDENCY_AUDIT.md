# Hand-only global dependency review and conditional assembly

Date: 2026-11-07. Internal mathematical dependency review of the hand
route at commit `ea21d7a7bb268d99545f240a668bb9b1ddcfaf2a`, with the new
[terminal hand count](HAND_TERMINAL_COVERAGE.md). No Lean, Lake,
typechecking, CI, interval replay or executable sign check was run for
this review.

**Scope.** The global reduction, finite-before-normal ordering,
whole-period interfaces, terminal classification and affine transport
can be assembled using hand arguments and explicitly named external
geometric/PMP results. The two pending mixed exclusions remain genuine
mathematical premises: H-S and the forward-successor part of H-N.
This review does not close them or relabel the earlier computational
assembly as a proof without computer assistance. Gate H-A remains open
until their complete proofs and actual-period interfaces are reviewed.

## 1. What is asserted conditionally

Write

\[
\delta_{\mathrm{oct}}
 =\frac{8-4\sqrt2-\log2}{2\sqrt2-1},\qquad
A_{\mathrm{oct}}=\sqrt{12}\,\delta_{\mathrm{oct}}.
\]

The remaining sufficient hand statements are the following.

- **H-S.** At a globally smallest active reverse-centre margin of any
  actual competitive finite normal mixed minimizing period with at
  least six pieces, the chosen smaller adjacent turn cannot belong to
  a short forward run.
- **H-N-F.** In the corresponding smaller-nonshort assignment, the
  actual next switch cannot be forward. The reverse next-switch
  alternative is already excluded by
  [MIXED_NONSHORT_REVERSE_HAND_EXCLUSION](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md).

Each statement must include equal smaller-turn choices, unequal
positive factors, the genuine incoming and outgoing switches, the
original common covector, and the original complete-period cost cap.
The scalar domains may be enlarged for a contradiction, but no
artificial comparison point acquires an unproved physical closure,
Hamiltonian inequality or Casimir cap.

If these two statements are proved by hand with that scope, the
retained chain yields

\[
C\ge A_{\mathrm{oct}}
\]

for every original integral-form admissible competitor, and
\(\delta(K)\ge\delta_{\mathrm{oct}}\) for every centrally symmetric
planar convex disk, with equality precisely for invertible affine
images of the concrete smoothed octagon.

The following sections verify this implication and identify its exact
external boundary. They do not claim its two pending premises.

## 2. The original competitor class and the disk retained for equality

[ADMISSIBLE_REALIZATION](ADMISSIBLE_REALIZATION.md) realizes any chosen
normalized geometric worst disk with its actual boundary and physical
area cost. [REVERSE_COMPARISON](REVERSE_COMPARISON.md) applies to every
trajectory in the integral admissible class, including measurable
controls. Below pi it reconstructs a balanced disk with equal area;
above that threshold the explicit octagon already supplies the needed
comparison. Thus the retained geometric realization is a global control
minimizer against the whole original class.

This is the correct quantifier order. Subsequent finite-representation
and PMP arguments concern actual minimizers, rather than every
competitor. Once such a minimizer has cost exactly
\(A_{\mathrm{oct}}\), its minimizing property gives the cost bound for
all competitors directly. There is no unproved density of finite words,
limiting local-replacement procedure, or assumption that every arbitrary
control carries a Pontryagin lift.

For the equality statement, choose the realization of the **given**
equality disk and carry it through the same chain. Replacing it by
another convenient minimizer would not identify that given disk.
The retained realization and affine boundary transport avoid that gap.

## 3. Finite representation precedes normality

The hand route must use the following order.

| Step | Hand input and scope |
| --- | --- |
| Common compact strict-star state domain | [COMPACT_DOMAIN_SOURCE_AUDIT](COMPACT_DOMAIN_SOURCE_AUDIT.md), using the earlier geometric area bound of Hales--Vajjha Theorem 5.0.6. The estimate applies at every point of the same balanced realization and bounds inactive as well as active margins. |
| Actual free-time Pontryagin lift | [GLOBAL_PERIODIC_PMP, Sections 1--3](GLOBAL_PERIODIC_PMP.md). Free initial state and both twisted cotangent endpoints are retained; normality is not presumed. |
| Positive singular clearance | [SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md). The pointwise clearance follows from the complete-period endpoint and cost budget for unit-normalized lifts, including abnormal lifts. |
| Measurable edge restriction | [MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md). A separate fixed-endpoint edge PMP and an integrating factor give at most four vertex pieces on every missing-control interval. |
| Finite vertex representation | [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md), with the preceding clearance and edge property. This is a hand guard/count argument for arbitrary measurable controls. |
| Normality of that same period | [GLOBAL_NORMALITY, Sections 1--6](GLOBAL_NORMALITY.md). The finite representation is now available; a combinatorial same-covector contradiction excludes an abnormal lift and allows positive rescaling to the physical normalization. |

The finite count's large constants do not constitute computer
assistance. Their bounds are displayed elementary inequalities. For
example the budget margin uses three positive terms of the logarithm
series, rational bounds on square roots, and an integrated form of
Machin's identity. No numerical root isolation or interval cover is
needed to conclude finiteness.

The measurable-edge proof is also explicit: after the increasing
abscissa change, it minimizes \(\int x^2w(x)\,dx\) with
\(w'=\beta_vw\), \(s'=w\), and fixed endpoint data. Its transformed
switching covector satisfies

\[
(\rho p_w)'=-\rho(p_s+\lambda x^2),\qquad\rho>0.
\]

The derivative has at most two zeros unless its quadratic is identically
zero. Rolle's theorem, with the nontriviality case treated separately,
gives at most three switching zeros and hence four pieces. That proof
uses the local optimality of the actual restriction and permits all
original measurable edge controls.

The quantitative count then uses this edge property, explicit
coercivity of the switch comparisons, and singular clearance. The
published finite bang-bang theorem and its later numerical
escape/basin analysis are not imported. In particular, the historical
qualitative singular-avoidance discussion in
`GLOBAL_MINIMIZER_COMPACTNESS` is not a substitute for the active
clearance proof. Only its common state bounds and, if used, its
projective compactness section belong to this route.

Deletion of zero-duration pieces, merging of equal neighbors, and
changes on null sets preserve the same actual state, frame, cost and
boundary. They do not create a new candidate minimizer whose equality
properties would have to be transported separately.

## 4. The complete-period exclusions have the correct scope

For an actual finite positive normal representation with at least six
pieces, the following partition is sufficient.

| Assignment | Hand status and role |
| --- | --- |
| Entirely reverse | [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) applies at a cyclic minimum and excludes every length. |
| Mixed with a reverse run other than length two | [MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md) excludes it by the reverse four-arc obstruction and strict three-arc log-concavity. |
| Mixed with all forward runs of length one | The two-centre cost argument in [MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md) and the angle contradiction in [MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) supply a uniform hand exclusion. |
| Entirely forward | [HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md), with its scalar norm proofs, excludes every eligible length at least six. |
| Mixed with a nonshort forward run | Choose the smaller adjacent turn at a global minimum reverse centre. H-S or H-N applies according to its actual run; H-N splits by the actual successor sign. H-S and H-N-F remain open at the reviewed head. |

The all-forward application is genuinely a whole-period argument.
Its twist gives \(N\equiv1\pmod3\), so \(N\ge6\) implies
\(N\ge7\). The seven budget indices used by the proof are distinct
at the smallest possible length. The scalar row retains both genuine
exterior missing-control floors and the same normal covector. The
proved norm bounds give
\(\gamma^2>23/125\), contradicting the sharper whole-period cap
\(\gamma^2<9193/50000\). The former neighbor and Casimir covers
are not used. The hard small-forward-minimum face is replaced by
[SMALL_FORWARD_MINIMUM_HAND_PROOF](SMALL_FORWARD_MINIMUM_HAND_PROOF.md).

For mixed periods, the margin minimum lies at a reverse centre:
the minimum-structure theorem allows either that pattern or a
four-forward-switch minimum; the reverse-centre scale bound makes
some reverse centre smaller than the range allowed by the completed
small-forward-minimum hand theorem. This argument uses the minimum
of one finite cyclic sequence and works through the actual twist.

The choice of smaller turn is exhaustive even at a tie. Reflection
combined with reversal of time is the proved symmetry in Sections 1--3
of `MIXED_GLOBAL_MINIMUM_STRUCTURE`; it preserves the physical cost,
normal multiplier and all endpoints. Formal reversal of a control
word alone would be insufficient.

The direct smaller-turn split does not need the separate claim that
at least one neighboring forward run is nonshort before making the
split. If both are short, the H-S hypotheses still hold. Therefore the
large coefficient tables in the historical short-bridge minimum
exclusion need not be premises of the hand assembly, as already
recognized in [HAND_REDUCTION_REVIEW](HAND_REDUCTION_REVIEW.md).
The elementary actual short-bridge secant and outer-root facts are
still required and are not removed by that pruning.

The reverse-successor proof supplies a uniform scalar contradiction
with all three lower-shape cases, including weak ties and its scale
face. Its internal coefficient identities are accompanied by explicit
hand bounds. This review accepts its role in the whole-period
implication, as detailed by
[MIXED_NONSHORT_REVERSE_HAND_AUDIT](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md).
It does not infer the unproved forward-successor conclusion from that
reverse result or from the newly proved common order of margins.

## 5. Terminal coverage has a direct hand proof

[HAND_TERMINAL_COVERAGE](HAND_TERMINAL_COVERAGE.md) removes any need
for a terminal word enumerator. At a genuine cut the labels satisfy
\(i_{j+N}=i_j+1\pmod3\), hence
\(\sum\epsilon_j\equiv1\pmod3\).

For \(N\le5\), the entirely reverse case is excluded by R. An
all-forward word has \(N=1\) or \(4\); the fixed-edge frame
obstruction removes \(1\), leaving `0120`. In a mixed word, if there
are \(m\) reverse runs and \(F\) forward switches, then
\(N=2m+F\ge3m\). Thus \(m=1\), and the same congruence gives
\(F=3\), \(N=5\), with representative `01020`. Both R and the
reverse-run theorem have no hypothesis \(N\ge6\), so their use here
is legitimate.

The terminal analytic formulas are already displayed in
[SMALL_PERIOD_COST_EQUALITY_AUDIT, Sections 2--3](SMALL_PERIOD_COST_EQUALITY_AUDIT.md).
The four-piece factor symmetry is derived from tangent closure, and
the initial state is forced by the state endpoint. Its strict
asymmetric derivative/integral comparison singles out the four
factors \(\sqrt2\). For the five-piece mixed representative, the
strictly concave logarithmic envelope and the positive middle-duration
inequality give a strict cost excess. The possible zero-middle-duration
equality limit belongs to the four-piece case after deletion.

These are hand algebra and calculus arguments. Companion symbolic
scripts verify their identities but are not indispensable premises.
The separate arbitrary-trajectory reverse-five comparison is also
unnecessary: the terminal theorem classifies actual normal minimizers,
which R already excludes in that orientation.

## 6. Cost and affine equality after the pending premises close

Once H-S and H-N-F close, Section 4 excludes every actual minimizing
representation with at least six pieces. Section 5 then makes its
cost exactly \(A_{\mathrm{oct}}\). The minimizing comparison in
Section 2 proves the unrestricted inequality directly.

For an original equality disk, retain its realization, initial linear
normalization \(e\), rebase cut \(s\), and cyclic relabeling matrix
\(C=R^r\). The classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

The four-piece equality factors and forced initial state determine
every physical duration and every constant-control flow. ODE uniqueness
therefore identifies the entire state and frame with the explicit
octagon. Its six cyclic contact arcs give the boundary of the retained
disk, yielding

\[
K=e^{-1}G(s)C(K_{\mathrm{oct}}).
\]

The matrix is invertible. Restoring the original centre permits a
translation. Conversely a linear map gives a bijection between lattice
packings and scales disk area and lattice covolume equally; greatest
lattice density is affine invariant. Fejes Toth's equality of greatest
and lattice density for this centrally symmetric planar class gives
the converse equality statement. It is not necessary to assert that
an affine map preserves general rotated congruent packings.

## 7. External inputs and acceptance boundary

The retained external inputs are the classical planar convex-disk
existence, regularity, balanced-normalization and critical-hexagon
facts; Fejes Toth's packing-density theorem; the earlier geometric
area lower bound; standard Pontryagin principles; and standard ODE,
absolute-continuity and elementary calculus results. Their references
and normalizations are listed in
[GLOBAL_COST_EQUALITY_ASSEMBLY, Section 7](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
and [COMPACT_DOMAIN_SOURCE_AUDIT](COMPACT_DOMAIN_SOURCE_AUDIT.md).
The source statements of the packing-density theorem and the
geometric area bound were checked against Hales--Vajjha,
[*Packings of Smoothed Polygons*, Chapters 2 and 5](https://arxiv.org/html/2405.04331v1).
No later computer-assisted chattering or basin theorem is a premise.

The active hand ledger must therefore continue to distinguish:

- a completed computational baseline;
- proved hand foundations, H-F and the reverse part of H-N;
- the two outstanding mixed hand exclusions; and
- the final acceptance of their complete actual-period interfaces.

At the reviewed head, no further indispensable executable exclusion was
identified outside the two outstanding mixed tasks. This is a review
of the stated dependency spine and its quantifiers; it is not a claim
that every historical document has been re-proved, or that the pending
mixed signs follow automatically. In particular, the physical cost
comparison under the short scale deformation and the remaining
forward Casimir signs cannot be supplied by the older certificates
when declaring a proof without computer assistance.
