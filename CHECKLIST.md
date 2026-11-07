# Proof ledger: global reduction before a fixed finite comparison

**NEXT WORKER: [GLOBAL REDUCTION PLAN](docs/GLOBAL_REDUCTION_PLAN.md).**

**NEW ACTIVE CASE ROADMAP:** [FINITE_CASE_COMPUTER_ROADMAP](docs/FINITE_CASE_COMPUTER_ROADMAP.md)
replaces impractical whole-word enumeration by five complete-period
PMP exclusion cases F=012012, R=021021, M1=021210,
M2=010201, M3=021012. For each, the finite A/B/C gates are:
reproducible necessary-condition screening, full-period continuation and
fate classification, and a universal hand certificate. **R and M3 are
CLOSED; F, M1 and M2 remain OPEN.**
[GLOBAL_REVERSE_PERIOD_EXCLUSION](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
and its [independent audit](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION_AUDIT.md)
exclude every entirely reverse finite PMP period by a minimum-active-
margin argument. The 20-identity checker passes. No equal-factor, rank,
Casimir-sector, cost-budget or transverse-switch hypothesis is used.
[MIXED_GLOBAL_MINIMUM_STRUCTURE](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
and its independent audit also exclude every bounded reverse run of
length at least three, closing M3. Every surviving mixed reverse run has
exactly two switches and a strict central margin minimum. Numerical checks in
[CASE_ATLAS_EXPERIMENT_001](docs/CASE_ATLAS_EXPERIMENT_001.md) verify the
oracle on known stationary and regular families. The curved
closed-period Hessian gives numerical negative indices 0,2,4 for
N=4,7,10; this reproduces already known examples and does not prove
an asymmetric-family index bound. The case domains retain
triple/cubic ties, vanishing factors, rank drops, and whole-period
cost budget. [GLOBAL_NORMALITY](docs/GLOBAL_NORMALITY.md) has now passed
an [independent internal hand audit](docs/GLOBAL_NORMALITY_AUDIT.md): every
finite twisted closed PMP lift is normal, without a local rank or
transverse-switch assumption. Existing finite representation applies this
to every global minimizer. The normality part of T is complete.
[NORMAL_TIE_BRANCHING](docs/NORMAL_TIE_BRANCHING.md) and its
[independent internal audit](docs/NORMAL_TIE_BRANCHING_AUDIT.md) give exact
necessary-and-sufficient outgoing positive-vertex tests through derivative
order three, including normal triple and cubic ties. This closes the
local branch rule, not the global fate of every passing branch. The
separate minimum principles close R and M3; three C gates remain open. Compactness also gives
a qualitative positive lower bound on -lambda in the initial unit
normalization, hence a compact family after normalization to lambda=-1.
No numerical value for this new bound is claimed.


## Active global checkpoint

The strongest complete-period bounds are now

\[
\boxed{D>10^{-11},\qquad N<10^{56}.}
\]

The clearance holds for every competitive complete-period PMP lift in the
common cyclically invariant state domain, with
`norm((lambda,Lambda_1,W)(0))=1`. The direct measurable-edge proof of (E4)
then gives the count for every actual global minimizer. The retained inputs
are the geometric/control correspondence, the common state domain, and
standard PMP. Normal and abnormal lifts are included; no prior finite
vertex representation or minimum arc duration is assumed.

| Global gate | Exact result | Status |
| --- | --- | --- |
| G1: full-period domain and compact lifts | Actual twisted state/costate closure; projective normalization including abnormal limits; common state bounds and compactness. | **Hand proof complete under the stated inputs.** [PMP interface](docs/GLOBAL_PERIODIC_PMP.md), [compactness](docs/GLOBAL_MINIMIZER_COMPACTNESS.md). |
| G2: singular clearance | Every normalized competitive closed lift in the common domain has `D>10^-11` at every time. | **Explicit hand proof complete.** [SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md), with a direct homogeneous estimate covering every costate component. |
| G3: uniform switch count | Every global minimizer has fewer than `10^56` positive vertex pieces. | **Specific integer proved.** The [quantitative theorem](docs/QUANTITATIVE_REGULAR_SWITCH_BOUND.md) uses `m=10^-8`, `M=10^8`, and the [direct edge proof](docs/MEASURABLE_EDGE_PMP_BOUND.md). |
| G4: global cost comparison and equality | Prove the octagon comparison and affine equality case for the bounded class, or a stronger structural reduction. | **Open.** The ceiling is not a practical catalogue. Through-five comparison/equality are retained; `N<=5` and unrestricted rigidity remain open. |

**Direct whole-period bridge:** let `A=Lambda_1-(3/2)*lambda*J`. Every
closed lift of cost `C<pi` satisfies
`norm(A(t)) >= abs(lambda)*3*(pi-C)/(2*pi-C)` at every time. The proof uses
an interior equilibrium control, spatial costate conservation, the exact
frame endpoint, and rebasing of the same twisted lift. On the minimizer
state domain, Hamiltonian width and positive equilibrium weights also give
`norm(W)<=10^6*norm(A)` and `10^-8<norm(P)<10^8`. These are explicit
algebraic improvements over the earlier Gronwall estimates.

**Direct E4 proof:** [MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md)
uses a separate two-state, fixed-time edge PMP. A positive integrating
factor makes the switching derivative a positive factor times a quadratic,
so at most three switches occur. The identically zero polynomial and all
abnormal cases are treated. The exact change of parameter preserves both
physical endpoints and the free-duration cost comparison.

**Preserved concurrent result:** [GLOBAL_COST_CASIMIR](docs/GLOBAL_COST_CASIMIR.md)
and [GLOBAL_NUMERICAL_REDUCTION](docs/GLOBAL_NUMERICAL_REDUCTION.md) prove
an independent normal-component estimate, `D>10^-1906`, and `N<10^5741`.
Their proof and the small/large-multiplier and determinant-sector bounds
remain intact. The new homogeneous proof improves the universal constants.

**Source boundary:** the active route needs neither Hales--Vajjha Theorem
8.1.4 nor Theorem 16.3.1. The earlier qualitative route and numerical
source audit remain recorded in
[FINITE_BANG_BANG_SOURCE_AUDIT](docs/FINITE_BANG_BANG_SOURCE_AUDIT.md).
Those source calculations have not been independently certified here.

**Actual global exclusion:** [GLOBAL_PERIOD_BUDGET](docs/GLOBAL_PERIOD_BUDGET.md)
excludes every small-core padded L3 window in `0<b<=1/(10000*sqrt(3))`
from any closed twisted-periodic PMP extremal by a finite escape test.
Their fixed-endpoint global optimality remains true; the full L3 parameter
domain is not excluded. The new
[MIXED_GLOBAL_SYMMETRIC_ESCAPE](docs/MIXED_GLOBAL_SYMMETRIC_ESCAPE.md)
excludes the full symmetric equal-factor reverse-four core domain
`1<h<2, 0<v<3`, with any positive incoming control-0 pad and outgoing
control-0 factor at least `h`. A complete-period Casimir obstruction
or postcritical finite escape covers every point of that domain. The
[independent audit](docs/MIXED_GLOBAL_SYMMETRIC_AUDIT.md) and 146 exact
algebra/sign checks passed. Asymmetric cores and shorter outgoing pads
are outside the theorem; the M1 case-C gate remains open.
[MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION](docs/MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md)
certifies an asymmetric local normal PMP window with a subcritical
negative-elliptic Casimir and low local cost whose outgoing 0 arc returns
before the postcritical point, at factor in `(251/250,201/200)`. Thus the
listed local first-order tests cannot force sufficient padding. No true
first external switch, geometric eligibility, full-period closure or
minimality is claimed; the revised complete-switch target remains open.

[VERTEX_INSERTION_OBSTRUCTION](docs/VERTEX_INSERTION_OBSTRUCTION.md)
refutes one proposed G4 shortcut: the all-reverse admissible class has
trajectories approaching the octagon cost. The proof is a general
endpoint-rank insertion theorem and an exact rank-five check at the
octagon, not a longer-word enumeration. It refutes C>=pi and any uniform
positive gap above A_oct on that class, without producing a PMP trajectory
or a cost below A_oct. G4 retains optimality and boundary constraints.

[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md)
and its [independent audit](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_AUDIT.md)
exclude the closed positive elliptic primary-costate cone, including zero
and its positive parabolic boundary, for whole pure-forward/reverse
normal periods with arbitrary unequal factors. Hyperbolic, negative
parabolic and negative elliptic alternatives remain. The strict action
derivatives are not constrained descent. The sector theorem itself
closes neither F nor R; R is now closed by the separate minimum-margin
PMP contradiction.
[REVERSE_PERIOD_CASIMIR_REDUCTION](docs/REVERSE_PERIOD_CASIMIR_REDUCTION.md)
shows the individual trace inequality supplies an upper Casimir bound.
It cannot be reversed into the needed lower bound; arbitrary unequal
periods were not resolved by that route. The new minimum-margin proof
closes R without that lower bound; the retained regular-family strict
lower bound is no additional competitor exclusion.

The later [GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](docs/GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
and its independent audit now remove the nonelliptic alternatives for
whole pure-forward periods as well. Every such normal lift has negative
elliptic primary costate. This makes the complete-period Casimir bound
available throughout F, but closes no further case-C gate.

No completed unrestricted cost comparison, affine uniqueness theorem, or
kernel validation is claimed.

**Next-gate sharpness check:** [GLOBAL_COST_CASIMIR, Section 6](docs/GLOBAL_COST_CASIMIR.md#6-exact-defect-and-equality-in-the-cost--casimir-bound)
now gives the exact three-term nonnegative defect and proves equality only
for the normal centroid-controlled circle, whose cost is pi. This does not
settle octagon equality. Explicit strictly subcritical local PMP phases
admit either switching direction, and another gives a genuine cubic reverse
switch. Neither has a claimed full-period closure or minimizing property.
Thus the new determinant gap does not justify a forward-only or simple-switch
assumption in G4. The bounded global variation investigation has not produced
a general negative direction or any additional global cost exclusion.

## Historical local package and preserved diagnostics

**P0 is complete at the hand-proof level:** see
[the minimizer-window audit](docs/MINIMIZER_WINDOW_AUDIT.md) for finiteness,
twisted rebasing, normalized sectors, and the finite-piece geometric splice.
**The original L3 lemma is refuted:**
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
constructs eligible `021210` windows with no cheaper replacement among all
measurable simplex controls, with free terminal time. Its additional input
is the explicitly checked ASZ sufficient-optimality theorem; the separate
six-piece proof is self-contained. The revised necessary domains below retain
the same five templates; all five strict-improvement premises are open.
**No new whole-word enumeration. Universal analytic exclusions proved: 0/5.**

Status date: **2026-11-07**. New Lean infrastructure, compilation, Lake, and CI remain paused.

The user requested a bounded set of cases before further enumeration. This ledger
therefore supersedes the earlier next-six/next-seven progression. The full prior
ledger and chronological source history remain at
[798a7e1](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/CHECKLIST.md).
No mathematical proof file or earlier contribution has been removed.

## The earlier local coverage checkpoint

**Prove a uniform bound on the complexity of every global minimizer before
expanding whole-trajectory case coverage.** A finite list of open lemmas is not
itself such a bound.

The original package in [docs/BOUNDED_REDUCTION.md](docs/BOUNDED_REDUCTION.md)
has a proved coverage argument, four open analytic inputs, and one refuted
sufficient input. It cannot be proved as stated.

The concurrent revised local candidate is
[SWITCH_COMPLETE_REDUCTION](docs/SWITCH_COMPLETE_REDUCTION.md). It defines
five explicit domains requiring one nontrivial whole-window PMP lift and
inactive ties at both external switches. Every selected minimizing window
belongs to one of these domains; improvement on all five still implies
N<=5 by the P0 splice. This necessary-domain and conditional-implication
proof is complete. **All five revised analytic targets remain open.**
It is retained alongside the active global compactness/count route above.

A proved necessary restriction is now available:
[MINIMIZER_WINDOW_PMP](docs/MINIMIZER_WINDOW_PMP.md) requires an inactive
Hamiltonian tie at both ends of a window of six complete pieces. Endpoint
rank makes the adjoint unique at the exact L1 input and throughout the
displayed sufficiently small padded L3 family. Both have strictly unique
active controls at the external cuts, so neither can be a selected complete
minimizer window. This does not rule out arbitrary cuts through longer arcs
or prove improvement on the remaining domain.

For L1, [LOCAL_FORWARD_ENDPOINT_FILTER](docs/LOCAL_FORWARD_ENDPOINT_FILTER.md)
expresses the four inactive gaps through two scalar boundary residuals and
one three-dimensional linear solve. Each residual must be an endpoint of
an explicit nonnegative interval. The same note proves a five-dimensional
family of asymmetric eligible local-PMP windows passing both external ties;
the filter does not force equal factors or a globally competitive extension.

| Component | Exact completion condition | Status |
| --- | --- | --- |
| P0: minimizer eligibility and splice | Prove every selected window meets the entire stated domain and every cheaper finite strict-star splice gives a geometric competitor. | **Hand proof complete**, using the named published reduction and retained through-five comparison certificates. Does not exclude a new cost class. |
| Coverage | Every cyclically reduced minimizing word with N>=6 contains one of the five specified six-arc windows, using the established forward-alternation exclusion. | Hand proof independently reviewed, with a separate finite-graph computational cross-check. No new cost class excluded by this alone. |
| L1: 012012 | Strictly cheaper endpoint-preserving replacement on the entire eligible local domain. | **Open.** An exact eligible stationary minimum disproves universal nearby same-word descent; different-word or nonlocal improvements remain possible. See [LOCAL_FORWARD_SIX](docs/LOCAL_FORWARD_SIX.md). |
| L2: 021021 | Same universal local improvement for five consecutive reverse switches. | **Open.** An exact rank-four positive-star input exists, but its cost exceeds pi; rank on the competitive sublevel remains unresolved. See LOCAL_L2_RANK_DROP. The existing regular subfamily does not cover asymmetric local endpoints. |
| L3: 021210 | Same universal local improvement for a single forward switch between two reverse pairs. | **Refuted even with arbitrary measurable replacements.** Eligible arbitrarily cheap windows are global minima for their fixed endpoints, with free terminal time. See [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md). No closed-minimizer embedding is asserted. |
| L4: 010201 | Same universal local improvement at a reverse run of length two followed by at least two forward switches. | **Open.** Full-domain endpoint rank five is proved. An exact eligible stationary family has all five compensated missing-control switch needles positive; that switch-only shortcut is false. See [LOCAL_SIX_VARIATION](docs/LOCAL_SIX_VARIATION.md). |
| L5: 021012 | Same universal local improvement at a reverse run of at least three followed by at least two forward switches. | **Open.** Full endpoint rank five is proved throughout the positive strict-star domain; its first five factor columns already suffice. See LOCAL_L5_ENDPOINT_RANK. |
| Revised five-target package | Restrict each input to the explicit complete-switch PMP domain, retaining abnormal alternatives where rank is unresolved. | Necessary membership and conditional sufficiency proved in SWITCH_COMPLETE_REDUCTION. All five revised improvement targets are open. |
| Bound of five | Deduce N<=5 for every global minimizer from valid local improvements and the published finite bang-bang reduction. | Conditional implication proved for the revised domains; its five analytic premises are open. No unconditional N<=5 theorem. |
| Global comparison and equality | Apply the existing through-five cost comparison and equality classification after the uniform bound is proved. | Conditional only. Global minimality and affine rigidity remain open. |
| Kernel validation | Compile and inspect the final statements and dependencies. | Deferred under the current workflow. |

**Analytic exclusions closed in this five-template package: 0/5.** This is a
count of precisely stated local targets, not a percentage of the conjecture
or an assertion that the targets have equal difficulty.

### Scoped local result; no full input closed

An exact [L1 obstruction](docs/LOCAL_FORWARD_SIX.md) has factors
`(11/10,11/10,121/100,121/100,11/10,121/100)` and initial margins
`sqrt(1975/1684) * (1,1,4761/3950)`. It satisfies the entire explicit
eligibility domain, including whole-arc sector inequalities. The endpoint
map has rank five, the first constrained variation is zero, and the second
is strictly greater than `1/200` on the displayed nonzero tangent. Hence it
is a strict local minimum on the same-word endpoint fiber. This refutes the
universal nearby same-word approach, not L1's broader replacement claim.

The [complete needle audit](docs/LOCAL_FORWARD_NEEDLE_AUDIT.md) strengthens
this to a strict strong local minimum in the augmented normalized free-log-time
formulation. All twelve nonactive full-arc gaps are positive in the interiors;
the external endpoints have unique active maximizers and all internal switches
are simple and transverse. The checked ASZ theorem rules out every sufficiently
nearby arbitrary-control improvement. This is compatible with the following
distant replacement.

For that exact input, [a different-word hand certificate](docs/LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md)
now constructs a strictly cheaper six-piece `012021` replacement. A rational
contraction ball proves exact endpoint equality, and rational logarithm
bounds prove a normalized cost decrease greater than `1/100000`. This is
one resolved explicit test input, not a full-domain L1 exclusion.

The independent appendix gives a second exact slice for the same source,
checked with standard-library Fraction arithmetic. The implicit function
theorem continues either construction to nearby eligible inputs; no radius
or coverage of the rest of the L1 domain is claimed.

[LOCAL_FORWARD_RANK](docs/LOCAL_FORWARD_RANK.md) proves that the full L1
endpoint map has rank five on its entire positive strict-star domain,
for every initial state and all six unequal factors. Active-margin
coordinates resolve the state endpoints; four explicit negative determinant
terms prove the remaining rank-three assertion. This removes every interior
singular-rank exception for L1. It supplies no cost exclusion and no uniform
conditioning estimate at the boundary; the stationary minimum above remains.

[LOCAL_FORWARD_PMP_LIMIT](docs/LOCAL_FORWARD_PMP_LIMIT.md) deduces normality
and uniqueness of the normalized adjoint from this rank theorem. It also
exhibits eligible six-windows of the existing standard forward polygons
with full PMP, transverse switches, and a twisted periodic extension; their
local costs tend to zero. Their displayed full periods exceed the octagon
cost. Thus local first-order PMP plus unrestricted periodic extendibility
cannot close L1; the total minimizing-period budget remains a distinct
possible input. No new closed family or uniform bound is asserted.

[LOCAL_FORWARD_REGULAR_DESCENT](docs/LOCAL_FORWARD_REGULAR_DESCENT.md) now
proves a same-word six-piece improvement for every state-cyclic forward
reference with `1<q<=5/4`, `a^2=4q/(4-q)`, and initial margins
`(a,a*(2/q-1),a)`. The exact constrained Hessian is strictly negative;
the rank theorem integrates its direction to the full endpoint fiber.
The improvement persists on an unspecified open neighborhood of each
reference, including unequal factors. This covers the existing standard
complete-switch windows `q_k=2*cos(pi*k/(3k+1))`, `k>=2`, and nearby inputs.
It does not cover all asymmetric L1 inputs or close its universal target.
The standard global family was already cost-excluded; this is a scoped
local exclusion and second-variation certificate, not a new global family.
Independent hand reviews passed; no numerical neighborhood radius or
uniform boundary estimate as q tends to one is asserted.

[LOCAL_REVERSE_SIX](docs/LOCAL_REVERSE_SIX.md) proves a strict local improvement
for every equal factor q>1 in the reverse state-cyclic family with initial
margins 2(1,1,2q-1)/sqrt(4q-1). An inserted missing-control arc, together with
five corrected original factors, gives an actual seven-piece competitor with
exactly the same frame and state endpoints. A normalized endpoint minor is
nonzero for all q>1; an elementary logarithm inequality proves strict descent.
The correction size and cost decrease need not be uniform as q approaches one.

This is a proper one-parameter subfamily of L2 and uses seven replacement
pieces. It does not prove the current at-most-six L2 target, its full-domain
seven-piece variant, or a uniform bound. A universal strict improvement with
any finite replacement count would still contradict global minimality; the
number of pieces in a competitor need not decrease for that contradiction.

[LOCAL_L3_STRONG_MINIMUM](docs/LOCAL_L3_STRONG_MINIMUM.md) gives an eligible
`021210` window with every factor `5/4` and initial margins
`sqrt(448/803) * (1,2,193/112)`. Its positive constrained Hessian, strict
full-arc Hamiltonian inequalities, and transverse switches meet the
published sufficient-optimality theorem after the explicitly justified
free-time augmentation. It is a strict strong local minimum in the normalized
free-log-time formulation, including its duration coordinate. Thus nearby
same-word or arbitrary-control improvements cannot handle every L3 input.
This is a local-method obstruction: no quantitative radius or global
comparison excludes a distant cheaper replacement for that explicit example.
The separate small-window theorem below refutes the original universal L3 target.

[LOCAL_REVERSE_SIX_OBSTRUCTION](docs/LOCAL_REVERSE_SIX_OBSTRUCTION.md)
supplies that counterexample without an optimal-control sufficiency theorem.
A scaled reverse-four core has an exact edge dual and positive interior
third-control gaps. After adding two small positive control-0 arcs,
compactness and endpoint normal coordinates force every cheaper competitor
with at most six pieces to use the same word. A five-coordinate local inverse
then fixes both padding arcs and the core endpoints; the exact edge lower
bound rules out cheapness. Full-arc star and sector eligibility are proved.
Independent hand review passed. This particular proof stops at six pieces.

[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
removes that restriction. The same family's fixed positive-pad extension
meets ASZ Theorem 2.6 after an explicit state-only clock and free-duration
augmentation. Arbitrary cheaper competitors for shrinking pads converge to
the unique edge core. Splicing them into that one fixed extension contradicts
its strong local optimality. This proves fixed-endpoint global optimality
among all measurable simplex controls, without a piece cap. Independent
reviews checked the primary theorem, its exact variation space, and every
compactness/clock/splice step. Increasing replacement counts cannot repair L3.
Global Reinhardt minimality remains open.

## What is fixed, rather than growing

[LOCAL_SIX_VARIATION](docs/LOCAL_SIX_VARIATION.md) proves full-domain L4
endpoint rank by a short paired-holonomy determinant identity. It also proves
that a negative compensated needle gives a genuine cheaper replacement.
An exact eligible stationary L4 family nevertheless has all five switch
needles strictly positive. Rational logarithm bounds and Bernstein sector
coefficients certify the signs; positive outer padding follows by the
implicit function theorem. This excludes a proposed switch-only method,
not the full L4 target or every interior-arc needle.

The labels are three control vertices. Every input template has two free
initial-state coordinates and six positive arc factors: eight real variables,
independent of the total word length. The exact domain includes whole-arc
strict-star positivity, the octagon sublevel cost, and a nonrepeating geometric
sector test. The last test reduces to finitely many quadratic inequalities.

A replacement must preserve BOTH the frame and state at both ends. It can
use at most six vertex pieces, with free elapsed time. A small same-word
variation is enough; actual six-to-five shortening is not necessary to
contradict minimality. No compactness or boundary-attainment assumption is
needed when a strict local descent is established.

All five words end in three distinct labels. Explicit positive-factor
inversion removes the three tangent-endpoint constraints, leaving two
state-endpoint equations on three variables. This is an exact fixed-size
setup, not a proof that a decreasing direction always exists. For L1, L3, L4, and L5
the reduced state rank is two everywhere by LOCAL_FORWARD_RANK,
LOCAL_MIXED_SIX_RANK, LOCAL_SIX_VARIATION, and LOCAL_L5_ENDPOINT_RANK.
Rank-zero and rank-one loci remain obligations for L2; stationary points remain part
of all five targets.

A bounded-coordinate compactification is recorded, but singular boundary
faces are NOT certified. No exhaustive interval search or uniform dwell-time
bound is claimed.

## Stop and failure rules

Do not make a seven-arc or higher closed-word list the next milestone.
Do not count the remaining closed six-arc comparison as a boundedness result.
Do not use a global closed-word deformation that changes its initial state
as a local endpoint-preserving replacement.

A case closes only with a hand proof on its entire stated domain. A proof
on a compact numerical sample box, a generic-rank argument, or successful
floating-point optimization does not close it. If a proposed sufficient
local claim is false, record the counterexample and revise the reduction;
do not conceal the failure by increasing the arc cutoff.

## Existing mathematical assets retained

The baseline hand notes supply the following results. They remain available
as inputs or checks; their preservation is not new progress in this checkpoint.

| Asset | Scope and reference |
| --- | --- |
| All descriptions with at most five positive vertex pieces | Full comparison and equality within that class: [four](docs/FOUR_LINK_HAND_PROOF.md), [five noncyclic](docs/FIVE_ARC_PROGRESS.md), [five reverse](docs/REVERSE_FIVE_ARC.md). |
| Forward four-arc alternation | Arbitrary-length local strict improvement, used in the new coverage proof: [hand argument](docs/FORWARD_ALTERNATION_EXCLUSION.md). |
| Two complete six-piece closed orbits | [010202](docs/SIX_ARC_010202.md), its [independent deformation](docs/SIX_ARC_REVERSE_BLOCK.md), and [012012](docs/SIX_ARC_012012.md). These are not the open local L1-L5 statements. |
| Remaining closed six-piece orbit | [012102](docs/SIX_ARC_012102.md) has endpoint/cost reductions but no completed comparison. The archived [moment note](docs/SIX_ARC_012102_MOMENTS.md) proves two sufficient inequalities on every finite arc-vanishing boundary; both interior targets remain open. Work is paused unless it directly proves a bounded-reduction input. |
| Both standard regular polygon families | [REGULAR_FAMILY_COMPARISON](docs/REGULAR_FAMILY_COMPARISON.md) handles equal-arc standard families of arbitrary size, not asymmetric words. |
| Other length-independent restrictions | [fixed edges](docs/SWITCHING_WORDS.md), [cyclic ordering](docs/VERTEX_WORD_REDUCTION.md), [endpoint holonomy](docs/WORD_HOLONOMY.md), [circle intervals](docs/CIRCLE_VARIATION.md), and [near-circle bounds](docs/NEAR_CIRCLE_BOUND.md). None supplies a uniform word bound. |
| Failed shortcuts | [GLOBAL_CALIBRATION](docs/GLOBAL_CALIBRATION.md) and [LOCAL_SHORTENING_OBSTRUCTION](docs/LOCAL_SHORTENING_OBSTRUCTION.md); preserve these to prevent repeated invalid reductions. |
| Earlier constructive Lean drafts | Actual-minimizer geometric/control realization and reverse comparison. They remain uncompiled and unchanged by this checkpoint. |

## Current-session entries

- **Entire mixed case M3 CLOSED:** MIXED_GLOBAL_MINIMUM_STRUCTURE and
  its independent audit exclude every bounded reverse run of length
  at least three. The actual reflection, common normal edge covector,
  alternating-margin inequality and finite-run minimum proof retain all
  ties and the twisted seam. Every remaining mixed reverse run has
  exactly two switches. R and M3 are closed; F, M1 and M2 remain open.

- **Whole-forward ellipticity proved:** GLOBAL_STRUCTURE_FORWARD_ELLIPTIC
  and its independent audit exclude all nonelliptic primary costates
  for every normal pure-forward period, without equal factors, rank,
  a budget or transverse ties. The two-dimensional Jacobi kernel and
  exact stationarity give the contradiction. Ten exact identities pass.
  The remaining curvature-corrected constrained Hessian is explicit;
  no uniform negative direction or complete F comparison is claimed.

- **Entire reverse global case CLOSED:** GLOBAL_REVERSE_PERIOD_EXCLUSION
  proves a strict minimum principle for every normal 0210 PMP window.
  Two positive needles with zero endpoint differential have strictly
  negative cost at the asserted margin minimum. A minimum in the actual
  twisted periodic sequence excludes all pure reverse periods, across
  every costate sector and without a budget. Independent hand review and
  20 exact identities pass. At that checkpoint four cases remained;
  the later bounded-run minimum principle also closes M3.

- **Case-first computational reorientation:** adopt the fixed five
  complete-period exclusion cases and 15 small A/B/C gates in
  FINITE_CASE_COMPUTER_ROADMAP. Publish deterministic numerical oracles:
  structural_case_probe.py (fixed-initial-state six-window normal PMP
  screen), octagon_boundary_probe.py (exact-endpoint numerical
  reverse-eight degeneration), closed_period_index_probe.py (free-initial-
  state complete-period curvature-corrected Hessian). The first experiment
  records actual inputs, versions, commands, failures and limitations.
  Generic windows are not stationary; known stationary L1/L3 windows
  fail their two external switch ties; standard N=7 forward passes
  local PMP but exceeds the full-period octagon cost. Numeric constrained
  indices 0/2/4 at N=4/7/10 match an **existing** standard-family theorem.
  No universal cost exclusion, new hand inequality, or practical exhaustive
  search is claimed. Do not increase N sequentially. At that checkpoint
  all five case C gates and the unrestricted conjecture remained open;
  the later direct reverse-period proof closes R.


Newest entries come first. Earlier entries record the scope at their own
checkpoint; the active gate table above controls current status.

- Test the next proposed all-reverse comparison and refute its unconditional
  C>=pi target. VERTEX_INSERTION_OBSTRUCTION proves a general rank-five
  insertion lemma, checks the actual octagon endpoint rank with both initial
  state variables free, and preserves the full twisted seam. Positive
  all-reverse refinements approach A_oct. A uniform positive gap cannot
  be supplied by the word and endpoint constraints alone. The result makes
  no cheaper-than-octagon or PMP claim; G4 remains open.

- Complete the sharpness audit of GLOBAL_COST_CASIMIR. The exact defect
  identity separates winding, frame nonorthogonality, and stationary-control
  slack; equality is precisely the normal circle lift, with centroid control
  almost everywhere. Add exact local subcritical forward/reverse and cubic
  reverse-switch examples to prevent invalid pointwise reductions. Independent
  hand derivations checked the two active switching derivatives and the
  edge-coordinate pullback. These diagnostics close no additional G4 class:
  a comparison using actual complete-period closure remains the open step.

- Sharpen the universal bound to `D>10^-11`, `N<10^56` in
  SINGULAR_COST_BUDGET. A direct homogeneous polar-budget inequality
  covers every costate component and abnormal multiplier; positive
  equilibrium weights and frame conservation replace exponential norm
  propagation by `10^-8<norm(P)<10^8`. MEASURABLE_EDGE_PMP_BOUND proves
  E4 directly by a separate fixed-time PMP, integrating factor, and
  quadratic zero count. Independent full hand reviews checked both notes
  and every numerical substitution. The concurrent cost--Casimir proof is
  preserved. The active chain needs no source Theorem 8.1.4 or 16.3.1;
  G4 cost comparison and affine equality remain open.

- Complete the universal numerical reduction. GLOBAL_COST_CASIMIR proves
  the actual-frame polar-angle inequality and the competitive negative
  elliptic determinant gap. GLOBAL_NUMERICAL_REDUCTION checks exact
  rational cost bounds, exhausts all normal orbit types, retains abnormal
  lifts, and proves `D>10^-1906` and `N<10^5741` with E4. It does not use
  Theorem 16.3.1 or assume a finite vertex representation. Separate internal
  reviews checked the fully assembled proofs and the Chapter 8 dependency.
  G2 and G3 are now complete under the stated inputs; G4 cost comparison
  and equality remain open, with an impractically large numerical ceiling.

- Prove conserved-determinant clearance: exact trace algebra yields
  `|Delta|<=9*||A||/4+||A||^2/2`, so `|Delta|>=delta` forces
  `D>delta/3` and a fully explicit count. Initial normalization also
  separates every |lambda|>=1/2 lift. Keep the intermediate normal,
  near-critical region open and distinguish a critical-slice tube from
  a transverse neighborhood certificate.

- Prove a numerical small-multiplier subcase: norm decomposition gives
  `D>=m-sqrt(11/2)*|lambda|`; exact coefficient bounds give fewer than
  `10^5740` pieces when `|lambda|<=m/sqrt(22)`. This includes every abnormal
  lift and does not use Theorem 16.3.1. Safely normalize the complementary
  lifts to cost multiplier -1 with explicit costate bound `10^3807`.
  Independent hand reviews checked the arithmetic and one-lift quantifier.

- Sharpen the regular-domain count to three comparison lines and local
  factor 28. Four possible small rotations supply an explicit derivative
  margin; propagate its new value through every threshold and time bound.
  The conditional formula is now `28*ceil(T_max/[c*min(epsilon,1,m)])`.
  Independent reviews checked both the angular construction and constants.
- Audit the external finite bang-bang input. FINITE_BANG_BANG_SOURCE_AUDIT
  records the numerical unstable-curve and basin steps used by the checked
  source. The minimizing-family clearance and existential common bound
  remain deductions using Theorem 16.3.1; no independent certification of
  that theorem's computational support is claimed. Compactness and the
  supplied-clearance count retain their separate proofs.
- Publish LOCAL_FORWARD_REGULAR_DESCENT: exact same-word improvement on
  1<q<=5/4 and open neighborhoods of the state-cyclic references, with
  independent Hessian, sign, endpoint-fiber, and nearby-input reviews.
  Full L1 remains open; no new standard global family is counted.

- Prove and independently review GLOBAL_FORWARD_INDEX: the standard
  N=3k+1 forward family has constrained negative index at least 2(k-1).
  Cyclic active margins resolve state closure; all three remaining frame
  equations, the endpoint curvature correction, and Fourier signs are
  checked. Rank-three regularity yields genuine cheaper closed variations.
  This is a method check on an already cost-excluded family, not new
  competitor coverage or a theorem for asymmetric words.

- Replace the failed broad local route with the complete-period global plan.
  Prove the actual PMP interface, compactness of all normalized minimizing
  lifts including abnormal limits, uniform qualitative singular clearance,
  and a locally uniform transported-covector switch theorem. Together they
  give one common finite bound over every global minimizer. Published as
  [48e3a42](https://github.com/vltanh/lean4-smoothed-octagon/commit/48e3a425391a1e194911929a98ff7c2d7780e3e1).

- Make the regular-domain count effective in QUANTITATIVE_REGULAR_SWITCH_BOUND.
  Prove explicit state denominator and multiplier bounds, two exact algebraic
  coercivity estimates, a fixed angular mesh, and every short-time error
  budget. A supplied normalized clearance epsilon gives an explicit
  O(1/epsilon) bound; no numerical clearance, particular integer, or global
  cost comparison is inferred. Three separate hand reviews passed.

- Prove the finite phase-region escape criterion in GLOBAL_PERIOD_BUDGET
  and verify it over the explicit core range 0<b<=1/(10000*sqrt(3)). It
  excludes any closed-PMP occurrence of the small padded L3 family.
  Preserve the independent concurrent asymptotic continuation/cost proof
  below; these are complementary certificates for one family.

- Certify actual endpoint rank four at one full positive strict-star L2
  input in LOCAL_L2_RANK_DROP. The paired image has rank five and contains
  its state-stabilizer line; all six factors and all seven states are exact.
  Prove separately that its cost exceeds pi. Independent matrix and active-
  margin reviews passed. This refutes unrestricted positive-domain rank five,
  not rank five on the competitive sublevel or any local improvement target.

- Prove that completing the outer control-0 arcs of the padded L3
  counterexample does not yield a complete PMP candidate when the core is
  sufficiently small. Exact limiting gaps stay positive until star loss;
  first- and second-derivative estimates control the degenerating join.
  Reflection handles both sides. An independent hand review passed. The
  auxiliary cost excess applies only to intervals within one period.
  No general L3 replacement or explicit smallness cutoff is claimed.

- Prove endpoint rank five throughout L5 using its five-piece prefix02101.
  A three-column frame pivot and an explicit positive two-column minor give
  a five-dimensional paired image. A strict-star sign makes it transverse
  to the state-stabilizer line, so actual rank is five even when the paired
  six-by-six determinant vanishes. Independent hand review passed. L5
  minimizing windows are normal with a unique normalized adjoint; no cost
  exclusion is inferred.

- Define and independently review a corrected five-template necessary domain
  in SWITCH_COMPLETE_REDUCTION. Preserve the false original L3 claim as
  historical, retain one continuous PMP lift and both external ties, and
  prove actual minimizing-window membership and the finite-splice conditional
  implication. All five revised cost-improvement targets remain open.

- Prove full endpoint rank five on the entire positive strict-star L3
  domain in [LOCAL_MIXED_SIX_RANK](docs/LOCAL_MIXED_SIX_RANK.md). The middle
  edge map has rank three; two exact asymmetric normal columns have strictly
  negative determinant. Fixed outer-flow transformations cover arbitrary
  positive padding, with the initial state fixed. Independent hand review
  passed. This removes abnormality and normalized-adjoint ambiguity throughout
  L3; it supplies no descent and does not restore the original false target.

- Prove the complete-window external-switch condition, including the actual
  twisted seam and the unique-adjoint argument. Exclude the exact L1 input
  and the displayed sufficiently small padded L3 family from this necessary
  domain. Derive an exact active-margin filter for L1, and prove that full
  local PMP plus both endpoint ties still permits asymmetric windows.
  Independent hand reviews passed. No universal analytic target is closed.

- Prove that the exact L1 input is a strict strong local minimum against
  arbitrary nearby controls, with twelve full-arc gap certificates and the
  normal free-time ASZ hypotheses. Independently review the hand argument
  and reproduce its exact identities. Preserve the concurrent nonlocal proof;
  add a second rational slice with an independent Fraction checker and the
  open-neighborhood continuation. These results concern the same source and
  do not close a universal local gate.

- Strengthened the small-window L3 counterexample to all measurable controls
  and free terminal times. Checked ASZ's hypotheses on one fixed padded
  reference, proved arbitrary-control compactness and state-only clock
  convergence, and used fixed-reference splicing. Independent hand reviews
  passed. The broader finite-replacement relaxation is also refuted; no
  geometric embedding in an actual closed minimizer is asserted.

- Refuted the original at-most-six L3 lemma on its exact necessary-superset
  domain. Independently reviewed the edge dual, full-arc gap, compactness,
  deletion expansion, normal masses, and inverse argument. Updated the
  reduction and worker instructions to require a repair. No new global
  minimizer class is excluded and no counterexample to Reinhardt is claimed.

- Proved full-domain rank five for L4 and an exact eligible stationary
  family with all five compensated switch needles strictly positive.
  Independently checked the determinant proof, endpoint-correction argument,
  rational logarithm bounds, and whole-arc sector certificate. The exact
  reproduction passed. This refutes the switch-only shortcut; L4 stays open.

- Resolved the broader replacement question at the explicit stationary L1
  input by an exact six-piece `012021` construction. Independently checked
  the rational contraction data, analytic derivative bounds, positivity,
  and logarithm cost certificate. Universal L1 remains open.

- Derive L1 normality and a unique normalized adjoint from full endpoint rank.
  Prove that local PMP plus unrestricted twisted periodic extendibility is
  insufficient, using already known standard polygons with arbitrarily cheap
  eligible six-windows. Their whole periods are not competitive. Independent
  hand and primary-source reviews passed; no local target is closed.

- Prove an exact eligible L3 strict strong local minimum. The finite endpoint,
  Hessian, sector, and needle identities have an exact reproducer; the full-arc
  logarithm signs and published theorem's free-time hypotheses were checked
  by hand and independently reviewed. This rules out nearby methods, not
  the full L3 statement, and leaves the analytic completion count at 0/5.

- Consolidate the independent P0 review into MINIMIZER_WINDOW_AUDIT. Record
  the corrected terminal conjugation, actual relabeling map, exact octagon
  equality trajectory and the nonsingular linear map for each original worst
  disk. The uniform bound is still needed before that conditional rigidity
  conclusion applies; no duplicate P0 note or new exclusion is counted.

- Prove full-domain rank five for L1 by active-margin coordinates and four
  small determinant sign identities. The action and constrained-variation
  formulas passed two independent hand reviews. This closes the interior
  rank-classification subtask only; no universal local input is closed.
- Proved and independently reproduced the exact eligible L1 same-word local
  minimum. The hand certificate includes rational state/sector tables, rank,
  stationarity, and the positive constrained Hessian; the finite exact checker
  is supplementary. A different-word, nonlocal, or minimizer-specific argument
  is now required at this input. No full local target is marked closed.
- P0: proved the selected-window eligibility lemma, including sectors after
  transforming the entire disk by the initial-frame inverse. Verified the
  twisted seam, finite bang-bang source, exact endpoint splice, and low-cost
  reverse geometric construction. The through-five equality scope was
  checked; its full algebra was not re-audited. At that checkpoint all five
  analytic inputs were open; the later L3 refutation is recorded above.
- `6076dc6`: proved the five-template coverage statement by a hand run argument;
  stated the exact local domains, endpoint map, suffix inverses, and conditional
  global conclusion. No analytic local case was marked closed.
- `498df52`: retained an exact finite transition-graph cross-check. All 32
  five-sign blocks are examined; 21 avoid the established +-+ exclusion.
  Removing the five target edges leaves a 12-vertex, 16-edge acyclic graph.
  This verifies coverage without testing a maximum total length.
- Ledger reorientation: freeze increasing-length comparisons; separate the
  proved finite coverage theorem from the then-open universal cost statements.
  Retain the exploratory local-fiber probe with its failures, not as a certificate.
- Independent hand review passed for the five-template coverage: all sign/label
  maps, the twisted seam, the run alternatives, and the one-period window
  condition were checked. This does not review or close any analytic target.
- Preserve the previously completed closed-012102 moment boundary arguments.
  Their cost implication and finite boundary proofs were independently reviewed;
  the two interior inequalities remain open and their investigation is paused.
- Prove the uniform/state-cyclic reverse-six subfamily admits a strict
  seven-piece endpoint-preserving improvement for every q>1. This is recorded
  separately from the five full-domain targets; none is marked closed.

## Literature and validation boundary

The original qualitative route uses Hales--Vajjha Theorem 16.3.1 for
finite bang-bang minimizers, with the source boundary recorded in the audit.
The current explicit bound instead uses the complete-period cost–Casimir
inequality and the independently proved regular-domain count with E4.
It retains the geometric, compact-state, PMP, and local edge source inputs.
Hales's 2011 Section 7.6 already proposes link reduction. The earlier
five-template coverage and finite sufficient package remain separate from
the new boundedness result; a valid reduction to five is still unproved.

See [SOURCE_MAP.md](SOURCE_MAP.md) and
[DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md). No new Lean theorem,
compilation, typechecking, Lake command, kernel audit, or CI run was performed.
