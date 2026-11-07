# Source map: the global-reduction checkpoint

Date: 2026-11-07. No Lean declaration was added or modified for this checkpoint.
The earlier full declaration-by-declaration map is preserved at
[798a7e1 / SOURCE_MAP.md](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/SOURCE_MAP.md).
All corresponding proof files remain in the repository. The current ledger
supersedes earlier recommendations to continue by increasing whole-word length.

## Active global reduction

| Statement | Exact source and scope |
| --- | --- |
| Historical finite bang-bang source boundary | [FINITE_BANG_BANG_SOURCE_AUDIT](docs/FINITE_BANG_BANG_SOURCE_AUDIT.md). The checked source's unstable-curve escape and basin containments use numerical support not independently certified here. Theorem 16.3.1 is retained in the historical qualitative compactness route. The new universal numerical reduction bypasses it and these audited computational steps; it does not certify them. |
| Replacement action plan and acceptance gates | [GLOBAL_REDUCTION_PLAN](docs/GLOBAL_REDUCTION_PLAN.md). Full-period domain, singular clearance, uniform count, then a fixed finite comparison. Numerical clearance and a specific integer are proved; the active gate is global cost comparison and equality. |
| Complete-period cost–Casimir inequality | [GLOBAL_COST_CASIMIR](docs/GLOBAL_COST_CASIMIR.md). An explicit interior stationary control gives 2*kappa*m_s<=3*m_b. Exact spatial conservation and the actual frame endpoint give C>=4*pi*kappa/(2*kappa+3) for negative elliptic normal costate. The budget C<pi separates its determinant from 9/4; no finite-switch input or winding assumption. Section 6 gives an exact nonnegative defect, circle-only equality, and exact local examples showing the determinant gap permits both switching directions and cubic switches. These are scoped diagnostics, not new global exclusions. |
| Original universal numerical clearance and switch bound | [GLOBAL_NUMERICAL_REDUCTION](docs/GLOBAL_NUMERICAL_REDUCTION.md). Hand rational budget estimates and all normal orbit components give cost-normalized norm(A)>1/120. Including small multipliers and abnormal lifts yields D>10^-1906 for every normalized competitive lift; E4 gives N<10^5741 for every global minimizer. No Theorem 16.3.1 or assumed finite representation. Internal reviews passed; final cost/equality comparison remains open. |
| Stronger homogeneous clearance and explicit uniform count | [SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md). Every competitive closed lift satisfies norm(A)>=abs(lambda)*3(pi-C)/(2pi-C). Equilibrium weights, Hamiltonian width, and frame conservation give 10^-8<norm(P)<10^8 on the common state domain. Hence D>10^-11 and N<10^56 with E4. Includes abnormal lifts; no orbit-type split, prior finiteness, or source escape input. |
| Direct measurable-edge four-piece theorem | [MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md). Exact increasing-x reconstruction preserves both endpoints and free-duration cost. A separate two-state PMP and positive integrating factor give at most three zeros of the switching function. All abnormal and degenerate-polynomial cases are included. Supplies E4 without source Theorem 8.1.4 or 16.3.1. |
| Boundary-density obstruction to an unconditional reverse-word gap | [VERTEX_INSERTION_OBSTRUCTION](docs/VERTEX_INSERTION_OBSTRUCTION.md). A general rank-five endpoint map permits small prescribed positive vertex insertions with exact closed endpoints. The octagon rank is proved using two state residuals and its cyclic-four rank-three frame map. All-reverse refinements approach A_oct<pi, refuting C>=pi and any uniform positive gap above A_oct on that class. No PMP or cheaper-than-octagon claim; no increasing-length enumeration. |
| Full-period PMP and unique-adjoint bridge | [GLOBAL_PERIODIC_PMP](docs/GLOBAL_PERIODIC_PMP.md). Free-initial-state transversality, conserved spatial covector, twisted extension, full-rank normality/uniqueness, and a finite-escape implication. |
| Explicit global continuation exclusion | [GLOBAL_PERIOD_BUDGET](docs/GLOBAL_PERIOD_BUDGET.md). Finite phase inequalities force one vertex to the strict-star boundary. Exact proof for all small-core L3 inputs `0<b<=1/(10000*sqrt(3))` with sufficiently small pads. Excludes any closed-PMP occurrence, not all L3 windows. |
| Compactness and uniform qualitative singular clearance | [GLOBAL_MINIMIZER_COMPACTNESS](docs/GLOBAL_MINIMIZER_COMPACTNESS.md). All projectively normalized actual-minimizer lifts, including abnormal ones; exact affine controls and weak-star closedness; positive common distance from the singular locus using external Theorem 16.3.1. This original source-based derivation is retained; the new numerical reduction supplies independent clearance in its stated matrix-covector normalization. No certification of the audited source calculations is claimed. |
| Uniform finite switch bound over all global minimizers | [GLOBAL_CLOSED_VARIATION](docs/GLOBAL_CLOSED_VARIATION.md). Transport to a fixed plane, robust finite angular sectors, uniformly signed first/second projection derivatives, and the minimizer edge bound. Compactness and the sourced singular avoidance give one common finite integer, conditional on the external finite bang-bang input. Three comparison lines give local factor 28. Its strongest numerical application now gives N<10^56 without Theorem 16.3.1; E4 has a direct proof and no dwell-time assertion is made. |
| Effective switch bound from a supplied clearance | [QUANTITATIVE_REGULAR_SWITCH_BOUND](docs/QUANTITATIVE_REGULAR_SWITCH_BOUND.md). Explicit state denominator and projective multiplier bounds, Hamiltonian-width and double-commutator coercivity, three comparison lines with four candidate rotations, and all error budgets. Proves N(epsilon)=28ceil(T_max/[c min(epsilon,1,m)]), with every coefficient fixed. SINGULAR_COST_BUDGET now supplies epsilon=10^-11 and algebraic covector bounds m=10^-8,M=10^8; final comparison remains open. Three independent internal hand reviews passed. |
| Numerical count for small projective cost multipliers | [GLOBAL_SMALL_MULTIPLIER_BOUND](docs/GLOBAL_SMALL_MULTIPLIER_BOUND.md). Exact norm clearance and hand coefficient bounds give N<10^5740 for one normalized lift with abs(lambda)<=m/sqrt(22), including abnormal lifts; abs(lambda)<=10^-1904 suffices. Independent of external Theorem 16.3.1. Complementary lifts admit safe cost normalization with entire covector norm<10^3807. This scoped lemma alone does not count all minimizers; GLOBAL_NUMERICAL_REDUCTION completes the complementary sector. |
| Clearance from the conserved costate determinant | [GLOBAL_CASIMIR_CLEARANCE](docs/GLOBAL_CASIMIR_CLEARANCE.md). Delta=det(Lambda_1)-(9/4)lambda^2 is constant. For 0<delta<=1, abs(Delta)>=delta gives D>delta/3 and N<10^5740/delta; abs(lambda)>=1/2 gives D>1/13 and N<10^5740. Hand algebra independent of Theorem 16.3.1; this scoped lemma alone does not resolve the critical band. GLOBAL_COST_CASIMIR and GLOBAL_NUMERICAL_REDUCTION now supply the missing all-component normal clearance. |
| Closed-period index in the standard forward family | [GLOBAL_FORWARD_INDEX](docs/GLOBAL_FORWARD_INDEX.md). At least 2(k-1) negative constrained directions for N=3k+1, with free initial state, exact state closure, and all three frame constraints. Exact multiplier, curvature correction, Fourier sum, and hand logarithm sign. Independently reviewed; validates a method on an already cost-excluded family. |

## Earlier local reduction and diagnostics

| Statement | Exact source and status |
| --- | --- |
| Uniform local descent on a forward state-cyclic subfamily | [LOCAL_FORWARD_REGULAR_DESCENT](docs/LOCAL_FORWARD_REGULAR_DESCENT.md): for all 1<q<=5/4, an exact negative constrained Hessian gives a six-piece same-word improvement with both endpoints fixed. The elementary logarithm sign and exact-fiber continuation are independently reviewed. Includes standard complete-switch windows and unspecified open neighborhoods; not all asymmetric L1 or a new global family exclusion. |
| Exact full-L2 rank-four point outside the competitive sublevel | [LOCAL_L2_RANK_DROP](docs/LOCAL_L2_RANK_DROP.md): six positive factors, all seven positive states, paired rank five and exact stabilizer inclusion give actual rank four. Elementary logarithm bounds prove C>pi. Independently reviewed, including a distinct active-margin check. No rank drop in the eligible cost domain or abnormal minimizer is asserted. |
| Small-core padded L3 continuations have no next switch before star loss | [PADDED_L3_PMP_CONTINUATION](docs/PADDED_L3_PMP_CONTINUATION.md): exact limiting control-0 gaps, positive small-core join slopes, second-derivative control, moving-boundary persistence, and reflection. Both maximal continuations hit the strict-star boundary before another tie. Auxiliary cost excess is restricted to one-period intervals. Independently reviewed; existential smallness only, no general L3 closure. |
| Full-domain L5 rank from its five-piece prefix | [LOCAL_L5_ENDPOINT_RANK](docs/LOCAL_L5_ENDPOINT_RANK.md): a three-column pivot, exact positive lower minor, and strict-star stabilizer transversality prove actual rank five for prefix02101 and hence full L5. This does not assume the paired six-by-six determinant is nonzero. Independently reviewed; no descent assertion. |
| Revised complete-switch necessary domains and conditional reduction | [SWITCH_COMPLETE_REDUCTION](docs/SWITCH_COMPLETE_REDUCTION.md): one continuous nontrivial free-time PMP lift, whole-arc inequalities, and both inactive external ties. Every selected actual minimizing window belongs; finite-piece improvement on all five revised domains would imply N<=5. Independently reviewed. All five analytic premises remain open; original L3 falsity is preserved. |
| Full-domain L3 endpoint rank and normalized-adjoint uniqueness | [LOCAL_MIXED_SIX_RANK](docs/LOCAL_MIXED_SIX_RANK.md): an arbitrary positive reverse-edge core has rank three; exact asymmetric outer-needle normal columns have strictly negative determinant. Fixed outer-flow coordinates prove rank five for the entire positive strict-star L3 domain. Independent review passed. No descent, smallness assumption, or restoration of the false original target. |
| Necessary external ties for six complete minimizer pieces | [MINIMIZER_WINDOW_PMP](docs/MINIMIZER_WINDOW_PMP.md): continuity and free-time PMP force an inactive tie at each external switch. Rank excludes abnormal or alternative normalized adjoints at the exact L1 input and the sufficiently small padded L3 family; their strictly unique external active controls exclude them from selected complete windows. Independent hand review passed. No full-domain improvement is claimed. |
| Explicit L1 boundary filter and asymmetric inputs that pass it | [LOCAL_FORWARD_ENDPOINT_FILTER](docs/LOCAL_FORWARD_ENDPOINT_FILTER.md): four inactive gaps reduce to two interval-endpoint tests using active margins and a three-dimensional covector. A smooth five-dimensional family of asymmetric eligible local-PMP windows passes both ties; equal factors do not follow. Independently reviewed; no competitive whole-period extension is supplied. |
| Nonlocal replacement at the explicit stationary L1 input | [LOCAL_FORWARD_NONLOCAL_REPLACEMENT](docs/LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md): two independently certified slices give exact six-piece `012021` solutions with the same endpoints and cost decrease greater than `1/100000`. The appendix has a standard-library [Fraction checker](explorations/local_forward_nonlocal_fraction_certificate.py) and a nearby-input continuation; no full-domain coverage. |
| Exact L1 strong local minimum against arbitrary nearby controls | [LOCAL_FORWARD_NEEDLE_AUDIT](docs/LOCAL_FORWARD_NEEDLE_AUDIT.md): twelve exact full-arc gaps, strict external endpoint maximization, transverse switches, and checked normal ASZ augmentation. The [exact reproducer](explorations/local_l1_needle_certificate.py) and independent hand review passed. Compatible with the distant replacement. |
| L1 normality and the limit of a first-order periodic-extension criterion | [LOCAL_FORWARD_PMP_LIMIT](docs/LOCAL_FORWARD_PMP_LIMIT.md): full rank implies normality and a unique normalized adjoint. Existing standard forward polygons give eligible full-PMP windows of arbitrarily small local cost, with noncompetitive whole periodic extensions. Independent primary-source/hand review passed; no new closed-family comparison or local exclusion. |
| Exact strong local minimum within the eligible L3 domain | [LOCAL_L3_STRONG_MINIMUM](docs/LOCAL_L3_STRONG_MINIMUM.md): exact endpoint, sector and cost certificates, positive constrained Hessian, all-arc Hamiltonian signs, and a checked free-time application of ASZ Theorem 2.6. Rules out nearby improvement at its explicit input; no distant comparison for that input. The [exact reproducer](explorations/local_l3_exact_certificate.py) is supplementary. |
| Counterexample to the original at-most-six L3 statement | [LOCAL_REVERSE_SIX_OBSTRUCTION](docs/LOCAL_REVERSE_SIX_OBSTRUCTION.md): eligible arbitrarily cheap padded reverse-four windows have no cheaper replacement of at most six pieces. Exact edge dual, compactness, normal mass, and endpoint inverse; independently reviewed. Larger replacement counts and closed-minimizer embedding are not asserted. |
| L3 counterexample even with arbitrary measurable replacements | [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md): exact convexification, state-only clock, checked ASZ Theorem 2.6 for one fixed padded reference, measurable compactness, and fixed-reference splicing. Sufficiently small trims are global minima for their fixed endpoints with free time; no piece cap. Independent hand review passed. No closed-minimizer embedding or Reinhardt counterexample is asserted. |
| Full-domain endpoint rank for L1 | [LOCAL_FORWARD_RANK](docs/LOCAL_FORWARD_RANK.md): active-margin coordinates, exact cost action, and a hand determinant sign proof of rank five everywhere on the positive strict-star domain. Two independent hand reviews passed. No cost exclusion or boundary conditioning estimate. |
| Full-domain L4 endpoint rank and failure of switch-only descent | [LOCAL_SIX_VARIATION](docs/LOCAL_SIX_VARIATION.md): a short determinant proves rank five everywhere; exact compensation converts negative needles to replacements. An eligible stationary family has all five switch needles positive, certified by rational logarithm and sector bounds. Full L4 remains open. The [exact reproducer](explorations/local_l4_switch_obstruction.py) is supplementary. |
| Exact obstruction to universal nearby same-word L1 descent | [LOCAL_FORWARD_SIX](docs/LOCAL_FORWARD_SIX.md): an eligible `012012` input with rank-five endpoint map and a strict constrained local minimum. Full L1 remains open. The [exact checker](explorations/local_forward_stationary_obstruction.py) is supplementary. |
| P0: minimizer-window eligibility and finite-piece geometric splice | [MINIMIZER_WINDOW_AUDIT](docs/MINIMIZER_WINDOW_AUDIT.md): hand proof, using Hales--Vajjha Theorem 16.3.1 and balanced-disk correspondence; sector normalization and winding are proved explicitly. Independent premises and equality-transfer reviews passed; exact octagon trajectory and linear equivalence are displayed. The entire through-five algebra was not re-audited. |
| Five-template coverage for every minimizing N>=6 | [BOUNDED_REDUCTION, Sections 1-2](docs/BOUNDED_REDUCTION.md): complete independently reviewed hand run argument, conditional on the already supplied forward-alternation exclusion. |
| Local strict improvements imply N<=5 and then global minimality/rigidity | Same note, Section 3: valid conditional implication, but the original L3 premise is false. The revised domains are in SWITCH_COMPLETE_REDUCTION; their five analytic premises remain open. No N<=5 theorem is proved. |
| Eight-coordinate input domains | Same note, Section 4: initial margins, exact factor updates, full-arc signs, cost, and geometric sector tests. |
| Full local endpoint map | Same note, Section 5: preserve tangent product AND terminal state with initial state fixed; generally the tangent endpoint is not R. |
| Exact elimination of three endpoint equations | Same note, Section 6: explicit inverses for both orientations of a positive distinct-label triple. LOCAL_FORWARD_RANK, LOCAL_MIXED_SIX_RANK, LOCAL_SIX_VARIATION, and LOCAL_L5_ENDPOINT_RANK resolve the remaining rank as two throughout the positive L1, L3, L4, and L5 domains; singular loci for L2 remain a separate obligation. |
| Parameter compactification and limits | Same note, Section 7: bounded coordinates only, not a certified finite interval search. |
| Finite graph cross-check | [finite_window_cover.py](explorations/finite_window_cover.py): 32 blocks, 21 surviving the established exclusion, five target edges, then a 12-vertex/16-edge DAG. No analytic cost conclusion. |
| Numerical diagnostic | [local_six_fiber_probe.py](explorations/local_six_fiber_probe.py): floating-point local search with a fixed seed and finite inputs. Neither convergence nor failures are proof premises. |
| Uniform/state-cyclic reverse-six subfamily | [LOCAL_REVERSE_SIX](docs/LOCAL_REVERSE_SIX.md): for every q>1, a strict seven-piece improvement with the same initial/final frame and state. Exact rank, correction, and cost-sign hand certificates. A proper subfamily only; full L2 and its at-most-six replacement statement remain open. |

## Existing mathematical inputs to the conditional implication

- [FORWARD_ALTERNATION_EXCLUSION](docs/FORWARD_ALTERNATION_EXCLUSION.md): the
  local pattern `i,i+1,i,i+1` is excluded, equivalently the sign block `+-+`.
- [VERTEX_WORD_REDUCTION](docs/VERTEX_WORD_REDUCTION.md): actual cost-preserving
  twisted extension and rebasing. Wrapped labels increase by one.
- [WORD_HOLONOMY](docs/WORD_HOLONOMY.md) and
  [FIVE_ARC_PROGRESS](docs/FIVE_ARC_PROGRESS.md): the two endpoint product orders,
  exact state margins, triangular factors, and cost formulas.
- [FOUR_LINK_HAND_PROOF](docs/FOUR_LINK_HAND_PROOF.md),
  [FIVE_ARC_PROGRESS](docs/FIVE_ARC_PROGRESS.md), and
  [REVERSE_FIVE_ARC](docs/REVERSE_FIVE_ARC.md): terminal comparison through five
  pieces and equality within that class. These do not prove a word-length bound.
- [REVERSE_COMPARISON](docs/REVERSE_COMPARISON.md): the geometric/control
  correspondence and exact cost conventions used in the program.

## Published sources and attribution

The archived [SIX_ARC_012102_MOMENTS](docs/SIX_ARC_012102_MOMENTS.md)
retains the previously completed cost implication and proofs of two sufficient
moment inequalities on all finite arc-vanishing boundary faces. These hand
arguments were independently reviewed. Both interior inequalities remain open;
this is neither a closed six-piece comparison nor a local L1-L5 improvement.
Further investigation is paused under the current priority.

Hales, *On the Reinhardt Conjecture* (2011), Section 7.6, Conjecture 56 and
Lemma 58, proposes local six-to-five link reduction and its role in reducing
the global comparison. The reduction idea is not new priority claimed here:
https://arxiv.org/html/1103.4518

Hales-Vajjha, *Packings of Smoothed Polygons* (2024), Theorem 16.3.1, proves
finite bang-bang structure for a global minimizer. Appendix B.4 explicitly
leaves a uniform edge bound unprovided:
https://arxiv.org/html/2405.04331v1

The five-template hand coverage and the precise weaker strict-improvement
package are the present contribution. They do not establish the five
universal local statements. Historical constructive Lean dependencies remain
pinned at the same revisions recorded in README and the historical source map.

