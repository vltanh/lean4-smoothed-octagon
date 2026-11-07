# Research toward the Reinhardt conjecture

This project studies whether the concrete smoothed octagon globally minimizes
the greatest packing density among centrally symmetric convex disks, with
uniqueness up to affine equivalence. It reuses the geometry of
[vltanh/lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon).

**The unrestricted conjecture is not proved. Lean compilation and kernel
validation have not been run. New formalization infrastructure is paused.**

## Active research route: finite complete-period PMP cases

See the [computer-assisted five-case roadmap](docs/FINITE_CASE_COMPUTER_ROADMAP.md)
and [reproducible first experiment](docs/CASE_ATLAS_EXPERIMENT_001.md).
The existing sign-coverage theorem sends every possible N>=6 minimizer
to one of five fixed six-window types: 012012, 021021, 021210,
010201, or 021012. Rather than enumerate lengths up to 10^56,
investigate the *complete-period minimizing extension* of each
type: necessary PMP switches, full twisted return and cost budget,
then a uniform hand-certified exclusion. The broad local 021210
replacement is known false and is not reinstated.

The numerical oracles in explorations/structural_case_probe.py,
explorations/octagon_boundary_probe.py, and
explorations/closed_period_index_probe.py are regression diagnostics.
The standard N=4,7,10 constrained-Hessian negative indices are
numerically 0,2,4, matching the existing exact standard-family
result, but **no entire remaining case is excluded**. The final
global cost inequality and affine equality theorem are OPEN.

## Closed checkpoint: every minimizing PMP lift is normal

[GLOBAL_NORMALITY](docs/GLOBAL_NORMALITY.md) and its
[independent internal audit](docs/GLOBAL_NORMALITY_AUDIT.md) exclude every
abnormal free-time PMP lift of a finite strict-star vertex trajectory with
the actual twisted state, frame and cotangent endpoints. The proof covers
rank defects and triple ties and uses no cost cap or transverse-switch
assumption. The existing finite-representation theorem therefore applies
it to all global minimizers.

Compactness further gives a qualitative positive lower bound on -lambda
in the initial unit normalization, and a compact family after normalizing
lambda to -1. No explicit value of that lower bound is claimed.
The restored exact checker passes 22 matrix/scalar identities. This closes
the normality obligation. Internal review is not external peer review or
Lean kernel validation.

[The normal outgoing-tie theorem](docs/NORMAL_TIE_BRANCHING.md), with an
[independent internal audit](docs/NORMAL_TIE_BRANCHING_AUDIT.md), now gives
a necessary-and-sufficient local sign test for each candidate positive
vertex arc. Explicit derivatives through order three resolve double and
triple ties and quadratic/cubic contacts. All passing branches must be
retained. The theorem supplies no uniform arc length and does not prove
closed return, cost comparison, or optimality; all five global cost
comparisons remain open.

## Uniform exclusion of the full symmetric M1 core family

[The symmetric mixed-core theorem](docs/MIXED_GLOBAL_SYMMETRIC_ESCAPE.md)
excludes every competitive closed PMP period containing a reflection-
symmetric `2121` core with four common factors `1<h<2`, any admissible
scale `0<v<3`, a positive incoming control-0 pad, and an outgoing
control-0 pad of factor at least `h`. It includes all symmetric M1
windows with six equal factors; the outer cuts may lie inside longer
arcs. The conclusion uses the actual complete-period equations.

The unique normalized adjoint either violates the complete-period
cost--Casimir budget or forces the last vertex to the state boundary
in finite time. The hand proof covers the full stated parameter range,
including a degenerate initial tie, with elementary logarithm bounds
and 18 explicit positive rational Bernstein coefficients. An
[independent internal review](docs/MIXED_GLOBAL_SYMMETRIC_AUDIT.md)
passed, as did all 146 supplementary exact algebra/sign checks.
Arbitrary asymmetric M1 cores and shorter outgoing pads remain open;
this subfamily theorem closes none of the five universal C gates.

[An exact short-pad obstruction](docs/MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md)
shows why the extension needs more than the local moments, adjoining ties
and Casimir cap. One asymmetric normal PMP core passes all those tests,
but its outgoing 0 arc switches back at a factor strictly between
`251/250` and `201/200`, before reaching the positive critical point.
Its first incoming cut is not asserted to be a switch; complete-period
closure, geometric embedding and minimality are unchecked. This refutes
the proposed local implication, not the full M1 target.

## Uniform costate-sector restriction for pure periods

[The cyclic costate-sector theorem](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md)
and its [independent audit](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_AUDIT.md)
exclude zero and the closed positive elliptic primary-costate cone for
every entirely forward or entirely reverse normal PMP period. The proof
allows arbitrary unequal factors and uses the full twisted endpoints and
free-initial-state transversality. A signed cyclic action has strictly
positive partial derivatives, while its exact frame columns all have
a fixed elliptic orientation; the PMP pairing yields the contradiction.
Hyperbolic, negative parabolic, and negative elliptic costates remain.
This is a sector restriction, not a global cost or index bound.

[The reverse Casimir calculation](docs/REVERSE_PERIOD_CASIMIR_REDUCTION.md)
identifies a specific remaining obstacle: each stationary trace equation
gives an upper bound on the Casimir, whereas the cost obstruction needs
a lower bound. The required lower bound holds for the already excluded
equal-margin family. Arbitrary unequal margins still require a cyclic
compatibility argument.

## Active result: an explicit bound for every global minimizer


**Start with [GLOBAL_REDUCTION_PLAN](docs/GLOBAL_REDUCTION_PLAN.md).**
Under the retained geometric, compact-state, and standard Pontryagin maximum
principle (PMP) inputs, every global minimizer has a complete period with

\[
\boxed{N<10^{56}}
\]

positive constant vertex pieces. This hand-proof bound includes abnormal
lifts and constructs a finite representation from arbitrary measurable
controls. The numerical boundedness gate is complete; global minimality
and affine uniqueness remain open. The ceiling is still far too large for
a practical exhaustive calculation.

The strongest current proof has three parts:

- [SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md) compares the zero
  Hamiltonian with an explicit equilibrium simplex control. Spatial costate
  conservation and the polar angle of the actual frame path give
  `norm(Lambda_1-(3/2)*lambda*J) >= abs(lambda)*3*(pi-C)/(2*pi-C)`
  at every time in a complete period with `C<pi`. The argument includes all
  frame-costate components without dividing by the cost multiplier.
- The same note uses the total cost and positive equilibrium weights to
  prove `10^-8 < norm((lambda,Lambda_1,W)(t)) < 10^8` in the initial unit
  product normalization. The octagon budget then gives the explicit
  singular clearance **`D>10^-11`** for every normalized competitive
  closed lift in the common state domain.
- [MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md) proves the
  four-piece edge property (E4) directly. An independent edge PMP and a
  positive integrating factor reduce its switch count to the roots of a
  quadratic. [QUANTITATIVE_REGULAR_SWITCH_BOUND](docs/QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
  combines E4 with three comparison lines and the supplied clearance to
  obtain the stated integer. No minimum arc duration is assumed.

This route does not require Hales--Vajjha Theorem 8.1.4 or Theorem 16.3.1.
The numerical escape and basin inputs recorded in
[the source audit](docs/FINITE_BANG_BANG_SOURCE_AUDIT.md) remain uncertified
here; the current proof bypasses them. The geometric correspondence, common
compact state domain, and standard PMP remain explicit inputs. Separate
internal hand reviews checked the assembled proofs and constants; these
are not Lean kernel certificates or external peer review.

The independent concurrent [cost--Casimir inequality](docs/GLOBAL_COST_CASIMIR.md)
and [original numerical reduction](docs/GLOBAL_NUMERICAL_REDUCTION.md)
remain intact. They give the larger bound `N<10^5741` by a different
costate-component argument and the earlier Gronwall estimates.
The sharper result above replaces that bound in the active plan.

The active task is a uniform cost comparison on the bounded class, or a
stronger structural/index reduction such as `N<=5` that makes the retained
through-five comparison applicable. Exact frame and state closure, free
initial state, boundary limits, and equality cases remain part of that task.
The integer bound supplies none of those cost inequalities.

A further [insertion obstruction](docs/VERTEX_INSERTION_OBSTRUCTION.md)
checks a proposed next shortcut: at a closed trajectory with endpoint rank
five, arbitrarily short prescribed vertex insertions can be compensated
while preserving both endpoints. Refining the octagon this way produces
all-reverse closed trajectories with costs approaching A_oct<pi. Thus
an unconditional all-reverse lower bound by pi, or by A_oct plus a fixed
positive gap, is false. No cheaper-than-octagon or PMP trajectory is claimed;
any strict comparison must handle these boundary limits.

The [sharpness audit](docs/GLOBAL_COST_CASIMIR.md#6-exact-defect-and-equality-in-the-cost--casimir-bound)
gives an exact sum of three nonnegative defects. Equality in that bound
forces the centroid-controlled circle, with cost pi; this is separate from
the octagon equality case. Exact local PMP examples also show that the
competitive determinant gap permits both switch directions and a genuine
cubic switch. A general closed-period comparison must retain those cases;
the gap alone supplies neither a forward-only rule nor simple switches.

Earlier results remain available: [compact normalized minimizing lifts](docs/GLOBAL_MINIMIZER_COMPACTNESS.md),
[the full-period PMP interface](docs/GLOBAL_PERIODIC_PMP.md), and
[an explicit continuation obstruction](docs/GLOBAL_PERIOD_BUDGET.md)
excluding every small-core padded L3 occurrence from a closed PMP period.
The [small-multiplier](docs/GLOBAL_SMALL_MULTIPLIER_BOUND.md) and
[determinant-separation](docs/GLOBAL_CASIMIR_CLEARANCE.md) estimates are
preserved as independent scoped results.

## Historical five-template route and retained diagnostics

The [earlier five-template handoff](docs/FIVE_TEMPLATE_HANDOFF.md) records
the failed sufficient package and its useful coverage proof. The prerequisite
[P0 audit is complete as a hand proof](docs/MINIMIZER_WINDOW_AUDIT.md):
it verifies minimizer eligibility, twisted seams, normalized geometric sectors,
and the finite-piece geometric/control splice. **The original local L3
statement is now refuted:** eligible `021210` windows can minimize cost for
their fixed endpoints among all measurable simplex controls, with free time.
Read [the full obstruction](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md) and
[its self-contained six-piece foundation](docs/LOCAL_REVERSE_SIX_OBSTRUCTION.md) before trying
to complete that sufficient package. L1, L2, L4, and L5 remain open;
universal analytic exclusions proved: **0/5**.

The revised [complete-switch PMP package](docs/SWITCH_COMPLETE_REDUCTION.md)
now has a proved necessary domain and conditional implication: every selected
minimizing window admits one nontrivial PMP lift with inactive ties at both
external switches, and strict finite-piece improvement on the five restricted
domains would imply N<=5. **All five revised analytic targets remain open.**
The new hypotheses do not establish any universal cost decrease. Do not
resume increasing-length whole-trajectory enumeration.

The P0 note also records the corrected terminal conjugation and the explicit
equality transfer to the concrete octagon. Independent premises and equality
reviews found no additional gap in that conditional transfer. A valid reduction
to the through-five class is still required before that equality transfer
proves unrestricted rigidity.


The user requested a bounded set of cases before continuing case-by-case
comparisons. The current research target is therefore a uniform complexity
reduction, not the next arc count.

[BOUNDED_REDUCTION.md](docs/BOUNDED_REDUCTION.md) proves a hand coverage theorem:
using the established local forward-alternation exclusion, any finite cyclically
reduced minimizing trajectory with at least six positive vertex pieces contains,
up to cyclic relabeling, one of these six-piece windows:

| Local template | Sign description | Original-domain improvement status |
| --- | --- | --- |
| 012012 | Five forward switches | Open |
| 021021 | Five reverse switches | Open |
| 021210 | One forward switch between two reverse pairs | Refuted on the stated domain even with arbitrary measurable replacements |
| 010201 | Reverse run of length two followed by at least two forward switches | Open |
| 021012 | Reverse run of at least three followed by at least two forward switches | Open |

Each window has eight free input coordinates: two initial-state coordinates
and six positive factors. Its eligibility and endpoint equations are explicit.
Proving a strictly cheaper replacement with the same frame and state endpoints
for each entire local domain would imply that every global minimizer has at
most five pieces. A replacement may still use six pieces; strict cost decrease
alone contradicts minimality. Actual six-to-five shortening is not necessary.

The existing through-five comparison and equality case would then finish the
hand proof. **Coverage and this conditional implication are proved, but the
original L3 premise is false; N<=5 remains open.** No finite
interval computation on a truncated parameter box is advertised as exhaustive.

The complete domains, twisted-seam argument, exact endpoint map, positive-factor
inverses, and singular-rank obligations are in the note. The independent hand
coverage proof uses runs of forward/reverse switch signs and has received a
separate hand review of the sign catalogue, twisted seam, and run argument. The retained
[finite graph cross-check](explorations/finite_window_cover.py) examines only
32 fixed-size sign blocks and verifies an acyclic graph; it does not enumerate
trajectories up to an arbitrary maximum length.

### A local subfamily with an exact improvement

The [exact L1 obstruction](docs/LOCAL_FORWARD_SIX.md) satisfies all the input
eligibility tests but is a strict minimum on its nearby same-word endpoint
fiber. Thus universal nearby same-word descent is false even in the
competitive geometric domain. This does not refute a different-word or
nonlocal L1 replacement, and it is not a counterexample to Reinhardt.
An [exact different-word certificate](docs/LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md)
now resolves that particular input with a six-piece `012021` replacement
whose normalized cost is lower by more than `1/100000`. It does not prove
the universal L1 claim.

The [full needle audit](docs/LOCAL_FORWARD_NEEDLE_AUDIT.md) proves that this
source is a strict strong local minimum in the augmented normalized free-log-time
problem, including arbitrary nearby controls. Every full-arc sign and the
published sufficient theorem are checked. The cheaper path is a distant
replacement, so the two results are compatible. The nonlocal note's independent
appendix supplies a second exact slice with a standard-library Fraction checker;
an implicit-function argument extends the improvement to nearby eligible inputs,
with no claimed coverage of the full L1 domain.

The [full-domain L1 rank theorem](docs/LOCAL_FORWARD_RANK.md) independently
resolves the singular-fiber question: all five frame-and-state endpoint
constraints have rank five for every strict-star `012012` input with positive
durations. Its active-margin coordinates also give a nearest-neighbor cost
formula and the exact constrained second variation. This rank result is
compatible with the stationary minimum; it proves no local improvement.

Its [PMP consequence and limitation](docs/LOCAL_FORWARD_PMP_LIMIT.md) shows
that a minimizing L1 window has a unique normalized normal adjoint, but local
first-order control tests plus an unrestricted periodic extension still do
not exclude all eligible windows. Standard forward polygons already supply
such windows with arbitrarily small local cost. Their whole periods cost
more than the octagon, so the whole-period budget cannot be dropped.

The [regular forward-window descent theorem](docs/LOCAL_FORWARD_REGULAR_DESCENT.md)
adds a second-order exclusion on part of that PMP domain. For every
`1<q<=5/4`, the state-cyclic reference has an exact endpoint-preserving,
strictly cheaper six-piece `012012` replacement. The constrained Hessian
sign is proved uniformly over the stated interval, and the improvement
persists in an open neighborhood of each reference. In particular, all
standard forward windows with at least seven pieces in their full period
are covered. The neighborhood sizes are not uniform near q=1; general
asymmetric L1 remains open. The standard closed family was already excluded
by its cost comparison, so this is additional local information.

[LOCAL_REVERSE_SIX](docs/LOCAL_REVERSE_SIX.md) proves a seven-piece strict
improvement for every q>1 in the equal-factor, state-cyclic reverse six-arc
family. The proof fixes the initial state, corrects both terminal endpoints
exactly, and proves the cost derivative is negative by an elementary logarithm
inequality. It requires neither the whole-word endpoint F=R nor numerical
optimization. This is a proper subfamily of L2; the full eight-dimensional
L2 target remains open; this subfamily does not repair the refuted L3 premise.

The [exact L3 strong local minimum](docs/LOCAL_L3_STRONG_MINIMUM.md) also
satisfies the complete input domain. Its full-arc control inequalities and
positive constrained second variation imply strict strong local optimality
by a published sufficient theorem, with the free-time conversion made
explicit. Arbitrary nearby controls do not improve this example. A distant
cheaper replacement is still possible, so this records a failed local method
for that particular input. An [exact finite reproducer](explorations/local_l3_exact_certificate.py)
checks the displayed algebra; the interval signs are proved in the hand note.

The separate [small-window L3 counterexample](docs/LOCAL_REVERSE_SIX_OBSTRUCTION.md)
proves a stronger, global statement with a fixed piece limit: some eligible
`021210` windows, of arbitrarily small cost, admit **no cheaper replacement
with at most six pieces**, regardless of word or elapsed time. The proof uses
an exact edge lower bound, compactness, and two endpoint coordinates, and has
received independent hand review. The subsequent global continuation theorem
excludes this family from any closed PMP occurrence. The result refutes the proposed sufficient local
lemma; it does not refute Reinhardt or Hales's geometrically embedded conjecture.

The [all-control strengthening](docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
shows that sufficiently small members of that same family minimize cost for
their fixed endpoints among **all measurable simplex controls and all terminal
times**. It checks a published strong-optimality theorem on one fixed padded
reference, then uses compactness and the exact edge dual to rule out cheaper
competitors for its small trims. The theorem transfer and limiting argument
received independent hand reviews. More replacement pieces do not fix the
failed local lemma; additional global-minimizer information is required.

The [complete-window PMP lemma](docs/MINIMIZER_WINDOW_PMP.md) supplies one
such necessary restriction: a selected window begins and ends at genuine
switches, so an inactive Hamiltonian must tie at each end. Full endpoint
rank fixes the normalized adjoint and shows that the exact L1 input and
the sufficiently small padded L3 examples fail both ties. They cannot
be the selected six complete pieces of a minimizer. This does not exclude
arbitrary cuts inside longer arcs or prove a replacement theorem on the
remaining domain.

For L1, the [explicit boundary filter](docs/LOCAL_FORWARD_ENDPOINT_FILTER.md)
reduces those four gaps to two scalar interval-endpoint tests. It also proves
that asymmetric eligible local-PMP windows with both external ties persist
near the standard forward family. Thus the added condition is effective
against the displayed obstructions, but cannot justify an equal-factor
classification.

The [PMP continuation analysis](docs/PADDED_L3_PMP_CONTINUATION.md) tests
whether the padded counterexamples can be completed to genuine outer arcs.
For all sufficiently small cores, their unique lift reaches the strict-star
boundary before either next Hamiltonian tie. Thus extending those pads does
not produce a surviving complete-window candidate. This is a proof for that
family, with an existential smallness threshold, not a universal L3 exclusion.

The [full-domain L3 rank theorem](docs/LOCAL_MIXED_SIX_RANK.md) proves endpoint
rank five for every positive strict-star `021210` input. Three independent
edge directions and two independent normal columns cover arbitrary outer
arc lengths and unequal states. Thus every stationary L3 input has one
normalized endpoint covector, and a minimizing window cannot use an abnormal
lift. This is a rank theorem; the original broad-domain replacement target
remains false.

The [L5 endpoint theorem](docs/LOCAL_L5_ENDPOINT_RANK.md) proves rank five
already for the prefix `02101`, hence throughout the full `021012` domain.
Its paired image is transverse to the state-stabilizer line by a strict-star
sign. Thus full-domain rank and normalized-adjoint uniqueness are established
for L1, L3, L4, and L5. The [exact L2 exception](docs/LOCAL_L2_RANK_DROP.md)
has actual rank four, with six positive factors and whole-arc strict star,
but its cost is proved greater than pi. Thus unrestricted L2 rank five is
false; rank on the competitive sublevel remains unresolved. None of these
rank results proves a cost improvement.

The [L4 variation certificate](docs/LOCAL_SIX_VARIATION.md) proves that the
`010201` endpoint map has rank five throughout its positive-factor domain.
It also exhibits an eligible stationary family for which every one of the
five compensated missing-control switch needles is strictly unfavorable.
The proof uses exact endpoint derivatives, rational logarithm bounds, and
whole-arc Bernstein sector certificates. It rules out a switch-only descent
criterion; the universal L4 replacement statement remains open.

## Earlier comparison results retained

The [closed-period index theorem](docs/GLOBAL_FORWARD_INDEX.md) gives a
separate uniform method check: the standard forward family with N=3k+1
has at least 2(k-1) negative constrained directions when its initial
state varies and both period endpoints remain exact. For k>=2 these
integrate to actual cheaper nearby closed trajectories. This family was
already excluded by its cost comparison; the result does not classify
asymmetric forward words or add another excluded global class.

The source notes supply a full asymmetric hand comparison for every admissible
trajectory representable with at most five positive-duration vertex pieces,
including equality within that class. They also compare two complete closed
six-piece orbits and both standard equal-arc regular polygon families. These
results do not bound the complexity of every minimizer.

| Mathematical asset | Hand proof |
| --- | --- |
| Complete four-piece comparison | [FOUR_LINK_HAND_PROOF](docs/FOUR_LINK_HAND_PROOF.md) |
| Five-piece coverage and noncyclic comparison | [FIVE_ARC_PROGRESS](docs/FIVE_ARC_PROGRESS.md) |
| Reverse five-piece comparison and exact minimum | [REVERSE_FIVE_ARC](docs/REVERSE_FIVE_ARC.md), [REVERSE_FIVE_MINIMUM](docs/REVERSE_FIVE_MINIMUM.md) |
| Arbitrary-length local forward-alternation exclusion | [FORWARD_ALTERNATION_EXCLUSION](docs/FORWARD_ALTERNATION_EXCLUSION.md) |
| Closed six-piece comparisons | [010202](docs/SIX_ARC_010202.md), [reverse-block deformation](docs/SIX_ARC_REVERSE_BLOCK.md), [012012](docs/SIX_ARC_012012.md) |
| Standard regular families of arbitrary size | [REGULAR_FAMILY_COMPARISON](docs/REGULAR_FAMILY_COMPARISON.md) |
| Fixed edges, word ordering, and exact holonomy | [SWITCHING_WORDS](docs/SWITCHING_WORDS.md), [VERTEX_WORD_REDUCTION](docs/VERTEX_WORD_REDUCTION.md), [WORD_HOLONOMY](docs/WORD_HOLONOMY.md) |
| Circle and near-circle exclusions | [CIRCLE_VARIATION](docs/CIRCLE_VARIATION.md), [NEAR_CIRCLE_BOUND](docs/NEAR_CIRCLE_BOUND.md) |

The remaining closed six-piece orbit [012102](docs/SIX_ARC_012102.md) is still
uncompared. Its investigation is paused unless it directly closes a uniform
reduction input. Its archived [moment boundary arguments](docs/SIX_ARC_012102_MOMENTS.md)
prove two sufficient inequalities on all finite arc-vanishing boundary faces;
neither interior inequality is proved. In particular the completed CLOSED 012012 comparison does
not close the LOCAL 012012 target: a local endpoint is generally not R, and
its initial state cannot be varied when splicing into the surrounding path.

The exact candidate density is

\[
\delta_{\rm oct}=\frac{8-\sqrt{32}-\log 2}{\sqrt 8-1}.
\]

## Earlier constructive formalization

The uncompiled source development constructs actual worst-disk normalization,
boundary regularity, balanced representation, determinant time, measurable
controls, integral dynamics, cyclic endpoints, and area/cost correspondence.
It also reconstructs geometric competitors from low-cost admissible controls.
These reduction implementations are not new exclusions of arbitrary competitors.

The source-level target transfer is `ReinhardtConjecture ↔ ControlLowerBound`.
Both the unrestricted lower bound and global affine rigidity remain open.
The detailed historical declaration inventory and audit are linked from the
current [source map](SOURCE_MAP.md) and [audit checklist](DEEP_AUDIT_CHECKLIST.md).
All mathematical proof files and concurrent contributions are retained.

## Working records and reproducibility

[CHECKLIST.md](CHECKLIST.md) is the controlling progress ledger.
[AGENTS.md](AGENTS.md) records the boundedness-first working agreement.
[GLOBAL_CALIBRATION](docs/GLOBAL_CALIBRATION.md) and
[LOCAL_SHORTENING_OBSTRUCTION](docs/LOCAL_SHORTENING_OBSTRUCTION.md) retain failed
shortcuts. Do not retry them without changing their failed premises.

The [local-fiber numerical probe](explorations/local_six_fiber_probe.py) is an
incomplete diagnostic, not an analytic exclusion. Its numerical bounds and
solver failures are explicitly recorded in the audit. Computer assistance is
allowed for direction; the eventual proof must have a complete hand argument.

Dependencies remain pinned to `lean4-smoothed-polygon`
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f` and mathlib
`9d581dfff2e41de989072ea63abf3daf69311520`, with Lean `v4.36.0-rc2`.
Access to the reference repository is required. Lake resolution, typechecking,
CI, and kernel validation were not run. See [CREDITS.md](CREDITS.md).

The complete pre-reorientation narrative remains in
[the earlier README](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/README.md).
Its mathematical results are retained; its suggested next tasks are superseded.
