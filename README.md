# Research toward the Reinhardt conjecture

This project studies whether the concrete smoothed octagon globally minimizes
the greatest packing density among centrally symmetric convex disks, with
uniqueness up to affine equivalence. It reuses the geometry of
[vltanh/lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon).

**The unrestricted conjecture is not proved. Lean compilation and kernel
validation have not been run. New formalization infrastructure is paused.**

## Current priority: establish boundedness before more enumeration

**Next-session handoff:** [five-template action plan](docs/FIVE_TEMPLATE_HANDOFF.md).
Read it **before** attacking any additional case. The prerequisite
[P0 audit is complete as a hand proof](docs/MINIMIZER_WINDOW_AUDIT.md):
it verifies minimizer eligibility, twisted seams, normalized geometric sectors,
and the finite-piece geometric/control splice. The next target is L1 as a **local** endpoint-preserving
cost improvement, including stationary endpoint fibers. L1 has full endpoint
rank throughout its positive domain, as proved below. Continue
with L2–L5 only against the same strict acceptance criteria. All five
universal local improvements remain **OPEN** (0/5). Do not resume
increasing-length whole-trajectory enumeration.

The P0 note also records the corrected terminal conjugation and the explicit
equality transfer to the concrete octagon. Independent premises and equality
reviews found no additional gap in that conditional transfer. The global
complexity bound is still required before it proves unrestricted rigidity.


The user requested a bounded set of cases before continuing case-by-case
comparisons. The current research target is therefore a uniform complexity
reduction, not the next arc count.

[BOUNDED_REDUCTION.md](docs/BOUNDED_REDUCTION.md) proves a hand coverage theorem:
using the established local forward-alternation exclusion, any finite cyclically
reduced minimizing trajectory with at least six positive vertex pieces contains,
up to cyclic relabeling, one of these six-piece windows:

| Local template | Sign description | Universal improvement status |
| --- | --- | --- |
| 012012 | Five forward switches | Open |
| 021021 | Five reverse switches | Open |
| 021210 | One forward switch between two reverse pairs | Open |
| 010201 | Reverse run of length two followed by at least two forward switches | Open |
| 021012 | Reverse run of at least three followed by at least two forward switches | Open |

Each window has eight free input coordinates: two initial-state coordinates
and six positive factors. Its eligibility and endpoint equations are explicit.
Proving a strictly cheaper replacement with the same frame and state endpoints
for each entire local domain would imply that every global minimizer has at
most five pieces. A replacement may still use six pieces; strict cost decrease
alone contradicts minimality. Actual six-to-five shortening is not necessary.

The existing through-five comparison and equality case would then finish the
hand proof. **Coverage and this conditional implication are proved; the five
analytic exclusions and hence the uniform bound remain open.** No finite
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

[LOCAL_REVERSE_SIX](docs/LOCAL_REVERSE_SIX.md) proves a seven-piece strict
improvement for every q>1 in the equal-factor, state-cyclic reverse six-arc
family. The proof fixes the initial state, corrects both terminal endpoints
exactly, and proves the cost derivative is negative by an elementary logarithm
inequality. It requires neither the whole-word endpoint F=R nor numerical
optimization. This is a proper subfamily of L2; the full eight-dimensional
target and the other four local targets remain open.

The [exact L3 strong local minimum](docs/LOCAL_L3_STRONG_MINIMUM.md) also
satisfies the complete input domain. Its full-arc control inequalities and
positive constrained second variation imply strict strong local optimality
by a published sufficient theorem, with the free-time conversion made
explicit. Arbitrary nearby controls do not improve this example. A distant
cheaper replacement is still possible, so this records a failed local method
and leaves L3 open. An [exact finite reproducer](explorations/local_l3_exact_certificate.py)
checks the displayed algebra; the interval signs are proved in the hand note.

The [L4 variation certificate](docs/LOCAL_SIX_VARIATION.md) proves that the
`010201` endpoint map has rank five throughout its positive-factor domain.
It also exhibits an eligible stationary family for which every one of the
five compensated missing-control switch needles is strictly unfavorable.
The proof uses exact endpoint derivatives, rational logarithm bounds, and
whole-arc Bernstein sector certificates. It rules out a switch-only descent
criterion; the universal L4 replacement statement remains open.

## Earlier comparison results retained

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

