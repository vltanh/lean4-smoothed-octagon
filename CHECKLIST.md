# Proof ledger: bounded reduction before further case comparisons

**NEXT WORKER: [FIVE-TEMPLATE HANDOFF](docs/FIVE_TEMPLATE_HANDOFF.md).**
**P0 is complete at the hand-proof level:** see
[the minimizer-window audit](docs/MINIMIZER_WINDOW_AUDIT.md) for finiteness,
twisted rebasing, normalized sectors, and the finite-piece geometric splice.
Attack **L1 (012012)** as a *universal local
endpoint-preserving improvement*; test for obstructions before extending to
L2–L5. The proof acceptance criteria, exact eight-variable domain, local
endpoint elimination, singular-rank obligations, and stop/failure rules are
spelled out there. **No new whole-word enumeration. No claim that the five
universal statements are true. L1–L5: 0/5 proved.**

Status date: **2026-11-07**. New Lean infrastructure, compilation, Lake, and CI remain paused.

The user requested a bounded set of cases before further enumeration. This ledger
therefore supersedes the earlier next-six/next-seven progression. The full prior
ledger and chronological source history remain at
[798a7e1](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/CHECKLIST.md).
No mathematical proof file or earlier contribution has been removed.

## The controlling checkpoint

**Prove a uniform bound on the complexity of every global minimizer before
expanding whole-trajectory case coverage.** A finite list of open lemmas is not
itself such a bound.

The candidate route is the fixed five-template package in
[docs/BOUNDED_REDUCTION.md](docs/BOUNDED_REDUCTION.md). It has a proved coverage
argument and five unresolved analytic inputs. It is not an unconditional
boundedness theorem.

| Component | Exact completion condition | Status |
| --- | --- | --- |
| P0: minimizer eligibility and splice | Prove every selected window meets the entire stated domain and every cheaper finite strict-star splice gives a geometric competitor. | **Hand proof complete**, using the named published reduction and retained through-five comparison certificates. Does not exclude a new cost class. |
| Coverage | Every cyclically reduced minimizing word with N>=6 contains one of the five specified six-arc windows, using the established forward-alternation exclusion. | Hand proof independently reviewed, with a separate finite-graph computational cross-check. No new cost class excluded by this alone. |
| L1: 012012 | Strictly cheaper endpoint-preserving replacement on the entire eligible local domain. | **Open.** An exact eligible stationary minimum disproves universal nearby same-word descent; different-word or nonlocal improvements remain possible. See [LOCAL_FORWARD_SIX](docs/LOCAL_FORWARD_SIX.md). |
| L2: 021021 | Same universal local improvement for five consecutive reverse switches. | **Open.** A regular-family comparison does not cover asymmetric local endpoints. |
| L3: 021210 | Same universal local improvement for a single forward switch between two reverse pairs. | **Open.** An exact eligible strict strong local minimum rules out universal nearby improvement, including arbitrary nearby controls. Distant replacements remain possible; see [LOCAL_L3_STRONG_MINIMUM](docs/LOCAL_L3_STRONG_MINIMUM.md). |
| L4: 010201 | Same universal local improvement at a reverse run of length two followed by at least two forward switches. | **Open.** |
| L5: 021012 | Same universal local improvement at a reverse run of at least three followed by at least two forward switches. | **Open.** |
| Uniform bound | Deduce N<=5 for every global minimizer from all five local improvements and the published finite bang-bang reduction. | Conditional implication proved; its five analytic premises remain open. |
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
comparison excludes a distant cheaper replacement. L3 remains open.

## What is fixed, rather than growing

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
setup, not a proof that a decreasing direction always exists. For L1 the
reduced state rank is two everywhere by LOCAL_FORWARD_RANK. Rank-zero and
rank-one loci remain obligations for L2–L5; stationary points remain part
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
  checked; its full algebra was not re-audited. L1--L5 remain open.
- `6076dc6`: proved the five-template coverage statement by a hand run argument;
  stated the exact local domains, endpoint map, suffix inverses, and conditional
  global conclusion. No analytic local case was marked closed.
- `498df52`: retained an exact finite transition-graph cross-check. All 32
  five-sign blocks are examined; 21 avoid the established +-+ exclusion.
  Removing the five target edges leaves a 12-vertex, 16-edge acyclic graph.
  This verifies coverage without testing a maximum total length.
- Ledger reorientation: freeze increasing-length comparisons; separate the
  proved finite coverage theorem from the five open universal cost statements.
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

The hand research may use Hales-Vajjha, Theorem 16.3.1, for finite bang-bang
minimizers. That is not a uniform numerical bound; Appendix B.4 explicitly
leaves such a bound open. Hales's 2011 Section 7.6 already proposes link
reduction. The new contribution is the five-template coverage and precise
finite sufficient package, not a claim that link reduction has been proved.

See [SOURCE_MAP.md](SOURCE_MAP.md) and
[DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md). No new Lean theorem,
compilation, typechecking, Lake command, kernel audit, or CI run was performed.
