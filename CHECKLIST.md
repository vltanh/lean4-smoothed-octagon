# Proof ledger: bounded reduction before further case comparisons

**NEXT WORKER: [FIVE-TEMPLATE HANDOFF](docs/FIVE_TEMPLATE_HANDOFF.md).**
Begin with **P0: validate the finiteness, twisted-seam, local-sector, and
geometric-bridge premises**, then attack **L1 (012012)** as a *universal local
endpoint-preserving improvement*; test for obstructions before extending to
L2–L5. The proof acceptance criteria, exact eight-variable domain, local
endpoint elimination, singular-rank obligations, and stop/failure rules are
spelled out there. **No new whole-word enumeration. No claim that the five
universal statements are true. L1–L5: 0/5 proved.**

Status date: **2026-11-06**. New Lean infrastructure, compilation, Lake, and CI remain paused.

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
| Coverage | Every cyclically reduced minimizing word with N>=6 contains one of the five specified six-arc windows, using the established forward-alternation exclusion. | Hand proof independently reviewed, with a separate finite-graph computational cross-check. No new cost class excluded by this alone. |
| L1: 012012 | Strictly cheaper endpoint-preserving replacement on the entire eligible local domain. | **Open.** The closed six-piece comparison does not prove this local claim. |
| L2: 021021 | Same universal local improvement for five consecutive reverse switches. | **Open.** A regular-family comparison does not cover asymmetric local endpoints. |
| L3: 021210 | Same universal local improvement for a single forward switch between two reverse pairs. | **Open.** |
| L4: 010201 | Same universal local improvement at a reverse run of length two followed by at least two forward switches. | **Open.** |
| L5: 021012 | Same universal local improvement at a reverse run of at least three followed by at least two forward switches. | **Open.** |
| Uniform bound | Deduce N<=5 for every global minimizer from all five local improvements and the published finite bang-bang reduction. | Conditional implication proved; its five analytic premises remain open. |
| Global comparison and equality | Apply the existing through-five cost comparison and equality classification after the uniform bound is proved. | Conditional only. Global minimality and affine rigidity remain open. |
| Kernel validation | Compile and inspect the final statements and dependencies. | Deferred under the current workflow. |

**Analytic exclusions closed in this five-template package: 0/5.** This is a
count of precisely stated local targets, not a percentage of the conjecture
or an assertion that the targets have equal difficulty.

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
setup, not a proof that a decreasing direction always exists. Rank-zero,
rank-one, and degenerate stationary points remain part of each target.

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

## Literature and validation boundary

The hand research may use Hales-Vajjha, Theorem 16.3.1, for finite bang-bang
minimizers. That is not a uniform numerical bound; Appendix B.4 explicitly
leaves such a bound open. Hales's 2011 Section 7.6 already proposes link
reduction. The new contribution is the five-template coverage and precise
finite sufficient package, not a claim that link reduction has been proved.

See [SOURCE_MAP.md](SOURCE_MAP.md) and
[DEEP_AUDIT_CHECKLIST.md](DEEP_AUDIT_CHECKLIST.md). No new Lean theorem,
compilation, typechecking, Lake command, kernel audit, or CI run was performed.
