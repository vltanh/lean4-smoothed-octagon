# Source map: the bounded-reduction checkpoint

Date: 2026-11-07. No Lean declaration was added or modified for this checkpoint.
The earlier full declaration-by-declaration map is preserved at
[798a7e1 / SOURCE_MAP.md](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/SOURCE_MAP.md).
All corresponding proof files remain in the repository. The current ledger
supersedes earlier recommendations to continue by increasing whole-word length.

## New hand reduction

| Statement | Exact source and status |
| --- | --- |
| Exact strong local minimum within the eligible L3 domain | [LOCAL_L3_STRONG_MINIMUM](docs/LOCAL_L3_STRONG_MINIMUM.md): exact endpoint, sector and cost certificates, positive constrained Hessian, all-arc Hamiltonian signs, and a checked free-time application of ASZ Theorem 2.6. Rules out universal nearby improvement, including arbitrary nearby controls; distant replacement and full L3 remain open. The [exact reproducer](explorations/local_l3_exact_certificate.py) is supplementary. |
| Full-domain endpoint rank for L1 | [LOCAL_FORWARD_RANK](docs/LOCAL_FORWARD_RANK.md): active-margin coordinates, exact cost action, and a hand determinant sign proof of rank five everywhere on the positive strict-star domain. Two independent hand reviews passed. No cost exclusion or boundary conditioning estimate. |
| Exact obstruction to universal nearby same-word L1 descent | [LOCAL_FORWARD_SIX](docs/LOCAL_FORWARD_SIX.md): an eligible `012012` input with rank-five endpoint map and a strict constrained local minimum. Full L1 remains open. The [exact checker](explorations/local_forward_stationary_obstruction.py) is supplementary. |
| P0: minimizer-window eligibility and finite-piece geometric splice | [MINIMIZER_WINDOW_AUDIT](docs/MINIMIZER_WINDOW_AUDIT.md): hand proof, using Hales--Vajjha Theorem 16.3.1 and balanced-disk correspondence; sector normalization and winding are proved explicitly. Independent premises and equality-transfer reviews passed; exact octagon trajectory and linear equivalence are displayed. The entire through-five algebra was not re-audited. |
| Five-template coverage for every minimizing N>=6 | [BOUNDED_REDUCTION, Sections 1-2](docs/BOUNDED_REDUCTION.md): complete independently reviewed hand run argument, conditional on the already supplied forward-alternation exclusion. |
| Local strict improvements imply N<=5 and then global minimality/rigidity | Same note, Section 3: proved conditional implication; all five new analytic premises are open. |
| Eight-coordinate input domains | Same note, Section 4: initial margins, exact factor updates, full-arc signs, cost, and geometric sector tests. |
| Full local endpoint map | Same note, Section 5: preserve tangent product AND terminal state with initial state fixed; generally the tangent endpoint is not R. |
| Exact elimination of three endpoint equations | Same note, Section 6: explicit inverses for both orientations of a positive distinct-label triple. LOCAL_FORWARD_RANK resolves the remaining rank as two throughout the positive L1 domain; singular loci for the other four templates remain open. |
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
