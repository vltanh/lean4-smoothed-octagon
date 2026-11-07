# External-input boundary for finite bang-bang minimizers

Date: 2026-11-07. Source audit and certificate specification; no Lean, Lake,
typechecking, CI, or numerical trajectory computation was run for this note.

## 1. Finding and precise scope

The finite bang-bang theorem used by this repository is **an external
input**. The displayed arguments in the source contain numerical steps
that this repository has not independently certified. This audit does
not assert that the theorem is false, or that a certificate cannot exist
elsewhere. It identifies what was actually checked and what remains
outside our hand-proof boundary.

The [arXiv record](https://arxiv.org/abs/2405.04331), checked on the date
above, lists only v1, submitted 7 May 2024. This audit concerns that
version of Hales--Vajjha, *Packings of Smoothed Polygons*.

### Source observations

- [Section 14.4](https://arxiv.org/html/2405.04331v1#Ch14.S4) describes
  the unstable curve through a Mathematica approximation with 434 points.
  It explicitly distinguishes that computation from a possible rigorous
  interval-arithmetic calculation. The proof of Theorem 14.4.1 uses the
  curve's exit through the star boundary.
- [Section 16.1](https://arxiv.org/html/2405.04331v1#Ch16.S1), in the
  proof of Theorem 16.1.1, supports cell-image containments using numerical
  boundary images and Figures 16.1.1--16.1.4. This is a second enclosure
  obligation, distinct from the unstable-curve computation.
- [Section 16.4](https://arxiv.org/html/2405.04331v1#Ch16.S4) uses that
  containment order in the cluster-point argument.
  [Theorem 16.3.1](https://arxiv.org/html/2405.04331v1#Ch16.S3) invokes
  both the cluster theorem and Theorem 14.4.1 to exclude periodic
  chattering.

These observations concern the stated computational support. They do not
replace a review of the analytic arguments surrounding it. In particular,
a visually convincing plot and contraction observed near a fixed point
are not uniform error bounds for a continued invariant curve or for all
points of a cell face.

## 2. Exact effect on this repository

The following distinctions prevent an external theorem from being
silently promoted into a newly certified result.

| Repository argument | Dependence on the audited finite-switch input |
| --- | --- |
| Compactness of normalized minimizing lifts, through Section 4 of [GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md) | Independent of finite bang-bang representation. It uses the stated geometric, compact-state, PMP, and transversality inputs. |
| Avoidance of the full singular locus, Section 5 of that note | Uses Theorem 16.3.1 to supply a positive one-sided vertex arc at each time, then Lemma 8.3.4 to exclude its singular endpoint. |
| Uniform qualitative clearance, Section 6 | Follows from compactness and the preceding avoidance statement; therefore retains the finite-switch external input. |
| One common finite switch bound for actual global minimizers | Uses that qualitative clearance and the independently proved regular-domain counting theorem; therefore retains the same external input. |
| [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md), with a supplied numerical clearance and its stated hypotheses | Does not use Theorem 16.3.1 to prove the conditional count. The missing clearance must be supplied separately. |

The point of the first row is logical independence from this particular
input, not a claim that every other cited result has been re-proved here.
Likewise, the last row retains its explicitly stated edge-optimality and
state/coefficient hypotheses.

Taking Theorem 16.3.1 as an accepted external theorem gives the downstream
implications already recorded in the repository. Claiming an independent
hand verification of that theorem's computational ingredients would
require more than the present audit.

## 3. A rigorous escape certificate to obtain

Here is a concrete sufficient replacement for the unstable-curve step.
It is a specification of missing evidence, **not a completed certificate**.
Work in the source's blown-up switching section, with its actual
Reinhardt flow and its first-switch map.

First enclose a local unstable graph at the outward fixed point by proved
bounds. The enclosure must establish that every forward branch emerging
from that fixed point meets a specified compact fundamental segment of
the graph, up to the stated symmetries. A small error around one numerical
seed is insufficient: it must enclose the invariant graph itself. A
graph-transform estimate with explicit contraction and remainder bounds
would be one way to do this.

Next supply finitely many closed boxes or other explicitly described sets
covering the continuation of that segment. At each transition, certify:

1. The active control denominator stays bounded away from zero on the
   entire flow tube, so the chosen vertex flow is defined there.
2. The asserted next switch is the first switch: the active Hamiltonian
   dominates throughout the open arc; the specified competitor meets it
   at the terminal event; the third vertex has the required strict gap.
   Transversality or another explicit root-isolation argument must
   justify the event time and all endpoint cases.
3. The event map sends the entire incoming enclosure into the next one,
   with proved bounds on the elapsed time and accumulated error.

For the final tube, choose a star-boundary function

\[
\gamma_j(X)=-\operatorname{tr}(Z_jX).
\]

Prove that its first zero is reached in a bounded time while the same
vertex remains uniquely maximizing in the interior. A convenient strong
certificate would give an outward derivative bound
\(\dot\gamma_j\le-\beta<0\) near the crossing, keep the active
denominator positive, and exclude every competing switch before it.
There must be no unaccounted branch or earlier return to the initial
section.

These conditions imply escape for every trajectory in the enclosed
unstable segment: induction gives the certified sequence of events, and
the final maximizing arc reaches the boundary before a different control
can continue it inside the strict-star region. The local graph argument
then extends this conclusion to each corresponding trajectory emerging
from the fixed point. Time reversal supplies the incoming version.
This implication is elementary; the required graph and tube bounds are
the substantive missing part.

An analytic monotonicity or barrier proof could replace these enclosures.
Ordinary floating-point propagation, interpolation through finitely many
points, or numerical evaluation of switching gaps would not supply them.

## 4. The separate basin-containment obligation

The relevant finite target for the basin proof is a list of verified
inclusions for the closed cells and their refined subcells, including
their boundary identifications and one-sided map extensions. Each entry
must hold for **every** point in its specified domain. If a boundary-only
argument is used, its topological hypotheses must also be checked for
that map and that cell; continuity alone would not justify replacing an
interior inclusion by a boundary test.

Useful deliverables would be explicit parameterizations of the faces,
sign or interval bounds for the defining inequalities of each target
cell, and treatment of zero-switch-time, resultant, and discriminant
boundaries. A trapping region around the attracting fixed point needs
both invariant containment and a convergence argument on the region;
a linearization at the fixed point only controls a sufficiently small
neighborhood once entry into it has been proved.

This note has not re-created those enclosures or decided whether the
accompanying source calculations can be converted into them. The bounded
source check included the arXiv record and the authors' linked
[home page](https://kodyvajjha.github.io/) and
[announcement](https://jiggerwit.wordpress.com/2024/05/13/packings-of-smoothed-polygons/).
It did not locate a rigorous enclosure certificate there. That is a
statement about this search, not an assertion of nonexistence.

## 5. Why certifying escape still does not produce a numerical clearance

A certificate for the exact unstable graph repairs that specific input
to the finite bang-bang argument. It does not by itself exclude every
nearby periodic trajectory. Such a trajectory can start off the invariant
graph, pass near the singular locus, and leave the local chart through a
different part of its boundary. Local stable-manifold existence alone
does not bound that passage or its later return.

For the active quantitative gate, one needs a further **robust** statement
with numerical constants. One possible target is an explicit neighborhood
of the full normalized singular set such that every competitive closed
PMP lift entering it is forced into a certified exit tube, violates the
whole-period budget, or admits a proved decreasing variation. The proof
must cover all entrance directions, both time orientations where needed,
and the actual twisted state and costate seams. It must also control
returns from the complement of the local chart. A tube around the exact
unstable graph handles only one part of this requirement.

Finally convert the neighborhood to the norm used by
`QUANTITATIVE_REGULAR_SWITCH_BOUND.md`:

\[
\|(\lambda,\Lambda_1,W)(0)\|=1,
\qquad
D^2=\|X-J\|_F^2+
 \|\Lambda_1-\tfrac32\lambda J\|_F^2+\|W\|_F^2.
\]

The accepted quantitative input would be a stated rational
\(\varepsilon_0>0\) and a proof that every actual minimizer has a
normalized lift satisfying \(D\ge\varepsilon_0\) throughout its period.
Proving this for every normalized minimizing lift would be stronger and
also sufficient. Neither a positive minimum obtained abstractly by
compactness nor the exact-graph escape statement evaluates
\(\varepsilon_0\).

No numerical clearance, new unconditional finite bound, counterexample
to the source theorem, or resolution of Reinhardt is claimed by this audit.

Independent internal review reopened the arXiv record and the cited source
sections, checked both numerical dependencies and their downstream uses,
and reviewed the distinction between exact-graph escape and a robust
clearance certificate. No material issue was found in this audit's scope.
