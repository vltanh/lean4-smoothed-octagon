# Smoothed octagon: a hand proof

**The hand proof of the sharp Reinhardt cost bound and affine equality
case is complete under the explicitly declared classical geometric and
maximum-principle inputs.** All uniform period exclusions and the final
assembly have separate internal mathematical reviews. Start with the
[final theorem](docs/HAND_COST_EQUALITY_THEOREM.md).

## Main result

Let
\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]
Every centrally symmetric planar convex disk \(K\) satisfies
\[
\delta(K)\ge\delta_{\rm oct},
\]
with equality precisely for the invertible affine images of the
concrete smoothed octagon. The control formulation proves
\(C\ge\sqrt{12}\,\delta_{\rm oct}\) for every trajectory in the original
integral admissible class, including arbitrary measurable controls.

The [final theorem](docs/HAND_COST_EQUALITY_THEOREM.md) states the
quantifiers, derives a finite normal minimizing representation in the
required order, and transports equality back to the original disk.
Its Section 7 lists the external mathematical premises. Internal
review is distinct from external peer review and Lean kernel verification.

## Read the completed argument

1. [Final cost and affine equality theorem](docs/HAND_COST_EQUALITY_THEOREM.md).
2. [Global dependency audit](docs/HAND_GLOBAL_DEPENDENCY_AUDIT.md).
3. [Finite representation and whole-period review](docs/HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md).
4. [Unrestricted inequality and original-disk equality review](docs/HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md).
5. [Accepted status](docs/HAND_PROOF_STATUS.md), [finite gate record](docs/HAND_ONLY_COMPLETION_PLAN.md), and [source map](SOURCE_MAP.md).

The following exclusions are applied to an eligible competitive finite
normal minimizing period with \(N\ge6\) positive pieces.

| Complete-period class | Hand argument |
|---|---|
| Entirely reverse | [Reverse-period exclusion](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| Entirely forward, at least six positive pieces | [Forward hand theorem](docs/HAND_FORWARD_PERIOD_EXCLUSION.md), with [norm review](docs/HAND_FORWARD_NORM_AUDIT.md) |
| Mixed: smaller adjacent turn on a short forward run | [Smaller-short hand theorem](docs/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md), with [period review](docs/MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md) and [scope review](docs/MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md) |
| Mixed: smaller adjacent turn on a nonshort run, next genuine switch forward | [Nonshort forward theorem](docs/MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md), with [review](docs/MIXED_NONSHORT_FORWARD_HAND_AUDIT.md) |
| Mixed: smaller adjacent turn on a nonshort run, next genuine switch reverse | [Nonshort reverse theorem](docs/MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md), with [review](docs/MIXED_NONSHORT_REVERSE_HAND_AUDIT.md) |

The [mixed minimum-structure theorem](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
and [small-forward-minimum hand proof](docs/SMALL_FORWARD_MINIMUM_HAND_PROOF.md)
justify the choice of centre. The smaller-turn split covers mixed
periods even when both adjacent forward runs are short. These exclusions
force \(N\le5\). The [direct terminal count](docs/HAND_TERMINAL_COVERAGE.md)
leaves only \(0120\) and \(01020\); the
[analytic terminal comparisons](docs/SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
give the unique four-piece equality and strict five-piece cost excess.

## The completed smaller-short step

The actual short domain satisfies
\[
2<x<13/6,\qquad 0\le\delta=\beta/x-1<1/19,\qquad
\alpha=1+\eta\delta,\quad13/5\le\eta\le3.
\]
The [extended Casimir floor](docs/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md)
proves \(\Gamma_{\rm actual}>1829/10000\) throughout the required
interval, including the former gap beyond \(15/7\). Its
[six derivative signs](docs/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
have explicit product bounds and a separate
[review](docs/MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md).

The [actual-root comparison](docs/MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
then proves the required negative physical shear. The
[completion-cost theorem](docs/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
makes the original full-period cost strictly greater than the octagon
cost. The [whole-period theorem](docs/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md)
and its two reviews verify every caller hypothesis, equal-turn choices,
zero displacement, positive unequal durations and the twisted seam.

Every comparison retains the original common normal covector and one
whole-period cost budget. Artificial scalar points receive no unproved
physical closure, root, outgoing norm floor or competitive cap.

## Proof standard and preserved computational baseline

The hand route uses explicit analytic inequalities, finite polynomial
identities and elementary sign bounds. Symbolic or numerical calculations
may check discovery and transcription; executing a cover or a sign script
is not a premise. No growing word catalogue or refuted unconditional
local-shortening assertion is used.

The earlier [computer-assisted assembly](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md),
[its independent audit](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md), and
[certificate replay records](docs/CERTIFICATE_REPLAY.md) remain preserved.
Their arithmetic execution boundary is separate from the completed hand
route. Historical notes may describe earlier open gates or superseded
methods; the current reading path is [docs/ACTIVE_MAP.md](docs/ACTIVE_MAP.md).

- docs/: theorem statements, explicit hand arguments and independent reviews.
- explorations/: discovery calculations, transcription checks and historical frozen covers.
- docs/legacy/ and explorations/legacy/: prior plans, rejected shortcuts and archived investigations.
- SmoothedOctagon/*.lean and dependency pins: existing formalization drafts, unchanged.

No Lean compilation, Lake, typechecking or CI was run in this completion.
