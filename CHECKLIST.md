# Proof ledger and finite roadmap

Status date: **2026-11-06**. This is an active, uncompiled development.

## What is established in this PR

These are source deliverables, not kernel-certified milestones.

- [x] Reuse the actual octagon, its admissibility, exact density, and a worst disk from the
  pinned reference project. State global minimality and affine rigidity separately.
- [x] Give equivalent global closure criteria, including a density lower bound on any
  actual worst disk. The existence input is an upstream theorem, not an added hypothesis.
- [x] Supply a complete hand proof and Lean proof bodies for the new rational switching
  margin, including `(r-y)^3/8 ≤ hmaxF y r` throughout `2 ≤ y ≤ r ≤ 4`.
- [x] Transport the margin to the actual switching functions of normalized strong lifts:
  `χ₃₂(t) ≥ √3 t³/2` and `χ₃₁(t) ≥ √3 (t_sw-t)³/2` on the whole segment.
- [x] Construct a density-preserving affine normalization of an actual worst disk, with
  its critical contact midpoints at the sixth roots of unity. Prove the normalized area
  objective and pointwise six-contact configurations.
- [x] Construct the actual continuous six-contact boundary trace, with common period
  `2π`, simple traversal, full boundary coverage, and the prescribed initial values.
- [x] Construct a continuous normalized supporting covector field from unique support
  lines, with domination of the gauge and no assumed smooth boundary.
- [x] Prove the radial boundary is a regular positive `C¹` curve from that supporting
  field, including the exact orientation formula `det(b,b') = 1 / gauge(dir)^2`.
- [x] Construct a global increasing `C¹` arclength change of parameter with positive
  derivative, exact period drift, and Euclidean unit speed.
- [x] Assemble all balanced-pair fields for a normalized actual worst disk and prove it
  minimizes balanced circle area. Prove conversely that a balanced circle minimizer is
  an actual worst disk.
- [x] Transfer global minimality and affine rigidity to exact unrestricted balanced
  targets, with no assumed minimizer-reduction theorem.
- [x] Construct the global determinant-one contact frame and the positive periodic clock
  making its logarithmic derivative a determinant-one star state with Lipschitz entries.
- [x] Construct an everywhere-simplex measurable curvature control and prove both integral
  state equations, using pointwise convex curvature and the absolutely-continuous FTC.
- [x] Construct the actual positive `C¹` successor of all six contact curves and prove
  that its sixth iterate advances by exactly one full period.
- [x] Preserve all balanced-pair fields in determinant time and derive the uniform
  cyclic contact shift, initial identity frame, and both control terminal conditions.
- [x] Map every mathematical claim to source declarations and record the validation boundary.
- [ ] Compile and inspect kernel dependencies. **Not run under the current workflow.**

The existing candidate construction and its qualitative switching signs are upstream work.
They are not counted as newly closed conjecture cases. The new cubic margin strengthens one
local estimate; it does not establish global optimality.

## Global obligations

This is a finite list of obligations, **not** a claim that the remaining bodies form a finite
list, that the tasks have comparable difficulty, or that they are all routine formalization.

| Gate | Exact completion condition | Present status |
| --- | --- | --- |
| G1 — Fix the global target | Use the existing greatest packing density of congruent copies for every centrally symmetric convex disk; identify the concrete octagon and state affine rigidity separately. | Source draft supplied in `Problem.lean`; validation deferred. |
| G2 — Normalize an actual minimizer | Construct a balanced circle representation of an actual worst disk, preserving the relevant density and supplying every boundary parametrization hypothesis. | Source proof supplied through `worstDisk_balanced_normalization` in `BalancedReduction.lean`. Every parametrization hypothesis is constructed. Kernel validation remains deferred. |
| G3 — Justify the chosen reduction | If using the smoothed-polygon route, prove the needed optimal-control, extremal-lift, and Mahler First bridges for the minimizer from G2. | In progress. The matrix frame and determinant clock are constructed. Cyclic contact time, the admissible-competitor correspondence, and the later reduction remain to be integrated or proved. |
| G4 — Make the global comparison exhaustive | Prove either a direct inequality covering all normalized competitors, or an explicit uniform switch/side bound plus coverage of all words, parameter ranges, limits, and degeneracies. | Open research obligation. No finite case list is available yet. |
| G5 — Prove the octagon lower bound | Discharge `octagonDensity ≤ greatestPackingDensity K` for a genuine worst disk and apply `reinhardtConjecture_of_worst_disk`. | Open. Comparisons within the regular `(6k+2)` family cannot close this gate. |
| G6 — Classify equality | Prove `AffineRigidity`: every worst disk is an invertible linear image of the centered octagon. | Open; not implied by G5. |
| V — Validate the final theorem | Compile and audit `FullReinhardtConjecture`, its exact statement, and its complete dependency closure in the agreed kernel workflow. | Deferred; requires a change to the current no-compilation policy. |

G4 has two possible routes. A direct global inequality can bypass a finite classification;
otherwise the uniform bound and coverage proof must precede any claim of exhaustive case
enumeration. Merely showing that each minimizer has finitely many switches is insufficient.

## G2 construction ledger

All completed entries below mean source proof bodies and hand arguments have been supplied;
none has yet been checked by Lean. Substeps are not separate global conjecture cases.

| Step | Required output | Status |
| --- | --- | --- |
| G2a — Affine normalization | Starting with an actual worst disk, construct a normalized image, preserve its worst status and density, and identify density as area divided by `2 * √3`. | Source draft supplied in `Normalization.lean`. |
| G2b — Continuous boundary trace | Construct six continuous contact curves, a common period, simple traversal, full boundary coverage, and the initial sixth-root values. | Source draft supplied in `BoundaryTrace.lean`; no curve is assumed as an input. |
| G2c — Regular radial parametrization | Deduce a positive regular `C¹` polar boundary curve from the actual minimizer's unique supporting line at every boundary point. | Source proofs supplied in `SupportNormal.lean` and `RadialRegularity.lean`, including the bilateral slope squeeze and exact orientation formula. |
| G2d — Common arclength parameter | Construct a global increasing periodic change of parameter with Euclidean unit speed for curve zero. | Source proof supplied in `ArcLength.lean`; the speed is the explicit Euclidean coordinate formula. |
| G2e — Balanced assembly | Apply the upstream regularity, Lipschitz, star, and curvature lemmas; transport the period, simplicity, coverage, and initial values through the common change of parameter. | Source proof supplied in `BalancedReduction.lean`, including the balanced-area minimizer property and its converse. |

## Exact remaining comparison

`BalancedTargets.lean` proves the source equivalences

```lean
ReinhardtConjecture ↔ BalancedAreaLowerBound
AffineRigidity ↔ BalancedAffineRigidity
FullReinhardtConjecture ↔ BalancedAreaLowerBound ∧ BalancedAffineRigidity
```

`BalancedAreaLowerBound` quantifies over **every** balanced disk in circle representation.
`BalancedAffineRigidity` quantifies over **every** balanced circle minimizer. Both are still
open propositions. Their equivalence to the original targets does not establish either one.

## G3 construction ledger

| Step | Required output | Status |
| --- | --- | --- |
| G3a — Matrix frame | Construct the `SL₂` frame of the actual contact curve and its positive-determinant logarithmic derivative. | Source proof supplied in `DeterminantClock.lean`, with explicit frame, derivative, and star signs. |
| G3b — Determinant clock | Construct a global positive time change making the logarithmic derivative determinant one, with the needed regularity. | Source proof supplied in `DeterminantClock.lean`; the clock assumed by upstream Proposition 3.1.9 is now constructed. |
| G3c — Cyclic boundary and cost | Prove the common cyclic shift `σ_j(t+tf)=σ_(j+1)(t)` and the exact area-cost identity in the new parameter. | The actual successor, balanced determinant-time representation, and uniform shift are constructed through `CyclicClock.lean`. The exact area-cost assembly is next. |
| G3d — Admissible comparison | Supply measurable simplex controls and integral state trajectories, then justify comparison with every control-admissible competitor or a precisely restricted equivalent class. | The measurable control, integral trajectory, and cyclic endpoint conditions are constructed. Reverse comparison with every admissible control remains open. |
| G3e — Extremals and polygon reduction | Obtain the relevant Pontryagin lift and the complete Mahler First reduction for the actual minimizer. | Open in the pinned formalization. |

## Next bounded mathematical task

Continue **G3c–G3d** with the actual balanced minimizer and determinant clock now constructed:
build the cyclic shift and measurable integral control needed by the area-cost and admissibility
theorems. Keep G3d's competitor correspondence explicit. A geometric area minimizer cannot
be advertised as a minimizer over all control trajectories until that comparison is proved.

## Progress entries

- **2026-11-06, foundations:** concrete global target, equivalent closure criteria, exact
  scalar margin, and strong-lift transport supplied in three initial commits.
- **2026-11-06, G2a:** actual-minimizer affine normalization and normalized area objective
  supplied; commit `2c7dd88`.
- **2026-11-06, G2b:** actual continuous six-contact trace supplied, including common period,
  simplicity, coverage, and circle representation; commit `2ccfe60`.
- **2026-11-06, G2c support field:** unique normalized supporting covectors constructed;
  a uniform compact box and uniqueness of cluster points prove continuity; commit `b01624d`.
- **2026-11-06, G2c regularity:** bilateral supporting-slope squeeze differentiates the
  angular gauge. The radial curve is `C¹`, nonvanishing, and positively oriented;
  commit `abe06e2`.
- **2026-11-06, G2d:** integrate the positive periodic Euclidean speed, prove global
  surjectivity, construct the inverse order isomorphism, and prove unit speed and period drift;
  commit `eb339a6`.
- **2026-11-06, G2e and target transfer:** all balanced-pair fields assembled from an actual
  worst disk, with density preserved. Balanced area minimizers and actual packing minimizers
  are linked in both directions; commit `4ed2dda`. The unrestricted area bound and rigidity
  remain open.
- **2026-11-06, G3a–G3b:** construct the contact frame, raw logarithmic derivative,
  positive determinant speed, and inverse clock. A proved covariance identity conjugates
  a positive sixfold contact successor to translation by `P / 6`; the actual successor
  construction is integrated separately; commit `b18fe62`.
- **2026-11-06, G3d forward dynamics:** define the repaired measurable curvature control,
  prove simplex membership at every time, and obtain both integral equations from actual
  normalized boundary geometry. Global periodic frame-velocity Lipschitz regularity is
  also supplied for the cyclic balanced assembly; commit `a94ac12`. Reverse comparison is
  still open.
- **2026-11-06, G3c contact lift:** construct the contact successor from unique indexed
  critical hexagons, prove its exact one-turn sixfold relation, and derive its positive
  `C¹` regularity from the actual boundary curves; commit `7f6809f`. No contact map is
  assumed as an input.
- **2026-11-06, G3c cyclic clock:** prove the new contact derivatives are globally
  Lipschitz, retain the full balanced pair, and conjugate the actual successor to the
  uniform shift `P / 6`. Derive `G(0)=I`, `G(T)=R`, and `X(T)=R⁻¹X(0)R` with the
  same time parameter used by the integral dynamics.

The cubic switching margin is available for later quantitative control estimates. A new
estimate should be tied to one of G2–G6 before it is added to the progress ledger. In particular,
this margin vanishes at the switching endpoint, so it is not a uniform dwell-time theorem.

## Literature boundary

Hales–Vajjha, *Packings of Smoothed Polygons* (2024), proves Mahler's First conjecture and
leaves octagon selection open. Appendix B.4 explicitly does not provide a uniform edge bound.
The abstract and research-problem section are the relevant source checks:

- <https://arxiv.org/abs/2405.04331>
- <https://arxiv.org/html/2405.04331v1>

The pinned reference repository implements substantial Chapters 2–7 material; its report
lists the later Mahler First machinery outside the completed formalization. Its name must
not be read as evidence that every published smoothed-polygon reduction is already formalized.
