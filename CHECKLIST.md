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
| G2 — Normalize an actual minimizer | Construct a balanced circle representation of an actual worst disk, preserving the relevant density and supplying every boundary parametrization hypothesis. | In progress. Affine normalization, the continuous trace, and radial regularity have source proofs; arclength and the final assembly are being integrated. See G2a–G2e below. |
| G3 — Justify the chosen reduction | If using the smoothed-polygon route, prove the needed optimal-control, extremal-lift, and Mahler First bridges for the minimizer from G2. | Open in the pinned formalization. The published mathematical reduction is a source, not an imported theorem for this entire step. |
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
| G2d — Common arclength parameter | Construct a global increasing periodic change of parameter with Euclidean unit speed for curve zero. | Open; the norm on `Fin 2 → ℝ` must not silently replace Euclidean speed. |
| G2e — Balanced assembly | Apply the upstream regularity, Lipschitz, star, and curvature lemmas; transport the period, simplicity, coverage, and initial values through the common change of parameter. | Open, dependent on G2b–G2d. |

## Next bounded mathematical task

Continue **G2d–G2e** to produce the balanced circle representation of an actual worst disk.
The source normalization constructs the map and preserves the correct density, and the
continuous trace is now constructed from unique indexed critical hexagons. The remaining
analytic input is a common global Euclidean arclength reparametrization; radial `C¹`
regularity is now derived from the actual minimizer. The final assembly must still supply
every balanced-pair field explicitly.

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
  angular gauge. The radial curve is `C¹`, nonvanishing, and positively oriented.

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
