# Source audit and validation boundary

Date: **2026-11-06**. All checks in this file are source-level unless explicitly stated.

## Reproducibility

- [x] Pin `SmoothedPolygons` to `8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.
- [x] Pin mathlib to upstream's resolved commit `9d581dfff2e41de989072ea63abf3daf69311520`.
- [x] Match upstream's toolchain: `leanprover/lean4:v4.36.0-rc2`.
- [x] Record the remaining transitive revisions from upstream's `lake-manifest.json`.
- [ ] Resolve dependencies with Lake: **not run**. The lockfile was assembled from the
  upstream resolved records with this project's root and direct dependency entries.

The dependency is private. A future checkout needs access to both repositories. The exact
revisions, rather than a moving `main` branch, are the intended dependency boundary.

## Statement audit

- [x] `octagon` denotes the concrete `smoothedPolygonDisk 1`, rather than a shape with a
  density assigned by definition.
- [x] `octagon_density` uses the existing area and balanced-disk packing theorems.
- [x] The global quantifier ranges over `IsCCSDisk`, including convexity, compactness,
  nonempty interior, and central symmetry.
- [x] The upstream density is the supremal density for congruent-copy packings. The
  lattice/congruent-copy identification is an upstream theorem, not a silent convention.
- [x] A genuine worst disk exists by the upstream theorem used in `exists_worst_disk`;
  the minimizer-only criterion is therefore not vacuous.
- [x] `ReinhardtConjecture`, `AffineRigidity`, and `FullReinhardtConjecture` are open
  proposition definitions. No theorem claims to prove them unconditionally.
- [x] Equality is stated up to invertible linear images after centering.
- [x] No theorem treats the regular `(6k+2)` family as all smoothed polygons.

## New scalar proof

- [x] Use upstream `hmaxF` directly.
- [x] Check the exact logarithmic residual identity independently by hand.
- [x] Check the pinned mathlib statements `Real.le_log_one_add_of_nonneg` and
  `Real.log_le_sub_one_of_pos` by source inspection.
- [x] Track positive denominators `y`, `r`, and `r+y` before clearing them.
- [x] Preserve the whole closed domain `2 ≤ y ≤ r ≤ 4`, including the diagonal and corners.
- [x] Discard the rational boundary correction only under `r ≤ 4`.
- [x] State clearly that a cubic margin vanishing on the diagonal does not bound dwell time.
- [ ] Check Lean elaboration and tactic output: **not run**.

## Switching-function transport

- [x] Use the existing `chi32_eq` identity and prove the scalar variables stay inside
  the certificate triangle; its denominator is positive on the entire allowed segment.
- [x] Preserve `1/√3 < y₀ < 1`, `0 ≤ t ≤ switchTime y₀`, and the normalization
  `IsStrongLift y₀ Λ₁ ΛR (-1)` in the exported theorem.
- [x] Use the upstream uniqueness and reflection theorems to cover both switching functions.
- [x] Bound `exp(s)-1` from below by `s` for `s ≥ 0`, and use `W(2-W) ≤ 1` with
  `1 ≤ W < 2`; all cube comparisons concern nonnegative quantities.
- [x] Keep the result restricted to this family of strong lifts, not arbitrary extremals.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Actual-minimizer normalization

- [x] Start with `IsWorstDisk K`, without assuming a normalized disk or boundary curve.
- [x] Normalize the six contact midpoints, keeping the distinction from hexagon vertices.
- [x] Preserve worst-disk status through the upstream lattice/congruent-density equivalence.
- [x] Allow an arbitrary positive determinant factor, rather than assume area preservation.
- [x] Use the critical-hexagon area formula to obtain the normalized density objective.
- [x] Keep pointwise contact existence distinct from a continuous or smooth curve selection.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Continuous boundary construction

- [x] Select critical hexagons from the actual no-gap theorem `rein_mem_Θ`.
- [x] Use indexed uniqueness to prove continuity and period consistency of that selection.
- [x] Check every midpoint curve, rather than only curve zero, for injectivity and full
  coverage on every half-open interval of length `2π`.
- [x] Obtain the normalized initial values from uniqueness at angle zero.
- [x] Keep differentiability and arclength as explicit remaining obligations.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Supporting covectors

- [x] Obtain normalized support covectors from the actual separation theorem.
- [x] Derive their uniqueness from equality of support lines, rather than assume a
  stronger unique-normal hypothesis.
- [x] Bound every supporting covector in one compact box using an interior ball.
- [x] Pass the contact equality and all support inequalities to cluster points;
  continuity follows from uniqueness, with no smooth-boundary input.
- [x] Prove gauge domination separately for zero and nonzero vectors.
- [x] Independently review the hand proof and inspect the pinned compactness APIs.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Radial regularity

- [x] Squeeze both positive and negative difference quotients using minimum and maximum.
- [x] Differentiate the contact value without differentiating the continuous covectors.
- [x] Use the gauge's strict positivity before inversion.
- [x] Compute the exact radial determinant `1 / gauge(dir)^2` and deduce regularity.
- [x] Obtain support uniqueness from the actual worst-disk theorem, not an added hypothesis.
- [x] Independently review the proof and inspect the calculus APIs at the exact mathlib pin.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Global arclength construction

- [x] Define speed by the square root of the sum of squared tangent coordinates.
- [x] Prove positivity, continuity, and periodicity before integrating.
- [x] Prove both limits of the accumulated-length function and its global surjectivity.
- [x] Construct the inverse as an order isomorphism; prove its derivative and `C¹` regularity.
- [x] Prove the inverse fixes zero and transports the full period by an exact drift identity.
- [x] Verify Euclidean unit speed by the chain rule and positive-denominator cancellation.
- [x] Independently review the argument and exact pinned integral/inverse-function APIs.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Balanced assembly and global target transfer

- [x] Supply every `IsBalancedPair` field from actual-minimizer inputs.
- [x] Use one common arclength map for all six contact curves.
- [x] Set `tf = P / 6` and prove the exact half-open period correspondence.
- [x] Preserve the initial circle values by fixing zero.
- [x] Apply upstream Lemmas 2.4.2, 2.4.3, 2.4.5, and 2.4.6 with all hypotheses supplied.
- [x] Prove area minimality using the density formula for every balanced competitor.
- [x] Prove the converse with the constructed global worst representative, avoiding a
  circular or assumed existence argument.
- [x] Transfer affine rigidity through the inverse normalization in the correct order.
- [x] Independently review the assembly and target equivalences; correct the implicit
  map argument in `rein_image_symm_image` found during source review.
- [x] Keep the unrestricted area bound and equality classification as open propositions.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Matrix frame and determinant clock

- [x] Construct one global contact frame from two adjacent contacts and prove its action
  on all six points, determinant one, regularity, period, and initial identity.
- [x] Derive positive raw determinant and strict star signs from the balanced geometry.
- [x] Construct the inverse integral of `sqrt(det X)` and check the squared determinant
  scaling law for two-dimensional matrices.
- [x] Supply all hypotheses of upstream Proposition 3.1.9 for global state Lipschitz regularity.
- [x] Derive speed covariance by differentiating the actual matrix contact-shift identity.
- [x] Prove the generic clock conjugacy, retaining the successor's existence and sixfold
  relation as explicit inputs until the separate geometric construction is integrated.
- [x] Review matrix/inverse APIs and the hand argument independently.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Forward measurable control and integral equations

- [x] Repair the raw curvature control on its measurable exceptional set; simplex
  membership holds at every time, as the upstream trajectory definition requires.
- [x] Prove measurability of the derivative-based control and nonvanishing of its
  dynamical denominator at every star state.
- [x] Prove curvature directly at each twice-differentiable boundary point; do not
  pull an arbitrary null set through a change of time.
- [x] Derive local Lipschitz frame velocity, and the global bound when the frame is periodic.
- [x] Use the absolutely-continuous FTC for the almost-everywhere state equation,
  with endpoints removed as null sets and without a countability assumption.
- [x] Supply the determinant-clock and balanced-boundary hypotheses from constructions.
- [x] Independently review the integral APIs at the pinned mathlib revision.
- [x] Keep terminal conditions, area cost, and comparison against all admissible controls
  distinct from the state-trajectory conclusion.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Upstream source scan

All **64 upstream Lean files** at the pinned commit were fetched and searched for
`axiom`, `sorry`, `admit`, `native_decide`, and `unsafe`. The raw matches were reviewed:

| Match | Assessment |
| --- | --- |
| Two `sorry` terms in `Challenge.lean` | Intentional upstream challenge declarations; `Challenge` is outside this project's import closure. |
| `sorry` in a `CellDecomposition.lean` module comment | Stale prose describing earlier proof holes; the imported declarations have proof bodies. This comment is not a proof term. |
| `axiom` / `sorry` words in `scripts/Audit.lean` documentation | Explanatory comments; the audit script is outside this project's import closure. |
| New source files | No proof holes, new axioms, `native_decide`, or `unsafe` declarations introduced. |

The project imports implementation modules, not `Challenge` or `Solution`. The source import
graph reaches **56 upstream implementation modules** in `Basic`, `External`, and
`SmoothedPolygons`, then mathlib.
The name `External` does not by itself denote an assumed theorem: the fetched files contain
proof implementations. This scan is evidence about source text, not a kernel axiom audit or
an independent mathematical review of every upstream proof.

## Deferred mechanical validation

- [ ] Lean compilation and typechecking.
- [ ] Kernel dependency inspection for the new results and the imported candidate facts.
- [ ] Independent-kernel verification, if requested for the final proof.
- [ ] Mathematical audit of the entire upstream packing and normalization development.

None of these deferred checks was run. No workflow or CI configuration was added or changed.
Any reported upstream build status belongs to upstream and is not validation of this PR.

Additional static checks: the TOML configuration and JSON lock agree on both direct pins;
all local Markdown links resolve; the source diff has no whitespace errors. These checks
do not execute the Lean code.
