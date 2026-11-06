# Source audit and validation boundary

Date: **2026-11-06**. All checks in this file are source-level unless explicitly stated.

## Current hand-proof research

The working agreement in commit `4ffe766` pauses new Lean infrastructure and permits
exploratory computation with explicit limitations. Existing compilation, typechecking,
and CI prohibitions remain in force. Source constructions and new notation do not count
as mathematical closure of the unrestricted comparison.

- [x] Independently review the near-circle hand estimate: determinant identity, reflected-
  row angular signs, primary winding, and both Cauchy–Schwarz inequalities.
- [x] Check the positive quantity before squaring in the time-dependent bound; it is
  `π/3−C/3>0`, supplied by the explicit low-cost hypothesis.
- [x] Check that the excluded neighborhood applies to arbitrary admissible trajectories,
  and that costs at least `π` are separately handled by the actual octagon competitor.
- [x] Keep the lost directional information, possible short excursions, and lack of a
  uniform switching bound explicit in `docs/NEAR_CIRCLE_BOUND.md`.
- [x] Independently review the fixed-edge integration with absolutely continuous state
  coordinates and an arbitrary measurable control. Check the denominator before division.
- [x] Check the group endpoint contradiction, the exact rotation direction for every
  omitted coordinate, and the positive-integral consequence. No terminal `X` equation,
  cost bound, optimality premise, or finite-word assumption is used.
- [x] Independently review the exact hyperbolic circle variation, including the periodic
  left multiplier and unchanged right cyclic shift, all six positive curvature and star
  margins, winding and simplicity, convexity, and the real area/density calculation.
- [x] Check the complete perturbed balanced geometry before using the area identity;
  no unproved control-admissibility or determinant-clock premise remains in the hand proof.
- [x] Distinguish the recovered known circle-subarc exclusion from new global comparison,
  and retain the shrinking-support and nearby-curvature limitations of its quantitative bounds.
- [x] Independently check all stages of the asymmetric four-piece comparison: tangent
  closure, eight reduced words, forced initial shape and sign, full positive margins,
  exact per-piece cost, logarithmic derivative, convergent integral identity, and strict
  decreasing-weight sign. The octagon equality data match the existing candidate.
- [x] Include independent short shape and cost certificates so the four-piece conclusion
  does not rely on reported numerical or symbolic output. Keep its restricted scope explicit.
- [x] Check the cyclic time rebase on actual integral trajectories, including the wrapped
  `i→i+1` control permutation, both endpoints, and cost invariance.
- [x] Check the strict occurrence-order test, all three- and four-arc cases, the scaled
  margin surface, and the exact full-arc positivity condition before using any word formula.
- [x] Preserve the earlier three-arc symbolic exploration with its domain, versions,
  reproduction command, and limitations. Its residuals are not the hand proof or a
  certificate for longer words; no Lean or CI command is involved.
- [x] Independently check the exact finite relaxed frame endpoint, the positive quadratic
  root, the limiting cost, the rational separation from the octagon, and primary winding.
  State jumps are explicitly outside the actual integral control problem.
- [x] Check the state-only and separable-potential obstructions and the weighted three-
  vertex coupled residuals, with their full domain, endpoint, radius, and unsolved-
  certificate qualifications. These are retained failed routes and exact open conditions.
- [x] Independently review the generic word holonomy theorem: both product orders,
  reconstruction of actual integral trajectories, the centralizer, the forced orientation,
  full-arc monotonic margin tests, and the positive factors in rationalized sign checks.
- [x] Retain both central holonomies with the complete strict linear cone and quadratic
  cost quotient. No invertibility of a shape-elimination system is assumed there.
- [x] Independently enumerate all five-piece words surviving the cyclic ordering test;
  check the four-piece merger and both genuine rebase orbits.
- [x] Independently review the complete asymmetric `01020` comparison: tangent factors,
  positive parameter domain, half-factor order, forced initial state and sign, raw-margin
  table, exact algebraic cost cancellation, and all logarithmic coefficients.
- [x] Check the sharp scalar envelope through strict concavity of `h(√x)`, its equality
  case, the strict domain bound on `d`, the exact rational sign estimate, and the octagon
  limiting value. No sampled inequality or unproved symmetry is used.
- [x] Retain the false global-concavity shortcut with its differentiated convergent
  expansion, and document the exact-algebra archive's domain and limitations.
- [x] Independently review the arbitrary-length local edge exclusion: increasing
  coordinate, both logarithmic derivative signs, exact endpoint constraints and cost,
  rank-two switch derivative, and the three-distinct-roots contradiction.
- [x] Check that the implicit-function curve preserves endpoints exactly, retains
  strict star membership on the entire compact segment, and reconstructs a genuine
  free-time integral trajectory that can be spliced at matching `g,X` endpoints.
- [x] Check the sharper one-sided four-arc obstruction and keep the lack of a total
  switch bound explicit.
- [x] Check the published-input measurable-edge corollary against Hales–Vajjha
  Definition 8.1.1, Proposition 8.1.3, and Theorem 8.1.4. Their free-time endpoint
  data match the local variation. Distinguish edge extremality from the anomalous
  full-system lifts in Remark 8.1.6.
- [x] Independently review the three-to-two shortening obstruction: all shorter words,
  triangular centralizer and positive central sign, unique factor reconstruction,
  tangent-only mismatch, and exact full-arc feasible example.
- [x] Independently review the reverse five-piece tangent parameterization, all
  positive denominators, half-holonomy product order, central exclusion, and the
  independent-factor differentiation used to obtain the active margins.
- [x] Check the complete short square-root factorization of each positive active
  margin without assuming ellipticity; verify both independent adjacent-product
  identities before deriving the normalization identity. The argument is not circular.
- [x] Deduce all switching-state and full-arc strict-star inequalities on the entire
  positive two-parameter domain, then reconstruct the actual endpoint trajectory.
- [x] Check the exact cost telescoping, strict logarithm envelope, AM–GM and
  Cauchy–Schwarz bounds, and the exact comparison `10/11 > π/√12 > δ_oct`.
- [x] Combine both genuine five-piece orbits, the four-piece merger, and the
  earlier four-piece equality theorem to cover every description with at most five
  pieces. Keep arbitrary longer words and global affine rigidity open.
- [x] Preserve both reverse-five numerical diagnostics with their versions, exact
  finite input lists, seed, precision, domain, and limitations. Their outputs are not
  premises of any hand certificate or global coverage claim.
- [x] Independently audit the sharp reverse-five minimum: integral representation,
  strict concavity and increase, Jensen's inequality, positive numerator, denominator
  direction, uniform quotient derivative sign, exact minimum, and the unique golden
  factor tuple with its physical durations and normalized initial state.
- [x] Independently audit the full asymmetric six-piece `010202` comparison: tangent
  and state endpoints, parameter positivity, unique initial shape and sign, all raw
  state rows, exact cost cancellation and logarithmic grouping, strict scalar-domain
  bound, and the previously proved sharp envelope on the entire needed domain.
- [x] Check the actual positive family approaching the octagon, with full-arc star
  positivity and exactly two disappearing durations; no positive member attains equality.
- [x] Check all six-piece cyclic increment patterns without a reflection assumption.
  Distinguish the full cost comparisons for `010202` and `012012` from the infeasible
  `010102` orbit; retain `012102` as the open comparison.
- [x] Preserve and independently audit concurrent commit `421eeb1`: exhaustive tangent
  parametrization, actual half-holonomy and orientation, all prefix margins including
  the two-case strict sign certificate, complete positive feasibility, exact cost,
  and strictly monotone deformation to an actual five-piece boundary. Do not describe
  this varying-initial-state global deformation as a fixed local endpoint replacement.
- [x] Independently audit the complete `012012` comparison: exhaustive coordinates,
  compact parameter interval, exact initial state, all prefix and whole-arc strict-star
  inequalities including the arc-vanishing endpoints, and both positive five-piece
  boundary words. After rebasing, check both frame and state endpoints are fixed and
  the tangent is nonzero in the exact one-dimensional fiber. Apply the reviewed
  constrained Hessian only after proving those facts; use compactness to obtain the
  strict global cost comparison for this family.
- [x] Preserve and independently audit concurrent commit `1b23521`: smooth switch
  dependence, both tail-integral Hessian formulas, cancellation of the derivative of
  each jump coefficient, the rank-one term on the tangent line, the three strict
  diagonal signs, and the exact free-time splice. Keep reverse alternation outside
  the exclusion and do not infer a universal cost lower bound from local descent.
- [ ] Unrestricted octagon comparison and affine rigidity: **open**.

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

## Geometric cyclic contact lift

- [x] Construct the successor from the unique indexed critical hexagon at each polar angle.
- [x] Prove strict angular bounds for one and two successor steps, excluding extra winding.
- [x] Prove three steps advance by exactly `π` and six by exactly `2π`.
- [x] Construct the actual parameter lift through the boundary's increasing angle isomorphism.
- [x] Obtain regularity by a nonzero scalar tangent coordinate and inverse composition;
  the determinant quotient proves positivity and continuity of the derivative.
- [x] Check that all six contact identities, the full-period drift, and the sixth iterate
  are conclusions, rather than added hypotheses.
- [x] Independently review the geometry and pinned inverse-derivative APIs.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Balanced cyclic clock assembly

- [x] Derive global Lipschitz contact derivatives from the periodic frame velocity,
  using the plane's sup norm and explicit coordinate bounds.
- [x] Preserve every balanced-pair clause under the constructed clock, including
  half-open period simplicity and exact boundary coverage.
- [x] Apply clock conjugacy to the constructed actual successor, discharging all inputs.
- [x] Prove global cyclic frame and state identities and both exact endpoint conditions.
- [x] Keep the conjugation direction `R⁻¹ X R` consistent with upstream admissibility.
- [x] Independently review the matrix cancellations, Lipschitz bounds, and full output tuple.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Full forward realization and real cost

- [x] Assemble the measurable control, integral equations, initial frame, and both
  terminal conditions into the exact upstream `IsReinhardtAdmissible` predicate.
- [x] Supply the global one-contact shift required by `eqn_cost`, not just full periodicity.
- [x] Derive positive volume from nonempty interior before removing `ENNReal.ofReal`.
- [x] Prove exact real cost equals normalized area, and transfer the density identity
  back to the original worst disk through the constructed linear normalization.
- [x] Discharge the existence input with the actual worst-disk existence theorem.
- [x] Independently review the endpoint assembly and extended-real conversion.
- [x] Keep global control minimality unasserted until the reverse comparison is supplied.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Low-cost smooth-arc winding

- [x] Construct a continuous logarithmic angle from nonvanishing `C¹` data alone;
  do not assume periodicity or simplicity in that construction.
- [x] Use the reflected first row appropriate to the right equation `g'=gX`.
- [x] Check the completed-square identity and its trace upper bound by exact algebra.
- [x] Integrate the angular-speed bound with the cost normalization factor `3/2`.
- [x] Derive the integer endpoint phase from exponential reconstruction and exclude
  both negative and positive extra turns using strict positivity and cost below `π`.
- [x] Derive the positive first matrix coordinate on the entire closed segment.
- [x] Independently review the quadratic argument and pinned complex-periodicity APIs.
- [x] Keep the global smooth-arc hypotheses visible until an actual admissible extension
  is constructed; this module alone does not prove reverse reconstruction.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Arbitrary integral-trajectory regularity

- [x] Start with the actual `IsStateTrajectory` definition, retaining arbitrary measurable
  simplex controls and making no piecewise-constant or smooth-control restriction.
- [x] Prove joint continuity of the commutator on the compact time-times-simplex product,
  excluding zero denominators before obtaining uniform entrywise bounds.
- [x] Derive state Lipschitz regularity from the integral equations directly.
- [x] Prove frame derivatives within the closed interval, including both endpoints;
  do not differentiate unconstrained exterior values.
- [x] Apply the Lebesgue FTC to derive the a.e. state equation and all six curvature signs.
- [x] Inspect exact pinned FTC, integral norm, within-derivative, and Lipschitz APIs;
  explicitly import the Lebesgue theorem because a transitive private import is insufficient.
- [x] Independently review the compactness argument and the local curvature calculation.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Cost bounds and explicit comparison boundary

- [x] Derive the cost-density bound from determinant one and the positive trace sign;
  integrate it for every integral trajectory, without assuming a minimizer.
- [x] Use geometric minimality to bound an actual worst realization by the existing
  octagon's area below `π`; do not assume control minimality to obtain this bound.
- [x] Supply a concrete high-cost competitor and prove full reverse comparison is
  equivalent to its low-cost restriction.
- [x] Keep both reverse-comparison predicates and the universal low-cost inequality
  as propositions, with explicit premises on every conditional minimizer/equivalence theorem.
- [x] Verify that the sufficient control lower-bound criterion needs only the constructed
  forward realization and therefore has no hidden reverse-comparison premise.
- [x] Independently review the exact upstream candidate tuple and pinned integral APIs.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Reverse geometry from a smooth cyclic frame

- [x] Derive reflected-row full-period winding from the exact rotation and low-cost turn.
- [x] Use determinant one to exclude opposite first-column and reflected-row directions;
  continuity bounds their lifted-angle difference without assuming simplicity.
- [x] Derive exactly one first-column turn from the positive integer winding and upper bound.
- [x] Deduce injectivity from strict angular growth and the exact full turn.
- [x] Construct the disk as the actual radial hull and apply the upstream convexity theorem
  only after supplying simplicity, global derivative Lipschitz bounds, and a.e. curvature.
- [x] Derive central symmetry and all six boundary images from cyclic contact shifts.
- [x] Independently review the winding obstruction, interval-integral periodicity,
  complex phase APIs, and radial-hull assembly.
- [x] Keep the global extension inputs explicit until they are constructed from admissibility.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Actual admissible cyclic extension

- [x] Construct six twisted copies and then a global periodic extension from the actual
  admissible segment, preserving both states at every point of the closed segment.
- [x] Derive matching frame velocities from both endpoint conditions, and use integral
  gluing to obtain classical derivatives at the joins.
- [x] Avoid differentiating the discontinuous periodic-reduction map at seams; translate
  to a positive neighborhood where the integral-glued representation applies.
- [x] Prove finite-piece Lipschitz bounds and promote a two-period bound to a global one.
- [x] Transfer a.e. curvature by countably many measure-preserving translations;
  distinguish arbitrary derivative null sets from the separate countable seam grid.
- [x] Verify exact cost preservation by equality throughout the original interval.
- [x] Independently review all seams, matrix conjugation directions, and the pinned
  translation and totalized-derivative APIs.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Completed geometric/control comparison

- [x] Apply the actual admissible extension to the reverse geometric construction;
  every regularity, star, curvature, cyclic, and winding input is supplied.
- [x] Prove exact area equality at low cost and provide the concrete octagon for high costs.
- [x] Discharge both comparison predicates defined in `ControlBounds.lean`, retaining
  arbitrary measurable controls and the full upstream admissible class.
- [x] Construct a global control minimizer from actual geometric worst-disk existence,
  without assuming control-minimizer or extremal-lift existence.
- [x] Prove all control minimizers have the geometric minimax value and reconstruct
  actual worst disks; check that this argument has no circular existence step.
- [x] Prove the unconditional target equivalence while leaving the control lower bound
  and affine equality classification unasserted.
- [x] Independently review the assembled witness tuples, real area identities,
  minimizing comparisons, and exact original conjecture statement.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Pointwise singular-control algebra

- [x] Retain the star-state, traceless reduced-costate, and trace-perpendicularity
  hypotheses; impose no symmetric polygon or explicit strong-lift restriction.
- [x] Check the exact denominator-weighted vertex and gap identities, with every
  denominator negative on the simplex before division or sign cancellation.
- [x] Prove the three vertex control matrices separate traceless matrices and use
  `traceForm X X = -2` to eliminate the remaining proportional costate.
- [x] Derive maximizing support and proper-edge containment without claiming finite
  switching or identifying an edge tie with full-simplex control independence.
- [x] Independently review the algebra and correct the multiplication-factor direction
  in `nonneg_of_mul_nonneg_right` against the exact pinned mathlib API.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Entire-circle exclusion

- [x] Start from actual integral admissibility, using the constructed cyclic extension
  to supply global frame regularity rather than assuming it of the input trajectory.
- [x] Check that equality to `J` only on the open interval determines both cost and
  lifted-angle increment; the exact integral congruence ignores endpoint values.
- [x] Combine the strict low-cost winding theorem with unit angular speed to exclude
  every entirely circular admissible trajectory of cost below `π`.
- [x] Derive the strict bound for every full minimizer from a concrete admissible
  competitor, with no Pontryagin-lift hypothesis or circular existence argument.
- [x] Independently review the source and keep proper circular subarcs explicitly open.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Singular-interval rigidity

- [x] Retain the actual `IsPontryaginExtremal` input and the nonempty open interval
  on which the reduced costate is assumed to vanish; do not introduce a lift axiom.
- [x] Use the integral costate equation and Lebesgue FTC only almost everywhere, then
  upgrade the first-costate identity by continuity on the open interval.
- [x] Use nontriviality at an actual interior point to obtain a strictly negative
  multiplier before cancelling it in the first-costate differential equation.
- [x] Identify the circle state from the star-component signs, and derive uniform
  control only almost everywhere from the original state equation.
- [x] Review both wrappers against the exact pinned extremal tuple, interval hypotheses,
  and distinction between full control independence and a nonunique maximizing edge.
- [x] Preserve the explicit lift hypothesis on the whole-interval reduced-costate
  exclusion; proper singular subarcs and isolated singular contacts remain open.
- [ ] Check Lean elaboration and kernel dependencies: **not run**.

## Upstream source scan

The lift-interface audit in [docs/PONTRYAGIN_LIFT.md](docs/PONTRYAGIN_LIFT.md) also checks
the exact reduced nontriviality and endpoint conditions. Existing coordinate-change
and explicit polygon-lift theorems are not treated as an arbitrary-minimizer lift.

All **64 upstream Lean files** at the pinned commit were fetched and searched for
`axiom`, `sorry`, `admit`, `native_decide`, and `unsafe`. The raw matches were reviewed:

| Match | Assessment |
| --- | --- |
| Two `sorry` terms in `Challenge.lean` | Intentional upstream challenge declarations; `Challenge` is outside this project's import closure. |
| `sorry` in a `CellDecomposition.lean` module comment | Stale prose describing earlier proof holes; the imported declarations have proof bodies. This comment is not a proof term. |
| `axiom` / `sorry` words in `scripts/Audit.lean` documentation | Explanatory comments; the audit script is outside this project's import closure. |
| New source files | No proof holes, new axioms, `native_decide`, or `unsafe` declarations introduced. |

The project imports implementation modules, not `Challenge` or `Solution`. The source import
graph reaches **58 upstream implementation modules** in `Basic`, `External`, and
`SmoothedPolygons`, then mathlib.
All **26 local Lean modules**, including the umbrella, are in the current root closure.
The local graph has no missing imports or cycles; an independent source scan found no
cross-file uses of private local declarations or local declaration collisions.
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
