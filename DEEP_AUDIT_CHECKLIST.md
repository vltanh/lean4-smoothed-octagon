# Audit boundary for the global-reduction checkpoint

Date: 2026-11-07. New work is hand research and explicitly scoped exploration.
No new Lean file was added; no compilation, Lake, typechecking, kernel audit,
or CI was run. The coverage proof received an independent hand review of its
sign catalogue, twisted seam, run alternatives, and one-period window condition,
in addition to the distinct finite-graph computational cross-check. The analytic
local exclusions have not been proved. The original at-most-six L3 statement
and its arbitrary-measurable relaxation have been refuted by independently
reviewed hand counterexamples, with ASZ as an explicit input to the strengthening.

The complete earlier audit is preserved at
[798a7e1 / DEEP_AUDIT_CHECKLIST.md](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/DEEP_AUDIT_CHECKLIST.md).
Its historical source scans and review claims are not new validation performed
in this checkpoint. All existing mathematical and Lean proof files are retained.

## Audited all-short mixed equations and geometric winding

- [x] Independently multiply the all-short three-factor bridge, retain
  its full central sign, and combine the two-node antiperiodic incidences
  correctly; see [MIXED_GLOBAL_SHORT_RUN_PERIOD_AUDIT](docs/MIXED_GLOBAL_SHORT_RUN_PERIOD_AUDIT.md).
- [x] Derive the Euler cost identity with the same actual normal covector
  and the free-initial-state boundary cancellation. Common scaling is
  differentiated before the frame constraint, not asserted to preserve it.
- [x] Check the strict two-centre cost bound, arbitrary unequal factors,
  positive-duration boundary, and all eight exact symbolic identities.
- [x] Independently audit the state contraction, fixed-endpoint frame
  homotopy, canonical lifted product, all four switch-vector angle
  branches, and double-reverse gauges; see
  [MIXED_GLOBAL_PROJECTIVE_WINDING_AUDIT](docs/MIXED_GLOBAL_PROJECTIVE_WINDING_AUDIT.md).
- [x] Keep exactly two Jacobi kernel vectors along the regular-polygon
  deformation and count the ordinary inertia, including the two-node case.
- [ ] Prove a uniform constrained cost-index or comparison theorem for
  the remaining all-short `m>=5` domain and the other open F/M2 cases.
  The winding and scalar inertia alone do not prove this step.

These are independent internal hand audits, not external peer review
or Lean kernel validation. The two-centre comparison closes one fixed
base branch of a uniform family, not the entire sufficient M1 case.

## New case-atlas computation boundary

[FINITE_CASE_COMPUTER_ROADMAP](docs/FINITE_CASE_COMPUTER_ROADMAP.md)
and [CASE_ATLAS_EXPERIMENT_001](docs/CASE_ATLAS_EXPERIMENT_001.md)
are a proposed *research route*, not verified new G4 cost comparisons.

- [x] Reproduce the exact algebraic factor/state/tangent endpoint formulas
  numerically on all five fixed windows. Use complex-step for a
  5-by-6 endpoint differential; do not infer PMP signs when the
  normal stationarity residual is nonzero.
- [x] Screen the two known exact stationary L1 and M1 examples:
  computed exterior missing-control gaps are positive, so these
  source examples fail the selected-complete-switch condition.
  The rigorous conclusion is inherited from existing hand notes.
- [x] Screen standard forward N=7:
  two exterior switching ties, positive interior test gaps,
  exact-family closed endpoints, but whole-period cost above A_oct.
- [x] Probe four positive all-reverse octagon insertions with five
  numerically corrected endpoint coordinates; recorded costs increase.
  Floating-point root residuals do NOT prove exact closure or uniform
  cost positivity.
- [x] Compute curvature-corrected constrained Hessians on complete
  twisted periods with **initial state free**, obtaining numerical
  negative indices 0,2,4 at standard N=4,7,10, consistent with the
  separately existing exact hand theorem. Check stability under
  three finite-difference step sizes. This is not a new asymmetric
  index theorem or interval-certified inertia count.
- [ ] Implement and independently audit an event-driven numerical
  complete-period PMP continuation with all normal/tie exceptions.
- [ ] Prove one **uniform** G4 case exclusion on its complete stated
  domain, including rank defects, triple/cubic switches and boundary.
- [x] Independently audit GLOBAL_NORMALITY's abnormal exclusion, including
  the actual endpoint/covector interface, backwards zero-tie identities,
  positive-arc triple-tie obstruction and twisted seam. See
  [GLOBAL_NORMALITY_AUDIT](docs/GLOBAL_NORMALITY_AUDIT.md). Restore the
  previously missing checker; all 22 exact algebra checks pass.
- [x] Deduce a qualitative positive lower bound on -lambda over the compact
  unit-normalized minimizer lifts and compactness after lambda=-1.
  No explicit numerical bound or normal-tie exclusion follows.
- [x] Independently audit [NORMAL_TIE_BRANCHING](docs/NORMAL_TIE_BRANCHING.md):
  reconstruct all three Hamiltonians, both gap signs and the universal
  second-gap derivative; check zero-energy clock transport and derivatives
  through order three. [The review](docs/NORMAL_TIE_BRANCHING_AUDIT.md)
  covers triple ties, quadratic contacts and cubic switches, retaining
  every passing vertex. No uniform right interval or global fate follows.

Python/NumPy/SciPy version, commands, finite inputs, solver settings,
numerical failures/limitations and output tables are in the experiment
note. No independent review of the new exploratory scripts beyond
self-checks is claimed. None of the five case-C analytic certificates
was proved by those numerical diagnostics. The direct hand proof below
now closes pure-reverse R; the other four cases and the global octagon
comparison remain OPEN.

## Closed global reverse case: independent proof checks

[GLOBAL_REVERSE_PERIOD_EXCLUSION](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
and its [independent audit](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION_AUDIT.md)
close the entire pure-reverse global case R.

- [x] Convert the third-active-margin minimum exactly to the three
  non-strict inequalities in A, B, Z, b and c; retain equal minima.
- [x] Reconstruct the two positive missing-control needles, four original
  factor corrections, zero tangent-frame derivative and state-stabilizer
  derivative; all actual state/frame endpoint derivatives vanish.
- [x] Independently differentiate the complete margin and cost updates
  and obtain the same exact cost numerator.
- [x] Prove its uniform strict negative sign using the two elementary
  logarithm bounds, including the rational Padé remainder derivative.
- [x] Check positive physical needle clocks, the same actual cotangent,
  formal outer-factor stripping, and the zero active Hamiltonians.
  Use a necessary-PMP contradiction only; no rank or IFT is assumed.
- [x] Place the minimum in the twisted periodic active-margin sequence,
  with valid cotangent continuation across every seam.
- [x] Apply global normality to minimizing lifts, retaining all costate
  sectors and arbitrary unequal factors. No total-cost bound is needed.
- [x] Run all 20 exact symbolic identities and independently reconstruct
  endpoint/cost algebra in a separate calculation. No floating-point
  search, growing word catalogue, Lean, Lake or CI was used.

The later mixed-run proof also closes M3; F, M1 and M2 remain open.
The historical universal local-shortening
package is not closed by this global minimum principle.

## Closed mixed case M3: independent proof checks

[MIXED_GLOBAL_MINIMUM_STRUCTURE](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
and its [independent audit](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE_AUDIT.md)
close the entire long-reverse-run mixed case M3.

- [x] Check the reflected state, primary and reduced costates, physical multiplier, Hamiltonian gaps, and actual twisted endpoints.
- [x] Transfer the reverse-four minimum theorem to both interior positions using that actual PMP symmetry.
- [x] Derive the common edge coefficient mu from the same full-system normal covector, without obtaining a new auxiliary edge multiplier.
- [x] Retain weak switch derivatives, triple ties, and cubic contacts in the three-arc argument.
- [x] Prove strict alternating-margin log-concavity, including the equality case by a positive integrating-factor integral.
- [x] Exclude both endpoints of a minimum on a finite reverse run; exclude every interior position for length at least three.
- [x] Continue the same lift across the actual twist; no comparison path longer than a period is used.
- [x] Keep the surviving two-switch runs and the local 01020 counterexample; do not count M1 or M2 as closed.

The proof is by displayed hand identities and inequalities; its reverse-four
input has the separate exact checker. F, M1 and M2 remain open.

## Whole-period normal structure audit

[GLOBAL_NORMAL_PERIOD_STRUCTURE_AUDIT](docs/GLOBAL_NORMAL_PERIOD_STRUCTURE_AUDIT.md)
independently reviews mixed ellipticity, switch rigidity, and the
competitive forward pairing lemma.

- [x] Derive all four mixed state factors and frame columns, the signed cyclic action and the actual primary multiplier.
- [x] Prove strict turn secant bounds and check both physical switching bracket signs with normalization.
- [x] Use double-reverse-run minima for positive switch Gram values and opposite cross-pairing signs.
- [x] Obtain the projective contradiction from full central monodromy; do not assume spatial ray coverage from labels.
- [x] Compare hypothetical vertex germs using one initial covector and the same constant mu; retain phases where no candidate passes.
- [x] Check both sides of a zero-derivative switch, the unique cubic reverse alternative, and its incompatibility with strict closed-period reverse minima.
- [x] Check the forward determinant triangle, its degenerate boundary, concavity, exact minimum vertex and strict scalar factorization.
- [x] Run the 32 mixed and nine acute exact identities; retain the unresolved endpoint-curvature and radial/margin index.

F/M1/M2 remain open. No uniform switching derivative, dwell time, or
strict third-control gap follows from these results.

## Whole-forward ellipticity audit

[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](docs/GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
and its [independent audit](docs/GLOBAL_STRUCTURE_FORWARD_ELLIPTIC_AUDIT.md)
prove negative ellipticity throughout the normal pure-forward domain.

- [x] Use the actual primary multiplier and cancellation of free initial-state terms.
- [x] Include the positive physical clock and cost-normalization factors.
- [x] Derive the weak switching inequality without excluding triple or zero-derivative ties.
- [x] Use exact stationarity for the off-diagonal Gram bound; sign-only pairing is insufficient.
- [x] Derive two independent Jacobi solutions from full central frame monodromy.
- [x] Treat rank-one and indefinite forms, both periodic boundary signs, and the exact positive-kernel identity.
- [x] Retain endpoint curvature in the remaining Hessian and justify rank for N>=7 using the proved local six-forward rank theorem.
- [x] Run all ten exact local identities; do not interpret them as a uniform index calculation.

F remains open. The Jacobi inverse in the full Hessian is indefinite.

## Uniform symmetric mixed-core review

[MIXED_GLOBAL_SYMMETRIC_ESCAPE](docs/MIXED_GLOBAL_SYMMETRIC_ESCAPE.md)
received an [independent internal hand audit](docs/MIXED_GLOBAL_SYMMETRIC_AUDIT.md).

- [x] Check the full strict-star core range `1<h<2, 0<v<3`, all four
  equal factors, continuous stationary cotangent, and both outer ties.
- [x] Identify the actual normalized lift by the existing rank-five
  theorem, without imposing arbitrary state or frame endpoint equations
  on the six-piece window.
- [x] Verify the shear/cyclic cotangent transformation, physical factor
  `-3/2`, and negative elliptic orientation in the rejected Casimir region.
- [x] Retain equality in the outgoing switching derivative; use the
  actual factor-h pad to reach the last critical point with a strict gap.
- [x] Verify every rational logarithm envelope and polynomial threshold,
  the 18 positive Bernstein coefficients, concavity, and the exact
  determinant separation `891/400-(313/210)^2=211/35280`.
- [x] Prove both missing-control gaps stay strict until finite star exit,
  and use the full twisted state/costate extension for the contradiction.
- [x] Run the supplementary checker: all 146 exact identities and rational
  sign checks passed with Python 3.12.14 / SymPy 1.14.0.
- [ ] Extend the theorem to arbitrary asymmetric cores and shorter
  outgoing pads. This scoped family theorem leaves universal M1 open.

## Exact limitations on the next global extensions

[MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION](docs/MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md)
received an [independent internal audit](docs/GLOBAL_STRUCTURE_MIXED_SHORT_PAD_AUDIT.md).

- [x] Reconstruct the fixed asymmetric core, one continuous normal
  cotangent, all three inner edge ties and both adjoining control-0 ties.
- [x] Prove all whole-core third-control gaps using exact curvature and
  endpoint slope signs; construct a positive incoming 0 germ by the
  actual physical Hamiltonian switching derivative.
- [x] Verify the outgoing third gap stays strict and the other numerator
  has its unique first positive zero in `(251/250,201/200)`, while x<0.
- [x] Check the physical negative-elliptic determinant is below the actual
  competitive cap, with a local cost below A_oct. All 71 exact identities
  and rational sign checks pass with Python 3.12.14 / SymPy 1.14.0.
- [x] Keep the first external switch, geometric sector/embedding, full
  twisted return and minimality unproved. The counterexample refutes only
  the stated local inference, not the revised complete-switch M1 target.

[REVERSE_PERIOD_CASIMIR_REDUCTION](docs/REVERSE_PERIOD_CASIMIR_REDUCTION.md)
received an independent internal recheck of the trace signs, admissible
local triple, regular stationary multiplier, rank-three Fourier modes,
and strict logarithmic Casimir comparison. The individual trace bound is
an **upper** bound. The regular lower bound is only an already excluded
family check; no arbitrary reverse-period conclusion follows.

The sign-compatible parabolic/hyperbolic matrices in the cyclic-sector
note separately show why column orientation and derivative signs alone
cannot remove the remaining sectors. They are not claimed stationary
multipliers or actual PMP examples.

## Active global proof checks

The active entry point is [GLOBAL_REDUCTION_PLAN](docs/GLOBAL_REDUCTION_PLAN.md).
The original five-template sufficient domain remains refuted.

The current numerical reduction bypasses external Theorem 16.3.1.
The [finite bang-bang source audit](docs/FINITE_BANG_BANG_SOURCE_AUDIT.md)
still records numerical unstable-curve and basin-containment steps not
independently certified here. The earlier qualitative route used that
input; the new all-component clearance and E4 count do not. The named
geometric correspondence, compact-state, and standard PMP remain explicit
dependencies. The direct measurable-edge proof below removes the separate
Chapter 8 finite-edge theorem from the active dependency chain.

- [x] Derive twisted state-covector closure from the actual free-initial-state
  endpoint graph, and distinguish it from automatic frame-covector closure.
- [x] Prove full endpoint rank forces normality and a unique normalized lift;
  continue that same lift through arbitrary period seams.
- [x] Prove the finite escape criterion by exact vertex equations and
  `log(5)>8/5`, including every interior time before the strict-star exit.
- [x] Verify the rotated small L3 family meets the criterion throughout the
  explicit core range; the derivative sign has an exact finite-parameter proof.
- [x] Keep arbitrary-subwindow escape exclusion separate from the concurrent
  six-complete-piece endpoint filter and from fixed-endpoint optimality.
- [x] Normalize all genuine cotangent coordinates together with the cost
  multiplier; retain abnormal limits and uniform nontriviality bounds.
- [x] Prove compactness with exact affine controls, weak-star convergence,
  continuous cost, and the actual common globally minimizing cost.
- [x] Check the primary singular-arc lemma excludes an endpoint of a positive
  vertex arc on either side; combine with the finite bang-bang minimizer theorem.
- [x] Deduce uniform qualitative singular clearance for actual minimizers
  using external Theorem 16.3.1, without asserting it for all competitive
  PMP trajectories or independently validating the cited numerical steps.
- [x] Replace the role of the audited finite bang-bang input in the active
  reduction: GLOBAL_COST_CASIMIR and GLOBAL_NUMERICAL_REDUCTION prove
  clearance directly and construct finiteness with E4. The source
  unstable-curve and basin calculations themselves remain uncertified here.
- [x] Prove transport of the reduced costate to a fixed plane and uniform
  first/second derivative estimates without differentiating measurable controls.
- [x] Choose closed angular sectors with robust exclusions and generic guard
  lines; at most one or two zeros of each projection bound the edge intervals.
- [x] Use the minimizer edge bound explicitly; do not assert it for arbitrary
  full-system PMP lifts. Finite cover then gives a common finite piece bound.
- [x] Make the regular-domain count effective in a specified projective norm:
  verify the explicit common denominator, augmented-covector Gronwall bounds,
  both algebraic coercivity estimates, three comparison lines, four
  possible small rotations, explicit margins,
  the exhaustive three-case split, and every interval-length error budget.
  Three independent internal hand reviews passed. No numerical clearance
  was inferred from compactness or from changing norms. The factor-28
  refinement was separately reviewed, and its changed derivative margin
  is propagated through the time constants rather than reusing the old mesh.
- [x] Supply a numerical singular clearance and specific integer:
  D>10^-11 for every normalized competitive closed lift in the common
  state domain, and N<10^56 for every global minimizer. The earlier
  independent D>10^-1906 and N<10^5741 proof is preserved. This is
  an explicit ceiling, not a practical or evaluated case catalogue.
- [ ] Complete the remaining global comparison and affine equality theorem.
- [ ] Run kernel validation (deferred under the user's current workflow).

The separate GLOBAL_FORWARD_INDEX method check was independently reviewed:

- [x] Resolve twisted state closure with cyclic active margins and impose
  the full frame matrix equation, rather than just its trace.
- [x] Prove rank three and the exact Fourier tangent kernel; compute the
  uniquely determined endpoint multiplier and the endpoint curvature term.
- [x] Derive the finite commutator sum, diagonalize on the constrained
  tangent space, and prove the strict logarithm sign by hand.
- [x] Integrate the 2(k-1) negative directions to actual closed feasible
  curves with varying initial state, using the rank-three implicit function
  theorem and the finite-piece geometric bridge.
- [x] State that the standard family is already cost-excluded and that no
  asymmetric-word index theorem or new competitor class follows.

The separate [pure cyclic sector theorem](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md)
received an [independent internal audit](docs/GLOBAL_STRUCTURE_CYCLIC_COSTATE_AUDIT.md):

- [x] Derive the reverse signed action from its actual vertex update,
  without assuming a reversed control is admissible.
- [x] Check strict positive partial derivatives on the positive orthant
  by the three-term elementary logarithm decomposition.
- [x] Check both frame-column formulas, determinant signs and central
  seam, including arbitrary unequal positive factors.
- [x] Derive the actual endpoint multiplier pairing, initial-state
  cancellation and orientation change, without a rank assumption.
- [x] Include zero and the parabolic cone boundary in the exclusion.
- [ ] Eliminate the hyperbolic/negative-parabolic sectors or prove the
  remaining sharp cost/index statement in the negative elliptic sector.

The new hand proofs received separate internal mathematical reviews. Such
review is not external peer review or Lean kernel validation. No new Lean
file, build, typechecking, Lake command, or CI was introduced or executed.

## Direct period budget and measurable-edge review

[SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md) and
[MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md) have been
read in full and checked by the root and independent internal reviewers.

- [x] Verify strict positivity and normalization of the equilibrium control,
  including its barycentric weights in the control-affine formulation.
- [x] Derive the positive-elliptic conjugation identity, both polar angular
  velocities, the lifted endpoint angle, and the integrated cost inequality.
- [x] Rebase the same twisted lift at every time, preserving the period cost
  and the body covector; retain abnormal multipliers without dividing by them.
- [x] Check cyclic invariance and rotated height bounds, the Hamiltonian
  width estimate, `norm(W)<=607500*norm(A)`, and both algebraic projective
  norm bounds. Reuse the proved rational octagon and circle estimates.
- [x] Derive `D>10^-11`, verify that the count uses only certified `m,M`
  bounds, and recompute every time coefficient and ceiling for `N<10^56`.
- [x] Reconstruct every nearby measurable edge competitor in physical time
  with both frame and state endpoints fixed. Check strict-star margins,
  positivity, the bi-Lipschitz change of variable, and the free-time splice.
- [x] Apply a separate fixed-time PMP to that edge problem. Do not impose
  zero Hamiltonian or restrict an arbitrary full-system abnormal lift.
- [x] Treat the nonzero quadratic, identically zero polynomial, and abnormal
  cases; prove the finite zero count before claiming a vertex representation.
- [x] Preserve the independent concurrent cost--Casimir proof and explicitly
  remove source Theorems 8.1.4 and 16.3.1 from this active proof chain.

These are internal hand reviews, not external peer review or kernel
validation. The final cost comparison and affine equality theorem are open.

## General insertion obstruction and revised comparison boundary

[VERTEX_INSERTION_OBSTRUCTION](docs/VERTEX_INSERTION_OBSTRUCTION.md)
received independent full internal hand reviews.

- [x] Apply the parameterized implicit function theorem to the actual five
  closed endpoint residuals, using only an invertible old-parameter minor.
- [x] Check the smooth extension at zero inserted durations, positive
  inserted factors, persistence of old positive factors and strict star,
  and continuity of the full physical cost.
- [x] Prove full rank five at the octagon: the six-margin coordinate change
  is invertible, the two state residuals have rank two, and the frame
  residual restricted to their kernel has rank three.
- [x] Check the reverse refinement at every transition, including the
  twisted seam. Do not replace the frame matrix equation by its trace.
- [x] Refute only the unconditional C>=pi and uniform-positive-gap targets.
  No PMP lift, cheaper-than-octagon cost, or new excluded minimizer class
  follows. A strict comparison at every positive point may still hold.

## Numerical small-multiplier count

[GLOBAL_SMALL_MULTIPLIER_BOUND](docs/GLOBAL_SMALL_MULTIPLIER_BOUND.md)
supplies a numerical bound without the external finite bang-bang input.

- [x] Use the actual product norm and the exact constant sqrt(11/2) to
  give D>=m/2 for abs(lambda)<=m/sqrt(22); include abnormal lifts.
- [x] Check every state, Gronwall, derivative, and time coefficient by
  elementary inequalities; prove c>10^-27*m^2 and m>10^-1903.
- [x] Apply the three-line theorem and the integer ceiling to obtain
  N<10^5740, without assuming a pre-existing finite representation.
- [x] Keep E4 explicit and require only one favorable normalized lift.
- [x] Normalize the complementary sector to lambda=-1 only after the
  explicit lower bound on abs(lambda); prove the entire covector bound
  and conversion for any future normal-sector clearance.
- [x] Establish singular clearance for the complementary normal sector in
  GLOBAL_COST_CASIMIR and GLOBAL_NUMERICAL_REDUCTION; cover every orbit type.

Separate internal hand reviews checked the assembled argument. This is
an explicit sector estimate; the separate all-component numerical reduction
now completes the count for every minimizer.

## Conserved-determinant clearance

[GLOBAL_CASIMIR_CLEARANCE](docs/GLOBAL_CASIMIR_CLEARANCE.md) gives a
second direct clearance test independent of the finite bang-bang input.

- [x] Prove conservation from the commutator adjoint equation and absolute
  continuity, including every control switch.
- [x] Expand the determinant around (3/2)*lambda*J in the actual norm;
  prove the uniform estimate for arbitrary sign and orbit type.
- [x] Deduce D>delta/3 from abs(Delta)>=delta, including equality at the
  input threshold, and prove D>1/13 when abs(lambda)>=1/2.
- [x] Apply the general coefficient bounds from the small-multiplier note
  without importing its sector assumption; check every ceiling and power.
- [x] Preserve E4 and the scoped hypotheses of this determinant lemma.
  A tube in the source's exact critical Casimir slice would not certify
  a transverse neighborhood; the new whole-period proof bypasses it.
- [x] Prove the competitive negative elliptic determinant gap from actual
  frame closure and the cost budget; treat the other orbit components
  separately. GLOBAL_NUMERICAL_REDUCTION resolves the formerly missing band.

## Complete-period cost–Casimir inequality and universal numerical bound

The assembled notes [GLOBAL_COST_CASIMIR](docs/GLOBAL_COST_CASIMIR.md)
and [GLOBAL_NUMERICAL_REDUCTION](docs/GLOBAL_NUMERICAL_REDUCTION.md)
received separate internal hand reviews of their complete arguments.

- [x] Check the original physical-time Hamiltonian signs against the pinned
  upstream definitions; construct all three strictly positive coefficients
  of the stationary comparison control and use the full simplex maximum.
- [x] Prove spatial costate conservation and the explicit negative elliptic
  conjugacy; distinguish body and spatial angular quantities.
- [x] Expand the nonvanishing complex polar coordinate and its derivative
  exactly. Use the actual matrix endpoint to bound its continuous angle
  increment; no assumed primary winding or finite-switch representation.
- [x] Derive C>=4*pi*kappa/(2*kappa+3), the homogeneous cost-multiplier
  version, and the strictly separated determinant under C<=A_oct<pi.
- [x] Prove A_oct<313/100 and pi>157/50 with rational square, logarithm,
  and arctangent inequalities, including the angle branch in Machin's identity.
- [x] Exhaust negative elliptic, nonpositive-determinant, and positive
  elliptic normal costates. Prove the common cost-normalized ||A||>1/120
  without falsely imposing initial unit norm after cost normalization.
- [x] Convert homogeneously to the initial product norm, include the entire
  small-multiplier sector and abnormal lifts, and prove D>10^-1906 for
  every competitive complete-period lift in the stated state domain.
- [x] Reuse the general coefficient estimates c>10^-27*m^2 and m>10^-1903
  without importing a small-multiplier-only hypothesis; check the short
  interval scale and integer ceilings giving N<10^5741.
- [x] Reopen E4's Chapter 8 edge dependency and verify it does not use
  Theorem 16.3.1. Keep E4 essential to counting, and distinguish clearance
  for competitive PMP lifts from the count for actual minimizing controls.
- [x] Derive the exact three-term cost defect and classify equality in this
  bound alone: n=0, orthogonal B, X=J, T=pi/3, kappa=3/2, W=0, and
  centroid control almost everywhere. Retain traceless W and the actual
  state equation; verify the converse and homogeneous rescaling.
- [x] Check the exact subcritical two-direction switch phases and their
  side-independent Hamiltonian-gap derivative. Construct genuine short PMP
  segments using strict third-control separation and transversality.
- [x] Check the exact subcritical cubic reverse switch by pulling back the
  full cotangent vector to the invariant edge coordinates, preserving the
  positive physical clock, and computing the cubic leading coefficient.
  Retain nontransverse switches in any proposed general index theorem.
  Keep this restriction of a zero physical Hamiltonian distinct from the
  separate fixed-time PMP used for E4, which imposes no zero-Hamiltonian
  condition in its independent-variable formulation.
- [x] Keep all three sharpness/diagnostic results separate from octagon
  equality, a full-period counterexample, or a new global cost exclusion.
- [ ] Complete the uniform global cost comparison and affine equality case.
  Neither the enormous integer nor the normal determinant gap supplies it.
- [ ] Formalize and run kernel validation after mathematical closure, under
  the agreed later workflow. No Lean, Lake, typechecking, or CI was run.

## Regular forward-window descent

[LOCAL_FORWARD_REGULAR_DESCENT](docs/LOCAL_FORWARD_REGULAR_DESCENT.md)
proves a local theorem on the full stated interval 1<q<=5/4.

- [x] Derive the fixed-initial-state active-margin tangent and unique frame
  endpoint multiplier; include the full endpoint curvature in the Hessian.
- [x] Prove its scalar value is negative by exact polynomial expansion and
  the elementary logarithm bound, without sampled Hessian evidence.
- [x] Integrate the tangent to an actual endpoint fiber and preserve positive
  factors and strict star for each reference.
- [x] Prove improvement persists for nearby unequal-factor inputs, including
  nonstationary ones, while each input retains its own initial/end states.
- [x] Include all known standard complete-switch forward windows by the exact
  bound 2*cos(2*pi/7)<5/4. Keep global closure and PMP hypotheses separate
  from the broader continuous-q local theorem.
- [x] Retain the unresolved full L1 domain and lack of uniform neighborhood
  size at q=1. This does not add a newly excluded global standard family.

Independent internal hand reviews checked the complete derivation and its
scalar and implicit-function steps. No Lean, Lake, typecheck, CI, or new
exploratory computation was used for this result.

## Historical coverage checks

- [x] Use the actual twisted seam: the wrapped label increases by one, rather
  than silently imposing an untwisted periodic label word.
- [x] Choose a cyclically reduced description beginning at a genuine switch.
- [x] Restrict six-arc windows to one fundamental period when N>=6; do not
  apply a window theorem to six arcs spanning several octagon periods.
- [x] Convert the established forward alternating exclusion to exactly `+-+`.
- [x] Prove negative runs have length at least two in a mixed minimizing sign
  sequence, and exhaust positive-run length one versus length at least two.
- [x] Obtain exactly five fixed templates by a hand run argument; no tested
  maximum total word length is used.
- [x] Cross-check with the standard-library graph script: 32 sign blocks,
  21 surviving the old exclusion, 5 target edges removed, 12 vertices and
  16 remaining edges in a directed acyclic graph.
- [x] Independent mathematical review of the coverage argument in Sections 1-2.
- [ ] Complete independent mathematical review of every domain and analytic
  assertion in the new note; the coverage review alone does not establish this.

## Endpoint and domain checks

- [x] P0 hand audit: use the final finite bang-bang theorem, prove sectors after
  left normalization by transforming the entire disk, and justify a finite
  cheaper splice as a geometric competitor without an extra winding premise.
  See `docs/MINIMIZER_WINDOW_AUDIT.md`. This is not a re-audit of every retained
  through-five identity or a proof of an analytic local improvement.
- [x] Keep two initial-state coordinates and six factors explicit.
- [x] Independently review the P0 premises and equality-transfer scope.
  Record the book's terminal-conjugation misprint, the relabeling conjugation,
  exact equality state/times, and the linear map carrying each original worst
  disk to the concrete octagon. The future uniform bound is still a premise.
- [x] Require strict positivity at every state endpoint, using monotonicity
  of exact vertex flows to cover the entire continuous arcs.
- [x] Keep normalized cost C/sqrt(12) distinct from area/cost C.
- [x] Retain geometric one-sector eligibility for windows in an actual
  nonrepeating balanced boundary; state-only feasibility is not silently
  substituted for that condition.
- [x] Reduce the sector tests to quadratic inequalities using the exact
  Laurent-linear partial-frame formula.
- [x] Preserve BOTH tangent product and terminal state with initial state
  fixed. Derive preservation of the actual terminal frame from these data.
- [x] Do not impose the global equation F=R on an arbitrary local window.
- [x] Supply explicit inverse formulas for the two orientations of a positive
  three-distinct-label tangent block; check their denominators on their image.
- [x] Retain rank-zero, rank-one, and degenerate stationary points as analytic
  obligations rather than count dimensions as a descent theorem.
- [x] State that a replacement need not remove an arc: strict cost decrease
  with preserved endpoints suffices for contradiction to global minimality.
- [x] Refute the original at-most-six L3 target on its full stated domain
  by producing eligible counterexamples. This is not a proved exclusion.
- [x] Define the complete-switch PMP domains in SWITCH_COMPLETE_REDUCTION
  and prove actual-window membership plus the conditional finite-splice
  implication, retaining abnormal alternatives where rank is unresolved.
- [x] Independently review the revised physical fields, cost convention,
  single cotangent lift, neighbor labels, twist, and competitor scope.
- [ ] Prove all five revised analytic improvement targets or another
  unconditional bound of five. The separate global route now gives a
  uniform finite integer existentially, without identifying it.
- [ ] Certify singular boundary faces of the bounded-coordinate compactification.
- [ ] Deduce the unconditional bound N<=5.
- [ ] Prove unrestricted global minimality and affine rigidity.

## Necessary external-switch conditions

`docs/MINIMIZER_WINDOW_PMP.md` proves a necessary condition for selected
windows consisting of six complete pieces. `docs/LOCAL_FORWARD_ENDPOINT_FILTER.md`
gives its explicit L1 active-margin form and its classification limitation.

- [x] Derive both external ties from continuous free-time Hamiltonians,
  including actual costate transversality at the twisted seam.
- [x] Keep the initial state fixed in prepend-needle differentiation and
  account for propagation through the entire old suffix.
- [x] Use endpoint rank on the actual five-dimensional manifold to exclude
  abnormal multipliers and prove uniqueness of the normalized adjoint.
- [x] Preserve zero ties under positive vertex-dependent clock factors;
  do not transfer an equality of nonzero Hamiltonian values that way.
- [x] Exclude the exact L1 input and an open neighborhood from selected
  complete minimizer windows using strict external gaps.
- [x] Exclude the sufficiently small padded L3 family using fixed-input
  rank and external cuts lying inside longer strict control-0 continuations.
  This argument needs neither ASZ nor the all-word optimality theorem.
- [x] Derive all four L1 boundary gaps and retain all four neighboring-label
  branches and possible triple ties.
- [x] Prove asymmetric local-PMP persistence by strict switch continuation
  and a rank-based smooth left inverse; keep whole-period closure and total
  competitive cost outside that conclusion.
- [x] Obtain independent hand review of both notes.
- [ ] Prove a uniform strict improvement on a precisely revised domain.

## Completing the padded L3 arcs

`docs/PADDED_L3_PMP_CONTINUATION.md` excludes completion of that particular
counterexample family to genuine external switches, for sufficiently small
core size. It does not prove a general L3 improvement theorem.

- [x] Derive the exact two normal control-0 gap forms, including their
  fixed constant terms, and compute the limiting triple-tie data.
- [x] Prove positive limiting gaps up to the first inactive-margin zero.
- [x] Resolve the initial double-zero limit using positive small-core first
  derivatives and uniform positive second derivatives near the join.
- [x] Check smooth log-field continuation across the moving star endpoint
  and the exact reflected incoming state/covector equations.
- [x] Use short-window rank to fix the lift of any longer continuation.
- [x] Compute the auxiliary limiting cost and restrict its budget
  contradiction to an interval within one actual period.
- [x] Independently review the hand argument; retain its existential
  smallness threshold and its proper-family scope.

## L3 counterexample to the at-most-six sufficient lemma

`docs/LOCAL_REVERSE_SIX_OBSTRUCTION.md` supplies an existence family with
arbitrarily small positive cost and no cheaper endpoint-matching replacement
with at most six vertex pieces. The proof is independent of an optimal-control
sufficiency theorem.

- [x] Verify the scaled reverse-edge profile, exact dual, and equality case.
- [x] Check actual adjoint equations, third-control gaps, second derivative,
  switch jumps, and the Green-function sign bound on complete intervals.
- [x] Derive the two endpoint normal columns and their independence.
- [x] Match a smooth exact edge endpoint bound to the terminal covector.
- [x] Prove a uniform compact strict-star box for every cheaper competitor
  and an O(h) bound on all control-0 duration from the monotone tangent angle.
- [x] Justify deletion Taylor estimates at zero durations and merged arcs.
- [x] Force positive leading control-0 mass at both endpoints, then use the
  six-piece bound to force the exact word and the five-coordinate inverse.
- [x] Prove complete strict-star, cost, and sector eligibility.
- [x] Receive independent hand review of all critical identities and limits.
- [x] Keep the local-domain counterexample distinct from geometric embedding
  in a closed minimizer, larger replacement counts, and Reinhardt itself.

## L3 strengthening to all measurable replacements

`docs/LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md` proves fixed-endpoint global
optimality for sufficiently small positive pads, among all measurable simplex
controls and all terminal times. It adds ASZ Theorem 2.6 to the base hand proof.

- [x] Read the primary ASZ paper: Assumptions 2.1–2.3, constraint space (2.8),
  and Theorem 2.6.
- [x] Prove exact convexification and its inverse, and use the state-only
  clock d tau=y dt without enlarging the original admissible controls.
- [x] Verify the normal adjoint, strict gaps, two-way ties, and transverse
  Legendre signs for one fixed positive-pad reference P_H.
- [x] Identify the actual one-dimensional switching variation by rank five,
  and transfer the positive constrained edge Hessian to it.
- [x] Add cost and constant total-duration states; check both free-duration
  transversality conditions and the exact switching-parameter diffeomorphism.
- [x] Extend first-exit bounds to all convexified measurable controls;
  pass to an admissible limit with uniform states and weak-star controls.
- [x] Use tangent turning and exact edge equality to identify the unique core.
- [x] Prove convergence of clocks, inverse clocks, costs, and total duration.
- [x] Splice into one fixed P_H to contradict its one fixed strong neighborhood;
  never assume a uniform radius for shrinking-pad references.
- [x] Independent hand reviewers checked the theorem transfer and full limiting
  argument. This is not external peer review or kernel validation.
- [x] Keep fixed-endpoint global optimality separate from occurrence inside a
  closed Reinhardt minimizer; the latter has not been established.

## Full-domain L1 endpoint rank

`docs/LOCAL_FORWARD_RANK.md` proves rank five throughout the positive
strict-star L1 domain, with arbitrary initial state and unequal factors.
Two independent hand reviews checked the coordinate inverse, action,
four determinant identities and signs, and constrained Hessian correction.

- [x] Resolve both state endpoints by a smooth triangular coordinate change.
- [x] Prove the remaining frame rank is three everywhere by explicit signs.
- [x] Include endpoint curvature in the second-variation formula.
- [x] Retain the exact stationary minimum; do not infer cost descent from rank.
- [x] Distinguish interior full rank from uniform boundary conditioning.
- [x] Classify interior endpoint rank for L4: see LOCAL_SIX_VARIATION.
- [x] Prove full endpoint rank five throughout L3 in LOCAL_MIXED_SIX_RANK:
  arbitrary unequal edge-core data, exact two-dimensional normal determinant,
  fixed-coordinate transport through arbitrary outer arcs, and positive
  duration/factor changes. Independent hand review passed.
- [x] Exclude abnormality and normalized-adjoint ambiguity throughout L3.
- [x] Prove rank five throughout L5 from prefix02101: explicit upper pivot,
  positive two-column residual minor, and strict-star transversality to the
  actual state-stabilizer line. Independent hand review passed.
- [x] Deduce normality and normalized-adjoint uniqueness throughout L5.
- [x] Exhibit an exact actual rank-four L2 point in LOCAL_L2_RANK_DROP:
  fixed initial state, six positive factors, whole-arc strict star, paired
  rank five, and exact inclusion of the state-stabilizer line.
- [x] Prove its cost exceeds pi; retain the distinction between unrestricted
  positive-star rank failure and competitive-domain degeneracy.
- [x] Independently review the assembled certificate and distinct active-margin
  cross-check without asserting a smooth singular endpoint fiber.
- [ ] Resolve rank on the competitive L2 domain or handle any singular inputs
  there directly.

`docs/LOCAL_FORWARD_PMP_LIMIT.md` derives normality on the reduced state
manifold and proves a limitation of first-order PMP. Independent review
checked Hales--Vajjha Section 7.5 and the following exact implications:

- [x] Surjectivity excludes an abnormal reduced covector and makes the
  normalized adjoint unique for a stationary L1 input.
- [x] Standard forward polygons with `N=3k+1>=7` give proper eligible
  six-windows, with exact margins, full-arc sectors, and inherited full PMP.
- [x] Prove their local costs tend to zero using `C_window<6*pi/N`.
- [x] Keep the noncompetitive whole period distinct from the competitive
  local window; no low-cost periodic extension or local optimum is inferred.

## Exact L1 same-word obstruction

`docs/LOCAL_FORWARD_SIX.md` gives one rational-factor input with initial
margins normalized by `sqrt(1975/1684)`. It satisfies every explicit local
input test but is a strict local minimum on its same-word endpoint fiber.
This refutes a method, not L1 or Reinhardt. Independent exact reproduction
used Python 3.12.14 and SymPy 1.14.0; the finite input and command are in
`explorations/local_forward_stationary_obstruction.py`.

- [x] Verify determinant-one normalization and every whole-arc star margin.
- [x] Prove the competitive cost bound by rational/logarithmic inequalities.
- [x] Verify positive Bernstein coefficients for all whole-arc sector tests.
- [x] Use a valid tangent matrix chart and a nonzero five-column rank minor.
- [x] Verify the exact null vector and zero first constrained variation.
- [x] Include endpoint curvature in the constrained Hessian and prove
  its value exceeds `1/200` using `log(11/10)<143/1500`.
- [x] Distinguish strict same-word local minimality from arbitrary-control
  optimality, a full L1 counterexample, or an actual global minimizer.

## Exact nonlocal replacement for the L1 test input

`docs/LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md` supplies an actual six-piece
`012021` replacement at the stationary input, not a numerical equality.
The full L1 domain remains open.

- [x] Keep the initial state fixed and impose all five actual endpoint
  coordinates on a valid chart.
- [x] Use exact rational center and inverse data; verify a contraction on
  a ball of radius `10^-15` by uniform analytic derivative bounds.
- [x] Deduce exact endpoint equality at the fixed point and strict-star
  positivity on all complete arcs.
- [x] Bound logarithms by a finite rational series plus a positive tail;
  control the change from the center to the exact root by the mean-value theorem.
- [x] Prove normalized cost decrease greater than `1/100000`.
- [x] Independently run the supplementary exact checker under Python
  3.12.14 / SymPy 1.14.0, without Lean, Lake, or CI.

The independent appendix fixes the first replacement factor rather than
the last. Its separate Fraction checker passed with Python 3.12.14, including
the factor ball inside `(1,4/3)^5`, all finite residual and inverse-defect
bounds, the contraction/self-map inequalities, and the corrected cost gap.
The same uniform hand bounds apply to either choice of five varying factors.
Nonsingularity and strictness also give the stated nearby-input continuation;
no global coverage or numerical neighborhood radius is inferred.

## Exact L1 full-control needle audit

`docs/LOCAL_FORWARD_NEEDLE_AUDIT.md` strengthens the same-word obstruction
to a strict strong local minimum in the augmented normalized free-log-time
topology. Its exact reproducer passed with Python 3.12.14 and SymPy 1.14.0.
An independent hand review found no material issue in the interval signs,
endpoint conditions, normality, free-duration transversality, or ASZ application.

- [x] Display and prove all twelve whole-arc nonactive Hamiltonian signs.
- [x] Prove unique active maximization at both external endpoints.
- [x] Check all five simple switches and strict crossing derivatives.
- [x] Identify five normalized switches plus total duration with the six
  factor variables; retain the endpoint-curvature correction in the Hessian.
- [x] State the exact strong topology and allow arbitrary nearby controls.
- [x] Keep the distant replacement compatible with the local conclusion.

## Uniform reverse-six subfamily: exact hand certificate

`docs/LOCAL_REVERSE_SIX.md` treats every q>1 with six equal factors and the
specified cyclic initial state. It does not vary that initial state during
the endpoint correction. The normalized tangent chart avoids artificial
singularities of an unnormalized matrix-entry chart.
An independent hand review rederived all four Schur-complement entries and
checked the insertion column, correcting factors, endpoint conventions, and
the use of the implicit function theorem. No material issue was found.

- [x] Fix both tangent and terminal-state endpoints, and recover the actual
  frame endpoint from them.
- [x] Supply a nonzero five-column endpoint minor for every q>1, with an
  explicit three-by-three / two-by-two elimination calculation.
- [x] Display the correcting factor derivatives and check both endpoint
  variations; use the implicit function theorem for exact endpoint equality.
- [x] Keep the inserted factor positive and preserve every whole-arc star
  inequality by continuity and monotonicity of the vertex flows.
- [x] Derive the exact cost derivative and prove it is strictly negative by
  log(q)>2(q-1)/(q+1), without numerical signs as premises.
- [x] Record loss of a uniform variation margin as q approaches one.
- [x] State seven replacement pieces and a proper subfamily; do not mark the
  full L2 target or a uniform complexity bound complete.

## Exact L3 strong local minimum

`docs/LOCAL_L3_STRONG_MINIMUM.md` gives a single eligible `021210` input,
with all factors `5/4` and raw initial state `(1,2,193/112)`. Its independent
hand review checked all full-arc sign proofs and the ASZ theorem's hypotheses,
including the free total log duration as a constant state. A further review
checked the normalization, multiplier, finite variation space, and scope.
The exact finite reproducer completed with Python 3.12.14 and SymPy 1.14.0.

- [x] Verify whole-arc strict star and all sector signs by rational Bernstein
  coefficients, with an exact competitive-cost bound.
- [x] Use a valid full endpoint chart, rank five, and the one-dimensional
  kernel with fixed initial state.
- [x] Compute the constrained Hessian including endpoint curvature and prove
  its positive sign with elementary logarithm bounds.
- [x] Prove every nonactive full-arc needle gap is positive, with exactly two
  maximizers at each internal switch and a strict crossing derivative.
- [x] Check normality, free-duration transversality, and the finite second
  variation for the fixed-interval augmented problem in ASZ Theorem 2.6.
- [x] State strong local optimality in the normalized topology including
  duration; do not claim it is a global endpoint minimum or refutes L3.
- [ ] Exclude distant cheaper replacements. Not supplied by this certificate.

## Exact L4 rank and switch-needle obstruction

`docs/LOCAL_SIX_VARIATION.md` proves the full positive-domain L4 rank
lemma, exact endpoint compensation, and an eligible stationary family
with every missing-control switch needle strictly unfavorable.

- [x] Use the full paired tangent spaces and explicitly quotient the
  one-dimensional state centralizer; avoid matrix-entry chart artifacts.
- [x] Verify the nonzero determinant by the displayed short elimination.
- [x] Specify the stationary root by a rational interval and a strictly
  negative derivative; prove the logarithm bounds by series remainders.
- [x] Check all five positive compensated derivatives and cost eligibility.
- [x] Prove full-arc sectors with rational Bernstein coefficients.
- [x] Remove zero outer durations by the implicit function theorem while
  retaining stationarity, eligibility, and all five strict needle signs.
- [x] Independently run the finite exact checker with Python 3.12.14 and
  SymPy 1.14.0; keep it supplementary to the hand certificate.
- [x] Distinguish this switch-only obstruction from arbitrary-control
  local or global optimality and from a refutation of full L4.

## Exploratory local-fiber probe: inconclusive

The retained script `explorations/local_six_fiber_probe.py` records a finite
floating-point diagnostic. Reproduction environment: Python 3.13.5,
NumPy 2.3.5, SciPy 1.17.0; RNG seed 761106. There are five fixed template
words and three deterministic random initial tuples per word. Initial
p_0,p_1 are drawn from [0.7,1.4], p_2 is fixed by the determinant equation,
and initial log factors from [0.025,0.12]. The script prints every generated
input and output. No interval arithmetic is used.

The solver is SLSQP with 150 iterations, `ftol=1e-11`, log factors bounded
between 1e-7 and 2, and numerical state margins at least 1e-7. Endpoint and
cost formulas are exact expressions evaluated in floating point. Derivatives
are computed by complex-step differentiation. The script fixes three entries
of F on a chart with F_00 nonzero and two terminal state margins.

In the retained experiment, 6 of 15 runs reported convergence and reached
a log factor at the numerical lower bound. The other 9 did NOT converge;
their endpoint residuals ranged up to approximately 8.7e-6. Thus even the
reported cost decreases on those failed runs are not established feasible
improvements. The successful runs are approximate and do not reach an exact
zero-duration boundary.

The probe does not certify the sector eligibility condition, cover the full
parameter domain, treat singular ranks, or prove any local exclusion.
It was used only to inspect numerical conditioning and possible deformation
directions. No statement in the hand coverage proof depends on it.

## Reproducibility and scope

The archived `docs/SIX_ARC_012102_MOMENTS.md` was completed before the new
priority. Its exact cost implication, logarithmic coefficient bounds, and both
finite-boundary moment inequalities passed independent hand review. Neither
interior inequality is proved. Preserving this work does not close a local
target or continue increasing-length enumeration.

- [x] Retain the exact finite graph checker and its finite input specification.
- [x] Retain the numerical probe with fixed seed, versions, constraints, failed
  outcomes, and a command that prints all finite inputs/results.
- [x] Separate hand proof, exact finite computational cross-check, and
  inconclusive floating-point exploration.
- [x] Keep the old proof notes and pinned dependencies unchanged.
- [ ] Re-run the entire historical source audit. Not performed or required for
  these documentation and exploration changes.
- [ ] Lean elaboration, kernel dependency inspection, and independent-kernel
  verification. Deferred.
