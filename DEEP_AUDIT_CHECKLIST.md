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

## Active global proof checks

The active entry point is [GLOBAL_REDUCTION_PLAN](docs/GLOBAL_REDUCTION_PLAN.md).
The original five-template sufficient domain remains refuted.

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
- [x] Obtain uniform qualitative singular clearance for actual minimizers,
  without asserting it for all competitive PMP trajectories.
- [x] Prove transport of the reduced costate to a fixed plane and uniform
  first/second derivative estimates without differentiating measurable controls.
- [x] Choose closed angular sectors with robust exclusions and generic guard
  lines; at most one or two zeros of each projection bound the edge intervals.
- [x] Use the minimizer edge bound explicitly; do not assert it for arbitrary
  full-system PMP lifts. Finite cover then gives a common finite piece bound.
- [ ] Supply a certified numerical singular clearance and a specific integer
  bound. The existential uniform theorem does not identify a finite case list.
- [ ] Complete the remaining global comparison and affine equality theorem.
- [ ] Run kernel validation (deferred under the user's current workflow).

The new hand proofs received separate internal mathematical reviews. Such
review is not external peer review or Lean kernel validation. No new Lean
file, build, typechecking, Lake command, or CI was introduced or executed.

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
- [ ] Classify interior endpoint ranks for L2.

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

