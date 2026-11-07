# Audit boundary for the bounded-reduction checkpoint

Date: 2026-11-07. New work is hand research and explicitly scoped exploration.
No new Lean file was added; no compilation, Lake, typechecking, kernel audit,
or CI was run. The coverage proof received an independent hand review of its
sign catalogue, twisted seam, run alternatives, and one-period window condition,
in addition to the distinct finite-graph computational cross-check. The analytic
local targets have not been proved or independently certified.

The complete earlier audit is preserved at
[798a7e1 / DEEP_AUDIT_CHECKLIST.md](https://github.com/vltanh/lean4-smoothed-octagon/blob/798a7e119e254c3ee23073de615288986fa61929/DEEP_AUDIT_CHECKLIST.md).
Its historical source scans and review claims are not new validation performed
in this checkpoint. All existing mathematical and Lean proof files are retained.

## Coverage checks

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
- [ ] Prove any of L1-L5 on its full stated domain.
- [ ] Certify singular boundary faces of the bounded-coordinate compactification.
- [ ] Deduce the unconditional bound N<=5.
- [ ] Prove unrestricted global minimality and affine rigidity.

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
- [ ] Classify interior endpoint ranks for L2–L5.

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
