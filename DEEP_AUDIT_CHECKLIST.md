# Audit boundary for the bounded-reduction checkpoint

Date: 2026-11-06. New work is hand research and explicitly scoped exploration.
No new Lean file was added; no compilation, Lake, typechecking, kernel audit,
or CI was run. No independent reviewer checked the new coverage proof in this
session; the mathematical check is the displayed hand argument plus a distinct
finite-graph computational cross-check.

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
- [ ] Independent mathematical review of the new coverage and domain note.

## Endpoint and domain checks

- [x] Keep two initial-state coordinates and six factors explicit.
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
