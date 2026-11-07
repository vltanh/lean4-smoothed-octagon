# All-forward dependencies for a proof without computer assistance

Date: 2026-11-07. The all-forward hand-only gate H-F is closed by
[HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md),
using the [independently reviewed scalar norm proof](HAND_FORWARD_NORM_AUDIT.md).
The mixed gates H-S and H-N, and the full final audit H-A, remain open.

## The three quantified forward inputs now have hand proofs

| Input | Hand justification | Status |
| --- | --- | --- |
| U=4/a_min^2<3 | [Small-forward-minimum integral/cubic proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md), with [independent audit](SMALL_FORWARD_MINIMUM_HAND_AUDIT.md) | Closed. Replaces the hard H5 coefficient table and also supplies the shared mixed minimum-structure input. |
| z,w<4/3 | [Integral neighbor proof](HAND_FORWARD_NEIGHBOR_INTEGRAL.md), [asymmetric completion](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md), and [audit](HAND_FORWARD_NEIGHBOR_AUDIT.md) | Closed. Replaces the older 8,183-node cover, which proved the stronger but unnecessary bound 5/4. |
| Complementary Casimir contradiction | [Conditional two-norm theorem](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md), [sum initial/low-D proof](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md), [high-D proof](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md), and [larger-neighbor norm proof](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md) | Closed. The exact first row and genuine exterior floors imply delta u+delta v<1/35 and delta v<1/64. These imply gamma^2>23/125, contradicting gamma^2<9193/50000. The 20,999-node cover is not used. |

The two residuals decrease as the larger neighboring margin increases,
so both reduce to equal-neighbor inequalities. The sum proof uses a
quantitative initial-value cancellation, elementary rational logarithm
bounds, six displayed coefficient polynomials and one quartic sign.
The larger-neighbor norm proof uses exterior-factor concavity and two
tangent values, whose finite coefficient identities have explicit short
bounds. None of these signs is delegated to an executable test.

The earlier sufficient targets delta u+delta v<=1/40, <=1/39, and the
stronger homogeneous target are not needed. Their unresolved status
does not leave an obligation in this completed route.

## Essential inputs with readable hand arguments

- The upper active-minimum bound a_min^2<20/11, hence U>11/5,
  follows from coordinatewise monotonicity of the actual cyclic scalar
  cost, seven retained pieces, and a short logarithm estimate in
  [GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md).
- Negative ellipticity follows from the actual stationary Jacobi
  system and the positive-kernel-vector contradiction in
  [GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md).
  It is not an output of either forward cover.
- The whole-period competitive Casimir cap follows from the spectral
  cost theorem and explicit rational bounds for the octagon cost and
  pi. The hand cap is gamma^2<9193/50000 in
  [HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md).
- The centered stationary equations, determinant factorization and
  exact Casimir formula are displayed algebraic identities in
  [GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md).
  Their use retains one actual PMP lift; there is no fitted local
  multiplier or endpoint-rank premise.
- The genuine exterior missing-control floors follow from the actual
  first/last Hamiltonian inequalities in Sections 1--2 of
  [MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
  Those identities do not depend on the hard-face sign table later in
  that note. Weak third-control ties remain covered.
- The symmetric edge cost has a positive mixed derivative and is
  increasing and concave in the second argument on the required domain.
  These signs are proved in
  [GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
- The stronger exterior-factor budget in Section 3 of
  [HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) retains both actual
  exterior factors, using the positive mixed derivative and explicit
  seven-edge accounting. Its one-variable cost contradiction reuses the
  displayed degree-eleven identity with twelve positive coefficients in
  [GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md).
  This is an explicit finite algebraic proof, not a coefficient-count
  assertion.
- The exact positive central offset and the exterior-factor concavity
  used by the scalar norm proof are established in Sections 1--2.1 of
  [HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md).

## Material not imported into the hand proof

The historical H5 table, 8,183-node neighbor cover and 20,999-node Casimir
cover remain preserved as parts of the computational baseline. None is
a premise of H-F. The older interval-Hessian circle calculation and even
the broad circular comparison are unnecessary here, because the new
two-norm theorem treats the entire required scale domain.

The separate factor bound q<7/4, finite ceiling N<=61 and length-by-length
forward experiments are also unnecessary. This is a uniform period
argument, with no enumeration of increasing word lengths.

The forward endpoint-rank and dual-Hessian/index results remain possible
alternative routes. Ordinary Jacobi inertia or an unproved negative-space
assertion is not substituted for a scalar sign.

The finite-before-normality and geometric/PMP foundation retain their
separate global dependency audit. Closing this forward-specific gate does
not close the remaining mixed cases or the final hand-only assembly.
