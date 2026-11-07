# Pure-forward dependencies for a proof without computer assistance

Date: 2026-11-07. This inventory separates the current computer-assisted
baseline from the replacement hand arguments. It does not claim that
the pure-forward hand-only gate is closed.

## Essential quantified signs still to replace

| Input | Existing justification | Hand replacement status |
| --- | --- | --- |
| `U=4/a_min^2<3` | [SMALL_FORWARD_MINIMUM_HAND_PROOF](SMALL_FORWARD_MINIMUM_HAND_PROOF.md), with its elementary integral/cubic comparison | Closed by hand. The [independent audit](SMALL_FORWARD_MINIMUM_HAND_AUDIT.md) accepts the entire hard face, also supplying the mixed minimum-structure prerequisite. |
| `z,w<5/4` | The 8,183-node [neighbor cover](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md) | Open. A proved exterior-factor concavity lemma reduces a weaker sufficient `z,w<4/3` target to two planar faces. No signs on those whole planar faces have yet been accepted by hand. |
| Complementary Casimir contradiction | The 20,999-node [five-variable cover](GLOBAL_FORWARD_PERIOD_EXCLUSION.md) | Open. The new hand lemma proves the entire Casimir implication from `z,w<=4/3` and `delta u+delta v<=1/39`. The latter norm estimate remains unproved. |

The H5 table gives its full coefficients, not merely an execution count.
It is now replaced in the active hand route by the integral/cubic proof
linked above. The baseline certificate is preserved as historical evidence;
its coefficient count is not a premise of the new hand argument.

## Essential inputs that already have readable hand arguments

- The upper active-minimum bound `a_min^2<20/11`, hence `U>11/5`,
  follows from coordinatewise monotonicity of the actual cyclic scalar
  cost, seven retained pieces, and a short logarithm estimate in
  [GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md).
- Negative ellipticity follows from the actual stationary Jacobi
  system and the positive-kernel-vector contradiction in
  [GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md).
  It is not an output of either F cover.
- The whole-period competitive Casimir cap follows from the spectral
  cost theorem and explicit rational bounds for the octagon cost and
  pi. The stronger current hand cap is
  `gamma^2<9193/50000` in
  [HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md).
- The centered stationary equations, the scalar determinant
  factorization and the exact Casimir formula are displayed algebraic
  identities in [GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md).
  Their use retains one actual PMP lift; no fitted local multiplier
  or endpoint-rank assumption is needed.
- The two exterior missing-control floors are derived from the actual
  first/last Hamiltonian inequalities in Sections 1--2 of
  [MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
  Those identities do not depend on the hard-face sign table later in
  that note. Weak third-control ties remain covered.
- The symmetric edge cost has a positive mixed derivative and is
  increasing and concave in the second argument over the stated
  minimum domain. These derivative signs and their domain are proved
  in [GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
- The central linear budget uses one explicitly displayed degree-eleven
  polynomial identity with twelve positive integer coefficients in
  [GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md).
  This is a small exact hand-checkable identity, but remains a named
  premise of the current refinements. The new exterior-factor budget
  reuses that identical one-variable contradiction and introduces no
  new sign table.
- The broad circular exclusion in
  [GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md)
  has a complete displayed estimate using positive row sums, a cubic
  logarithmic remainder and a completed square. Its proof does not
  require execution of its supplementary symbolic checker.

## Computational or quantitative material that need not be imported

The earlier small-corner interval-Hessian table in
`GLOBAL_STRUCTURE_FORWARD_CIRCLE_CORNER` is superseded for this
application by the broad circular hand argument. It is unnecessary
once the conditional Casimir lemma in `HAND_FORWARD_LEMMAS` is applied,
because that lemma treats the entire stated scalar domain directly.

The separate factor bound `q<7/4`, the finite ceiling `N<=61`, and the
length-by-length forward experiments are not premises of the present
uniform hand route. The linear neighbor budget already bounds the
initial neighbor domain. No catalogue of complete words is needed.

The full forward endpoint-rank and dual-Hessian/index results are also
unnecessary for a necessary-condition contradiction using the actual
normal lift. They remain possible alternative research routes; ordinary
Jacobi inertia or an unproved negative-subspace assertion must not be
substituted for the missing scalar hand inequalities.

The finite-before-normality and geometric/PMP foundation retain their
separate global dependency audit. This F-specific inventory does not
claim to replace any computational premise elsewhere in that upstream
chain.
