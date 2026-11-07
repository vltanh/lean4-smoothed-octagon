# Independent hand review of the analytic refinements

Date: 2026-11-07 UTC. Two independent internal mathematical readings.
No execution result is used to establish a sign. No Lean, Lake,
typechecking or CI.

## Reviewed scope

The review accepts Sections 1--4 of
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md): the sharper
competitive cap, reverse-centre scale `a^2<2/3`, quantitative outgoing
forward norm gap and its transfer to the concave endpoint alternative.
It does not assert a hand exclusion of the remaining F or M2 domains.

## Competitive cap and reverse-centre scale

The first independent reading checked the directions of all substitutions
into the octagon cost and spectral inequality, the displayed rational
differences, and the relation `kappa^2=12*gamma^2`. The use of a complete
competitive period occurs before any scalar boundary comparison.

For the reverse centre, `E<3r/2,3t/2` holds on the entire norm rectangle,
so both norm-lowering derivatives have the required positive sign. At
`rho>=1/7`, lowering `r` to `rho/t` stays inside `r<1/2` and reaches
`rt=rho`; the negative coefficient of `r+t` has the correct inequality
direction. This yields `E0>=15/56>0`. Raising `r,t` to `1/2` therefore
lowers the squared Casimir. The derivative formula for `G`, monotonicity
in positive `B`, factored identity and three-term logarithm estimate are
all valid on the claimed closed-open interval. The final lower bound is
exactly `18387201/100000000`, with the stated positive margin over the
competitive cap.

No step assumes the desired scale bound while proving it. All variables
in this argument refer to the original actual reverse centre.

## Norm gap and endpoint transfer

The second independent reading checked both logarithm bounds directly
from their integral proofs, including strictness for `q>1`. Multiplying
by `12q(q+1)` yields the displayed quadratic. Its leading coefficient is
positive; its discriminant has the stated factorization. The remaining
quadratic in `eta` is negative by convexity and its two endpoint values.
At `eta=1/2`, the full polynomial is `2(q-1)^2`, so the overlapping
piecewise definition causes no missing boundary case.

For the physical application, the outgoing missing-control formula is
used with `x=eta/q_r`, not the incoming endpoint fraction. The actual
strict-star inequality gives `0<eta<1`, and the next forward factor is
strictly greater than one. The same actual `d,r` persist during the
scalar comparison, so the norm threshold is unchanged. Since the next
norm decreases with `w`, the asserted strict interval for the actual
`w` follows. Concavity then gives exactly the stated strict endpoint-cap
disjunction. Neither artificial endpoint inherits unproved physical
switching conditions.

## Acceptance

The refinements have complete readable hand proofs and are accepted as
new necessary conditions. They require no interval cover or large
coefficient table. The broader hand-only gates remain open in
[HAND_PROOF_STATUS](HAND_PROOF_STATUS.md).
