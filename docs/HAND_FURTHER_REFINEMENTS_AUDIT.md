# Independent review of further hand refinements

Date: 2026-11-07 UTC. Internal mathematical review.

## Explicit turn floor

[EXPLICIT_TURN_NORM_FLOOR](EXPLICIT_TURN_NORM_FLOOR.md) is accepted.
Substituting z=1/q in the proved logarithm upper bound gives exactly
the two positive reciprocal terms to which AM--GM is applied. Their
optimal point lies in 0<=z<=1 for the entire stated eta interval.
The original inequality is strict for q>1. The radical factorization
and derivative prove the floor is at least 3/4 and increases with eta.
The secant identification uses the actual positive turn factor, and
the smaller-turn ordering gives the stated common norm floor.

## Nonpositive short diagonal at the opposite floor

[MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
is accepted. The incoming norm bound follows directly from its integral.
Both scalar monotonicities have the claimed signs when D<=0; the
subsequent upper comparison has a positive coefficient of u and a
negative coefficient of D. Thus the norm upper bound and quadratic
lower bound for D are used in the correct directions.

The strengthened short order gives the displayed quadratic in beta/x.
For x<=2 it is positive, excluding D<=0 there. Completing its square
for x>=2 yields the stated single-variable rational identity. Dividing
its numerator by x^5 makes every nonconstant term increasing, and its
value at x=2 is 6005/32>0. The transport identity then gives w<=3/4,
with the stated strictness. No original lower Casimir cap or outer-root
sign is needed for this lemma. The remaining positive-D part and the
other stopping faces are still open.

## Exact forward targets and obstructions

[HAND_FORWARD_OPEN_TARGET](HAND_FORWARD_OPEN_TARGET.md) states the
remaining norm inequality with its complete structural domain and
genuine exterior floors. Its sum-slack identity is a direct elimination
of the two stationary equations. The displayed factorizations prove
the two row weights are positive. They do not prove the remaining
slack numerator positive.

The symmetric rational obstruction is valid: the stationary solution
has positive increments whose sum exceeds 1/39, while the structural
cost budget holds and the genuine floors fail. Its elementary rational
logarithm comparisons establish all strict signs. The two limiting
families also satisfy their stated structural conditions and force the
incompatible constant-multiplier bounds 4/3 and 26/15. This refutes only
the specified relaxations, not the intended inequality under the actual
floors. The final neighbor and norm-sum signs remain unproved.
