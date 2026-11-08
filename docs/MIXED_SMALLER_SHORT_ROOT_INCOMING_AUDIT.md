# Audit of incoming-norm monotonicity for the short-root residual

Date: 2026-11-08 UTC. Independent identity and domain review of
[MIXED_SMALLER_SHORT_ROOT_INCOMING_MONOTONICITY](MIXED_SMALLER_SHORT_ROOT_INCOMING_MONOTONICITY.md).

## Accepted statement

For `1 <= alpha <= x <= beta`, `x > 1`, `0 < p <= r_A` and
`0 < q <= 1/7`, the normalized envelope residual is strictly
increasing in its incoming scalar norm `u`. This remains a scalar
comparison at fixed geometry, normalized duration and scale; it
neither establishes an outer root nor transfers a physical cost,
upper Casimir cap or outgoing norm floor to the changed norm.

## Algebra and strictness

Differentiating the displayed residual term by term gives

\[
R_u^*=S+r_A^{-1}-p d S
 +q\{p(d^2+d\varepsilon S)-2d-\varepsilon S\}.
\]

The derivative is affine in each of `p,q` separately. A point in the
closed rectangle is a convex combination of its four corners, with
nonnegative weights summing to one. Thus four strict corner signs
suffice, and no critical-point selection is involved.

At `p=q=0` the value is `S+1/r_A>0`. At `p=0,q=1/7`, multiplying
by `7 alpha^2` yields exactly

\[
6\alpha^2S+(5\alpha^2-1)+3(\alpha\beta-x)+4\beta x.
\]

All denominators are positive; each summand is nonnegative and the
first is strictly positive. In particular `alpha beta >= x` follows
from `alpha>=1` and `beta>=x`.

At `p=r_A`, multiplying by `alpha(alpha+beta)` for `q=0`, and by
`7 alpha^3(alpha+beta)` for `q=1/7`, gives the full polynomials
`P_0,P_1` displayed in the source. The substitution
`alpha=1+z`, `x=1+z+h`, `beta=1+z+h+k` produces their stated terms
by ordinary expansion. Every coefficient is explicitly positive.
Because `z+h=x-1>0`, either a term containing `z` or the displayed
positive linear term in `h` is strict. This also covers `k=0`,
`alpha=1`, and `alpha=x`.

These checks do not call the logarithmic residual at `p=0`: only
its polynomial derivative is continuously extended to that corner.
The actual residual remains evaluated at strictly positive `p`.
The proof needs no sign of the short diagonal, no equality of
secants, and no lower bound `x>=2`.

## Acceptance and remaining scope

A separate second reading of the proof checked the bilinear derivative,
the four corner reductions, the strictness at `alpha=1` and
`alpha=x`, and the restriction to scalar incoming-norm substitution.
The conclusion is accepted with precisely the domain stated above.

The incoming-norm substitution is accepted throughout the exact
stated domain. The complete root-to-shear implication and physical
completion-cost contradiction are separate obligations. No numerical
optimizer, interval execution or hidden coefficient assertion is
used in this lemma: the complete corner polynomials and their
positive terms are printed in the source.
