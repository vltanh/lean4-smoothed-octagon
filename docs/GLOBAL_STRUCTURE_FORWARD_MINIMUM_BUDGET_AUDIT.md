# Audit of the whole forward budget at a global minimum

Date: 2026-11-07 UTC. Independent internal hand review of
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
No Lean, Lake, typechecking, or CI. This is not kernel validation or
outside peer review.

## Verdict and scope

The proof passes. In a competitive entirely forward normal period with
at least seven positive arcs, choose a global minimum active margin
`a` and its neighbors `b,c`. The established scale bounds and the new
whole-period comparison give

\[
\frac43<a^2<\frac{20}{11},\qquad
q=\frac{(a+b)(a+c)}{a^2+4}<\frac74.
\]

The stronger displayed bound `C >= B(a,q)` is retained. This is a
necessary restriction on the remaining F domain, not a proof that the
Casimir exceeds the competitive cap or that a cheaper closed variation
exists. The actual exterior factors and both exterior PMP gaps are
still required in the remaining comparison.

## 1. Whole-period action and the uniform scalar comparison

I checked the edge normalization `8J=sum G`, `C=sqrt(12)J`, and the
use of the earlier positive-partial-derivative theorem on the whole
positive orthant. Lowering all margins except `a,b,c` to the global
minimum `a` leaves exactly two edges of type `(a,b)`, two of type
`(a,c)`, and `N-4` edges of type `(a,a)`. The two neighboring indices
are distinct, and their incident edges are counted separately for
every `N>=7` in scope.

The diagonal edge action vanishes at `a^2=4/3` and strictly increases
with the diagonal argument. Therefore `G(a,a)>0`, and replacing
`N-4` by three is in the correct direction. The seven-entry array is
a scalar comparison valid uniformly for every `N>=7`; it is not an
enumeration or an assertion of seven-piece frame closure. Neither the
cost comparison nor its intermediate arrays need preserve PMP or
the actual matrix endpoint.

## 2. Ordinary concavity and scale monotonicity

I independently checked

\[
G_{ab}=2\left(1-\frac{ab}{(a+b)^2}\right),\qquad
G_{abb}=\frac{2a(b-a)}{(a+b)^3}.
\]

For fixed `b`, the latter is the derivative of `G_bb` in `a`, and is
nonnegative on `a<=b`. If `b<=2`, increasing `a` to `b` gives the
displayed diagonal bound with `rho` in `[1/4,1/2]`. Its derivative
has the claimed sign, and `1/2-log 2<0`. If `b>=2`, increasing `a`
to the continuous star endpoint `4/b<=b` gives
`log rho+1-rho<0`. Thus `G_bb<0` on the entire required domain.

The identity `G_b(a,b)=4C_b(a,b,a)` gives positivity from the established
cyclic derivative calculation. At fixed `a`, the derivative in `b`
of `G_a-G_b` is `G_ab-G_bb>0`, and its diagonal value is zero.
Consequently `G_a>=G_b>0`. These facts justify the optional chord
bound as well as the fixed-factor scale comparison.

On the path `b_*(a,q)=sqrt(q(a^2+4))-a`, decreasing `a` preserves
both `b_*>=a` and `ab_*<4`. The latter gives
`-1<partial_a b_*<0`. Therefore the derivative in (13) is strictly
positive; the extra six diagonal derivatives are counted correctly.
The path ends at `a=2/sqrt(3)` within the concavity domain. It is a
scalar comparison, not a claimed change of the actual trajectory.

## 3. Convexity in the logarithm of the adjacent sum

Ordinary concavity is not used to average the neighbors. I checked
the separate change `w=log(1+x)`, `x=b/a`, and differentiated the
dimensionless edge action directly. After dividing by `1+x`, the
second derivative is the stated rational expression minus
`(2x+1)log H`. On `u=4/a^2` in `[11/5,3]` and `x>=1`, one has
`H>=1`; thus `log H<=H-1` gives a lower bound.

The cleared lower numerator is

\[
2y^4+4y^3+(23-8d)y^2+(12-2d^2)y+(24-15d+2d^2),
\]

where `0<=d<=4/5` and `y>=0`. Its last three coefficients are at
least `83/5`, `268/25`, and `332/25`, respectively. Hence the
logarithmic-coordinate convexity is strict. Jensen's inequality
therefore preserves the product `(a+b)(a+c)` and gives the claimed
`b_*`, rather than using an ordinary arithmetic mean.

The geometric mean of the adjacent sums preserves `b_*>=a` and
strict star. Positivity of `G_b` also checks monotonicity of the
two-variable lower bound in `q`.

## 4. Exact cutoff and boundaries

I independently reproduced the rational logarithm majorant, its
derivative sign, all three square-root bounds, and the direction of
each substitution at `q=7/4`. The coefficient `4-sqrt(7)` of the
subtracted positive logarithm is bounded above by `13543/10000`;
the logarithm's argument is bounded above by `17500/14271`.

The resulting cost lower bound is exactly

\[
\frac{3131077749426660736399}{981902909728125000000}
>\frac{313}{100}>A_{\rm oct}.
\]

Its positive gap above `313/100` is
`57721641977629486399/981902909728125000000`. Thus `q=7/4` is
excluded along with every larger factor. The circle scale is only a
continuous scalar comparison endpoint; the actual minimum is strictly
above it by the previous theorem. The upper scale, strict-star, and
positive-factor assumptions of the actual period remain unchanged.

Finally `rt=rho/q>4rho/7`, together with `r,t<=1/2`, gives the stated
strict individual bounds `r,t>8rho/7`. No additional whole-period
case exclusion follows from these inequalities alone.

The supplementary checker
`explorations/global_structure_forward_minimum_budget_certificate.py`
passes all 21 exact identities and rational sign checks. The scope,
comparison paths, and use of the actual whole-period budget are the
hand arguments above.
