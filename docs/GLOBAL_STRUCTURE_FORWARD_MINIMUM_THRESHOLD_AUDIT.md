# Independent audit of the forward minimum threshold

Date: 2026-11-07 UTC. Independent internal hand review of
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md).
No Lean, Lake, typechecking, or CI was run.

The theorem passes this review with its stated scope: at a whole-period
global minimum with two forward incident switches, the actual auxiliary
variable satisfies `b_i>2 gamma a_i^2`. Pure-forward periods require
`N>=7`; mixed periods use the already proved reverse-centre scale bound.
The conclusion concerns the onsite scalar-dual term. It does not
establish negativity of a full principal block or close F or M2.

## Rational cap and minimum scale

The square-root, logarithm, and Machin-series estimates have the
correct strict directions. Substituting them in the positive exact
octagon numerator gives the stated upper cost bound. The endpoint-
dependent cost--Casimir inequality then yields
`gamma^2<42025/228528<23/125<3/16`, with the physical normalization
`kappa=sqrt(12) gamma` retained.

The entirely forward cyclic action has strictly positive derivatives
on the entire positive orthant. This justifies the coordinatewise
comparison with a constant array even when that comparison leaves
the positive-factor domain; it is an inequality between scalar
expressions, not an asserted admissible deformation. At
`m^2=20/11`, the displayed `N>=7` lower bound and the rational upper
estimate for `log(5/4)` give cost strictly above the octagon budget.
Thus `rho_min<5/16`. In a mixed period a reverse centre has
`a^2<4/3`, so its global minimum has `rho_min<1/4` independently
of any monotonicity assertion for the mixed action.

The added four-switch restriction (9a) also checks directly. A turn
immediately before or after a `++` global minimum has the displayed
factor ratio, whose strict positivity condition `q>1` would put a
smaller active margin two arcs away. Both signs and index placements
are correct. This uses actual complete positive arcs and extends
through the twisted seam; it supplies four consecutive forward
switches, without silently extending that count to five.

## The two scalar ranges

For `rt<rho<=1/4`, assume `L>=0`. The actual positive Gram pairing
and `gamma^2<3/16` give `E<3rho`. Holding `r,t,u,v` fixed makes
`G(x)=E(x)-3x` nondecreasing on `[rt,rho]`, so `G<0` on that
whole interval and the displayed `F'(x)` is positive. At its lower
endpoint, the polynomial identity (17) gives zero when the two
switch norms are at their lower bounds.

Raising these norms to their actual values is legitimate: `E(rt)`
increases along that path but remains below its final value `3rt`.
Consequently the partial derivatives of `4uv-E(rt)^2` are
nonnegative as claimed. The argument also covers a negative value
of `E(rt)`; it never divides by that value or silently assumes its
sign. Therefore `F(rho)>=F(rt)>=0`, contradicting the strict
Casimir bound.

For `1/4<=rho<=5/16`, the contradiction follows from `u,v>=3/4`
and the monotone substitution of the sharper rational cap in (19).
The resulting quadratic is convex, and both displayed endpoint
values are strictly below `9/4`. The two ranges overlap without
leaving a boundary case uncovered.

## Translation and exact validation

The conversion

\[
b-2\gamma a^2
=-\frac{K L}{8\gamma(1-\rho)^2}
\]

has the correct positive normalization factors. The onsite coefficient
matrix then has two negative diagonal entries and determinant
`8 gamma (b-2 gamma a^2)/(K^2(b^2+4))>0`, proving its negative
definiteness. The source note correctly keeps the positive incident
edge terms and the full endpoint constraints as unresolved parts of
the global index problem.

The supplementary command

```
python3 explorations/global_structure_forward_minimum_certificate.py
```

passed all 24 exact identities and rational sign checks during this
review. The domain, monotonicity, normal-PMP interface, and scope
arguments above are hand checks. No correction is required. This is
internal mathematical review, not external peer review or kernel
validation.
