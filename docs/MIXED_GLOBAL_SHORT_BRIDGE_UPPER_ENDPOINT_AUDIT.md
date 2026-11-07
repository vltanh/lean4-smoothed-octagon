# Independent audit of the whole short-bridge upper endpoint

Date: 2026-11-07 UTC. Reviewer: root agent, independently of the author.

I read the complete upper-endpoint proof, its exact checker, and the
static coefficient table. All thirteen exact checks pass. The hand
argument also passes without a mathematical correction.

The quantitative order follows from the actual secant continuation and
eta/xi>=2/7: differentiation of (alpha+2x/7)/beta has a strictly positive
lower bound before integration from (x,1). The order parametrization
covers precisely the required half-open interval, and its leading
coefficient argument retains a strict reserve at the closed upper end.

The common-lift formulas give the displayed numerator N=PQ R(T), with
P,Q positive. The second derivative sign uses only Z<1+x and v<U(s):
when Z>0, Z/q<s<2s(1-s), and when Z<=0 the sign is immediate.
Both coefficients of the incident norms in N'(q0) are positive. The
six-block identity for its negative has positive factors and a strict
j>0 term, hence supplies a genuine all-scale derivative sign.

At q0, both norm coefficients of N are strictly positive. In particular
(Z-S) and (Z-(q0-1)S) are both negative, while the remaining squared-sum
difference is nonnegative. Thus using the rational norm upper bound
has the stated direction. Its logarithm inequality follows from the
strictly positive displayed derivative and equality at zero.

I checked the exact table reconstruction: 803 unique positive integer
entries, the explicit square with coefficient 73344, and both strict
j^3 reserves. The only negative expanded coefficient is exactly the
cross term absorbed by that square. There is no condition on D or w,
and no positivity of an unproved endpoint factor is inserted.

The conclusion is the entire strict endpoint sign R(T)<0 for q>=q0,
including T=2 and either diagonal sign. It is not by itself an interior
maximum exclusion. No trajectory-preserving variation, endpoint rank,
new normal multiplier, Lean, Lake, typechecking, CI, or floating sign
calculation is used by the hand proof or this audit.
