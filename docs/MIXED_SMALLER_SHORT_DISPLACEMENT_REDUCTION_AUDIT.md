# Audit of the displacement reductions and exact shape inputs

Date: 2026-11-08 UTC. Separate reading of the weight, scale,
zero-scale, and central-beta arguments. These are accepted scalar
reductions. The terminal central and outer signs retain their own
proof obligations; this audit alone does not prove the displacement
restriction for every actual short bridge.

## 1. Original-root positivity and the full envelope

The [weight reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md)
starts with an actual descending root and its actual outgoing norm
floor. Since the weight is positive, their combination is strictly
positive before any comparison. The opposite-turn derivatives have
the displayed common factor. Its proof uses a concave quadratic in
normalized duration and then two concave quadratics in alpha. All
four endpoint signs are strict for x>=2. Thus the whole envelope is
available, without transporting the norm floor separately.

The upper incoming bound has the full required domain. For the exact
equal secants, the derivative of
`(B-1)[f(B)-g(B/x)]` is nonpositive for B>=x. The second secant at the
original beta makes that difference positive there, so the first
secant decreases from x to beta. This proves u<=V(x) without assuming
the displacement bound being sought. The rational diagonal estimate
then gives u<19/25. The lower alpha bound, both r_A bounds, and
0<D/alpha^2<3 follow from the accepted orders and S0.

The incoming coefficient is bounded below by 17/182. In this step
the norm floor is not needed at a comparison point. The estimate
uses tau+m<=T+1, D/Q<1, d<3/7, lambda*S<=19/6 and r_A<=13/30.
The coefficient is independent of u, so it controls an entire norm
substitution segment whenever that substitution is later made.

## 2. Both extra scale faces are now removed

At fixed normalized duration the weighted scalar is a strictly
convex quadratic in q. The square-completion proof of A2>0 is
valid on the stated domain. The extra tau=2 face is handled in
[the scale-continuation lemma](MIXED_SMALLER_SHORT_DISPLACEMENT_SCALE_CONTINUATION.md).
A separate reading checked its cubic derivative and its four
Bernstein coefficients. The first coefficient has the displayed
direct bound. For the other two, square completion in the diagonal
and concavity in 1/r_A reduce to two margin endpoints.

The incoming derivative of the completed square is exactly the
difference of two squares in that note. The four lower estimates
for uL-J0 and uL+J0 are positive. Hence the remaining norm endpoint
is u=19/25. All coefficients of the four terminal quartics are
printed. Their constants are positive for alpha-1>=1/10, and the
displayed coefficientwise absorption of both adverse higher powers
is strictly positive. This proves the continuation throughout the
entire interval q<=1/7, with the original incoming norm fixed.

The [zero-scale proof](MIXED_SMALLER_SHORT_DISPLACEMENT_ZERO_SCALE.md)
uses the original ceiling u<=U(r_A) before any looser norm is
inserted. The reviewer checked its derivative in r_A at both
duration endpoints, the exact positive numerator at r_A=1/3, and
the derivative in x including the decreasing endpoint r_0(a,x).
All domain conditions are preserved until x=max(2,a).

At those two edges, the quadratic logarithm bound is valid for
every positive duration parameter y<=1. Its completed square
leaves the two displayed univariate numerators. The first has one
coefficient-sign change and a positive value at one. The second
has only one negative highest coefficient, absorbed by the
preceding term on a-2<=1/6. All 25 coefficients are printed, and
the strict signs also cover the edge endpoints.

It follows that a positive actual weighted residual produces a
positive scalar value at q=min(q_c,1/7), still with the original
incoming norm. The exact duration derivative then leaves precisely
the two tests stated in the reduction. No assertion that a selected
point is a trajectory is used.

## 3. Central beta monotonicity

An independent reading of
[the central-beta lemma](MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_BETA.md)
checked the exact derivative identity, including the cancellation
from the logarithmic derivative. It also checked the explicit
incoming derivative, both diagonal bounds, the outer pairing bound,
and the quintic giving the transported-norm upper bound.

The lower y comparison has the exact endpoint values 2904/1805
and 2623/21660, both positive. The two final derivative margins
are 7/1500 and 1/1200. The proof is therefore accepted on its
stated scalar domain. It does not prove either test negative by
itself; an alpha-boundary comparison and terminal signs are still
needed to use it for exclusion.

## 4. The rational quadratic secant order

The [quadratic-order proof](MIXED_SMALLER_SHORT_RATIONAL_QUADRATIC_ORDER.md)
has also been read independently. The exact continuation supplies
0<=delta<9/20 and all positive denominators at a possible barrier
contact. The strict initial separation and first-contact argument
are valid, including delta=0 and a barrier that would reach alpha=x.

A fresh reconstruction of its rational derivative reproduces all
72 displayed ordinary integer coefficients and all eight endpoint
values. The proof itself uses only those printed identities: each
coefficient polynomial in delta has exactly one transition from
positive to negative coefficients, so its positive endpoint value
implies positivity by the termwise inequality in (8). The former
aggregate claim about 72 Bernstein minima is no longer used.

Thus alpha>=1+c(x)delta+delta^2/(1+4delta) is accepted on
2<=x<=13/6, with strict inequality for positive delta. Its
consequence alpha>1+(c(x)+1/23)delta for delta>=1/19 is an exact
shape restriction, not a transported root or cost condition.

## 5. Remaining scope

These results do not establish x>2, x<13/6, delta<1/19, the extended
Casimir floor, or the physical completion-cost contradiction. The
terminal displacement tests on the central and outer scale faces
must be signed off separately. H-S and the final global audit
remain open until all actual-domain callers are discharged.
