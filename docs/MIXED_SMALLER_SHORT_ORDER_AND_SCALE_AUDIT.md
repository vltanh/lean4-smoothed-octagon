# Review of the strengthened short order and negative-diagonal scale lemma

Date: 2026-11-08 UTC. These two hand lemmas are accepted with the
precise scopes below. They are additional reductions for H-S, which
remains open.

## 1. The stronger exact short order

The [strong-order theorem](MIXED_SMALLER_SHORT_STRONG_ORDER.md) is
accepted on the complete exact equal-secant domain with 1<x<=9.
Its continuation input is the integral branch argument in Sections
1--2 of the central short-bridge note, not that note's later
polynomial certificate.

The derivative formula uses p=alpha/beta and q=x/beta at the same
actual branch point. The gap estimate eta>eta_0, together with
eta+xi=g(p)-g(q), has the correct direction in
eta/xi>N/(W-N). The denominator is positive on nondegenerate
contacts. At the possible limiting endpoint p=q, direct substitution
gives W-N=N=6(1-p)(1+p)^2>0, consistent with the polynomial
endpoint calculation.

The affine barrier's derivative is p+kq with
k=4(x+1)/(7x+1). Its contact condition p<=q gives exactly the
stated q_min. The cleared numerator has the quartic factorization
printed in the proof. The factor b-4a is positive for x>1, so
P_qqq>0 on q<=1. The upper bound for P_qq(1) follows from
the convex quadratic's maximum 1269 on [1,9], leaving the
strict negative margin -423. Thus the quartic is concave on the
whole contact interval. Both factored endpoint values are positive.

At q=1 the factor 1-q vanishes, giving a weak rational barrier
inequality. The original strict gap estimate still gives a strictly
larger actual derivative there. It does so at every later actual
contact as well, since p<q on the exact positive bridge. The branch
therefore starts strictly above the barrier and cannot cross it.
The possibility that the barrier reaches alpha=x is also covered
by that first-contact argument. This proves the claimed strictness
for beta>x and the equality at beta=x.

An independent algebraic reconstruction verifies the cleared quartic
identity, the b-4a factorization, P_qq(1), and both endpoint
factorizations. All signs follow from the displayed derivatives,
factorizations and endpoint bounds. No executable sign premise is used.

## 2. The tau=2 scale comparison

The [negative-diagonal scale theorem](MIXED_SMALLER_SHORT_NEGATIVE_DIAGONAL_SCALE.md)
has a separate independent review recorded in its final section.
It proves (R_2^*)'>0 for fixed shape and incoming norm on the full
closed enlarged domain used there. The review checked both derivative
identities, all intermediate sign bounds, both successive concavity
reductions and their exact positive endpoint constants.

The domain uses the actual x<9 and u<=13/16 bounds. The accepted
pairing theorem excludes D<=0 when x<=12/5, so the enlargement
17/5<=S<=10 is valid on this branch. The improved scale bound
q=rho_A<1/7 applies at the actual outer reverse centre, as established
in the [reverse-centre scope audit](HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md).

The residual theorem itself has no q<=r_A/2 hypothesis. It therefore
allows a numerical upper comparison beyond that value to the smaller
of the central-duration and outer-scale bounds, without claiming a
physical reverse arc at the changed point. Any subsequent logarithm
estimate must cover the resulting argument, which can exceed one.
This comparison transports the residual alone. It supplies no new
outgoing norm floor, corrected cap or physical-cost inequality.

The final negative-diagonal residual sign and the remaining short
completion-cost signs remain separate obligations.
