# Independent review of the short-diagonal pairing sign

Date: 2026-11-07. Internal mathematical review by a worker other than
the author. No Lean, Lake, typechecking, CI, interval execution or
numerical sign check is a premise of this review.

## Accepted statement

The proof in
[MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md)
establishes
\[
 D\ge0\implies E_L>0
\]
on its entire stated exact equal-secant domain, including the weak
central duration endpoint, equal-centre bridge endpoint, and D=0.
More precisely it proves E<0 for x>=12/5, and D>0 with E_L>0 for
1<x<=12/5. Thus every nonpositive-pairing point in the retained domain
must have x>12/5 and D<0.

## Domain and comparison checks

1. Raising v to U(t) increases E. The subsequent decrease in t to
   rho/r increases E because the derivative along that ceiling is
   2-1/t<0. The resulting envelope is exactly
   S(u-1)+1/S+rho(2S-1). These comparisons require only the central
   upper norm and the interval rho/r<=t<=r, both retained by the
   first short-root comparison.
2. The bound on the equal-centre secant follows by integrating the
   explicit nonnegative square and using s+x>=1+x. No certificate
   from the later parts of the historical short-bridge note enters.
3. The equal-secant continuation in Section 1 of that note supplies
   the complete beta segment, u_beta<0, alpha_beta>alpha/beta and
   beta<=alpha*x. The new proof uses this analytic section only.
   The derivative bound D_beta>2/x+4-2x stays strictly positive
   through x=12/5, where its lower bound is 1/30.
4. On the small-x segment D>=D_0>0 and D<=S^2. Consequently
   S-2rho D>=S-2>0, which is the needed coefficient sign in the
   derivative of E_*-2rho D u. Both summands of that derivative are
   strictly negative. The comparison therefore reaches beta=x,
   alpha=1 with the correct direction and at unchanged physical scale.
5. At that endpoint the expression is affine in rho. Its rho=0
   endpoint is strictly negative. At rho=S^-2 the coefficient of the
   secant is positive, so inserting the upper secant bound has the
   stated direction. The displayed quintic has positive sign because
   its quotient by x^4 decreases on [1,12/5] and its upper-endpoint
   value is 41817/3125>0. All denominators are positive.
6. On x>=12/5 the displayed cubic increases strictly and equals
   53/125>0 at the endpoint, so E<0. For D>=0, u>0 then makes
   2rho D u-E>0, including D=0. Multiplication by positive lambda
   gives the strict pairing sign.

## Actual-period scope and remaining work

The geometry, equal secants, incoming norm and physical scale remain
fixed during the first root comparison. Its central upper norm and
duration interval are precisely the hypotheses used above. Therefore
the lemma applies to those comparison endpoints, including the
outer-norm face w=3/4. It makes the existing positive-pairing deformation
available throughout D>=0 without the earlier outer-margin cutoff.

No lower Casimir bound is assigned to an artificial covector, and no
cost monotonicity is inferred from the pairing sign. The D<0 branch
and the three terminal cost/root face exclusions remain open. This
review accepts the uniform sign and its interface only; it does not
close H-S or the full hand proof.
