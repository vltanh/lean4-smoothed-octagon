# Review of the short order, scale, root and angle lemmas

Date: 2026-11-08 UTC. These hand lemmas are accepted with the
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

## 3. The compact incoming-norm majorant

The [incoming-norm theorem](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
is accepted for every 1<x<=beta. Its proof uses the positive integral
for the original secant, split at s=x. The displayed expression for
V(x)-3/4 follows by the change z=(x-1)/(x+1). Clearing the positive
factor (1+z)/(2z) gives exactly the stated logarithm inequality.

Differentiating its rational comparator gives
z^3(32-33z)/[2(1+z)^2(24+11z)^2]. Therefore its logarithmic error
increases and then decreases, so the two endpoint values control its
minimum on [0,1]. The lower endpoint is zero. The upper endpoint is
strictly positive because the three-term positive-integral bound for
log 2 exceeds 97/140 by exactly 1/6804. The endpoint fractions and
derivative identity were reconstructed independently.

On the tail s>=x, the inequality (s+x)^2>=4x^2 has the correct
direction for an upper bound on the positive integral. Its integral
is (beta-x)^3/(48x^2), including the case beta=x. Combining the two
pieces proves the full majorant. No second-secant equality, scale cap,
root condition or physical cost comparison is assumed or transported.

## 4. The backward root comparison for large x

The [backward-root theorem](MIXED_SMALLER_SHORT_BACKWARD_ROOT_REDUCTION.md)
is accepted on its stated x>=12/5 domain. The hypothetical D>=Q
inequality gives both alpha>=143/60 and beta<=29/12, using only the
actual short ordering. Hence the second secant has excess at most
1/(4*143^2), while integrating the first secant only on [1,3/2]
gives excess at least 27/5746. These are incompatible. Thus D<Q,
and the unchanged actual root parameter obeys 1-tau*d>0 for either
sign of D.

The integrating-factor argument for nu is in the backward direction:
nu'-A(t)nu=2t-1<0 implies positivity at every earlier time. Together
with 1-tau*d>0, the existing derivative identities then show that both
v and w increase while t decreases. Their lower floors and the central
upper norm are therefore retained down to t0. Smoothness on the whole
compact interval follows from the separately proved positive B(t).

The affine root coefficient is lambda*B0/t0, and the ratio of the
outer-norm coefficient to it is exactly a0/B0. Solving the affine
equation therefore gives both formulas (9) and all three necessary
inequalities (10). In particular the middle inequality must be kept
in its complete form when D>S. No outer descending ceiling or upper
Casimir cap is asserted at this new endpoint.

## 5. The small-shape upper order

The [upper-order theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md)
is accepted conditional on 1<x<=15/7 and delta<=1/19. The second
secant is the ordinary average of g on [p,q], and its fourth derivative
is positive on this interval. Simpson's remainder therefore gives the
claimed strict upper bound. The gap ratio increases with the average,
so eta/xi<N/Z has the correct direction and positive denominator.

At contact with alpha=1+3delta, p=(3-2q)/x and the barrier derivative
is p+2q/x. The numerator in the derivative comparison has exactly
the factorization (7) and the seven grouped terms (8). An independent
expansion verifies this identity. The contact condition p<q gives
h<z/(z+3), which is used only in the two negative-term bounds.

The three discarded high-order brackets are positive on [0,8/7].
The remaining negative terms are bounded in the stated directions,
including the coarse h^6<=h^2 estimate. Their sum leaves the concave
cubic J(z). Its endpoint values are exactly 100/3 and 61028/5145,
both positive. Thus the derivative comparison is strict at every
possible contact, including the initial one. The first-contact
argument proves the upper order on the whole exact branch. It does
not establish either small-shape hypothesis.

## 6. The scale angle barrier

The [angle-barrier theorem](MIXED_SMALLER_SHORT_SCALE_ANGLE_BARRIER.md)
is accepted with its explicit x<=12/5 and two scale-cap hypotheses.
The weighted reciprocal bound s<=4/(3X+6alpha^2) follows from those
two caps. Clearing its positive denominators gives the polynomial G.
Its negative cubic coefficient and its negative second derivative at
beta=x prove concavity on the entire permitted beta interval.

The two displayed degree-four positive-basis identities were
independently reconstructed from G. All ten coefficients and all
three rational values at x=12/5 agree with the printed formulas.
The three one-sign-change arguments and the remaining positive
coefficients establish both endpoint signs. Hence the negative
shear bound holds throughout the full enlarged scale interval.

The incoming norm bound follows by splitting its positive integral
at x: the first mean is at most R^2/12 and the tail mean at most
R^2/16. Its resulting deficit bounds have the correct directions.
They imply delta<(5/17)R<(5/16)R<theta1, and the separate lower-row
angle estimate gives psi<pi/6. Together with delta<1/6, these facts
exclude the upper critical angle and clipping everywhere on the
stated scale interval.

Finally the derivative reduction in Section 4 squares two positive
sides: JK-c=c-3(b1+b2)/2>0. Dividing out K^2+H^2 leaves precisely
the displayed quadratic in H^2. The three estimates (22) give its
strict negative bound -217383(b1+b2)/1323620, as verified by direct
rational addition. This accepts the conditional decreasing-score
claim. The root-implied condition -hR>=3A, h<0 and the actual bound
x<=12/5 are still open hypotheses for that application.

The strengthened threshold 5A/2 in Section 5 is accepted as well.
At fixed H,A, lowering b1 to its proved lower bound increases the
normalized derivative polynomial, while the associated b2 remains
nonnegative by (27). The derivative estimate uses the exact strict
comparison 14553/14656<1 for its only positive contribution. Raising
A to (2/5)HR then increases the expression. After this substitution
its linear and quadratic coefficients in H are positive, so the
stated upper H endpoint is legitimate. Convexity in c leaves its two
endpoints. Independent reconstruction verifies both degree-ten
identities and both negative rational values at R=7/17. Their
positive nonconstant coefficients prove the signs on the full
interval. The stronger conclusion remains conditional on the
unproved actual lower-shear condition; no root implication is claimed.

## 7. Scale endpoints for the combined root and norm-floor expression

The [combined scale theorem](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md)
is accepted on its complete stated enlarged domain. Its quadratic
formula in q is exact. When A2>=0, convexity gives the two scale
endpoints directly. The remaining case A2<0 is treated separately;
no global positivity of A2 is assumed.

The coefficient identities imply D>0 in that case. The elementary
order argument then gives (x-1)^2<2alpha^2. The independently
reconstructed discriminant identity (9) proves that A2<0 requires
S>5 and a<2/9. Thus all later enlargements to the rectangle (13)
are valid. The negative A2 reverses the q<=p/2 comparison in exactly
the direction printed in (11).

Completing the square in the signed diagonal gives (12). Its
quadratic coefficient in a, and the derivative at a=0, have the
claimed signs. The bound F_p<=-1/3 is therefore uniform, so p=1/2
is the required lower endpoint for F. Concavity in a then leaves
two endpoints. At a=0, the independent H,u rectangle gives exactly
12013/83200. At a=2/9, the affine-over-u square proves concavity
in u without a coefficient table. Direct reconstruction verifies
both quartic formulas and their four displayed rational endpoint
values. Each exceeds 1/10, proving the claimed strict derivative
bound and the exhaustive scale alternative. Only the combined scalar
test is transported.

## 8. The large-ratio floor-weighted envelope and its zero-scale sign

The [floor-weighted theorem](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md)
is accepted on 12/5<=x<=9. At the actual outer root, G is strictly
positive because the original outgoing norm is strictly above 3/4.
The positive B_(tau+1/2) identity proves that the two original
envelope motions increase G. The proof includes D>S: T>=2 controls
the extra half in tau+1/2, and 4Q-5(D-S)>0 follows directly from
the ordered margins. No separate floor is asserted after this motion.

The equal-secant integral argument proves alpha/beta<3/4. Its
convex-tangent weighted mean, derivative and rational endpoint were
checked independently. On the resulting enlarged ordered shape
domain, D/Q decreases in beta and has the stated two alpha cases.
Their endpoint comparison proves the uniform bound (9).

The coefficient of the incoming norm in G is strictly positive.
For D<0 the regrouped terms have the displayed signs. For D>=0,
the inequality tau*d<1 permits the stated lower bound, and the
two elementary x ranges bound its subtraction below 1/r_A.
Consequently the rational incoming majorant can be used in G once
the shape, scale and root parameter are fixed. This substitution
does not preserve an independent incident-norm ceiling automatically.

At q=0 the logarithm tangent gives an affine majorant in p. Its
first endpoint is bounded by -541/2380. At the second endpoint,
E0<0 gives the correct direction when replacing 1-D/Q by its lower
bound. Both later substitutions also increase the expression.
Independent reconstruction verifies the derivative numerator N,
the final polynomial P, and both positive expansions in z=5x-12.
Thus the entire zero-scale face is strictly negative. The three
positive-scale faces remain explicit, unproved sign obligations.

## 9. Global upper bounds for the exact short shape

The [global upper-order theorem](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md)
is accepted for every x>1, with its stronger coefficient on x<=5.
The change of variables gives precisely the decreasing weight
2/(1+z)^2. Its covariance with increasing z^2 is strictly negative,
so the weighted-average upper bound (6) has the claimed strict
direction. Subtracting the two endpoint values and taking their
ratio gives (7), with positive numerator and denominator.

At the affine barrier, the contact formulas and q interval follow
by clearing x>0. The derivative comparison has positive denominator
Z(x-q). Both complete quartic positive-basis identities were
reconstructed independently from this comparison. All ten factored
coefficients agree with the displayed lists. The sole coefficient
requiring a range restriction is positive for x<=5 by the explicit
877x^2 bound. Thus the derivative inequality is strict at every
possible contact, including the initial contact.

The exact branch consequently stays below the corresponding barrier.
If that barrier reaches x, the original strict alpha<x condition
already keeps the branch below it. This covers the whole ordered
continuation and proves both upper bounds without a scale or root
hypothesis. The resulting rational beta strip is a restriction on
the original exact short shape.
