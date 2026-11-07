# Independent hand review of the remaining endpoint reductions

Date: 2026-11-07 UTC. Independent internal mathematical review.

The reductions below are accepted with their stated domains. Their
remaining endpoint signs are open; this audit does not close H-N or H-S.

## 1. Reverse secant line and the single upper shape endpoint

[MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON](MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON.md)
is accepted. At r=sqrt(ad), two positive logarithm-series terms give the
displayed strict lower bound for the weighted secant deficit. Its proved
strict concavity and limiting derivative give the affine extension to
all larger r. Both intercept differences factor as stated; replacing
sqrt(ad) by the explicit rational lower bound has the correct direction.

The solved boundary norm has its already accepted rational dependence
on the shape parameter. Multiplying its difference from the new secant
upper bound by B^2 gives exactly LB+M. The coefficient of v in L is
negative, as is its logarithm coefficient. Lowering both to the stated
actual derivative floor and elementary logarithm lower bound therefore
gives an upper bound for L. The displayed three short polynomials prove
that upper bound strictly negative for the entire stated t,x,q domain.

Thus the comparison gap strictly decreases as k increases. The actual
reverse turn condition r>=sqrt(tp) survives that increase. At the upper
root endpoint its gap remains negative, giving the single necessary
endpoint inequality. No actual norm floor or physical Casimir cap is
assigned to the artificial root. The sign that would exclude this final
endpoint is not supplied by the reduction.

### Exact secant and sharper turn-length comparison

[MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON](MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON.md)
is also accepted. Extending the secant to zero and using three positive
atanh terms proves d<7c/3, and the reverse turn similarly gives d<7r/3.
The pointwise expression for d minus the integrand of J' has a concave
quadratic bracket, positive at both endpoints. Hence J'<d on the
required unchanged-coordinate range. The exact weighted root-gap
derivative is bounded above by the displayed strictly negative
three-coefficient expression. Thus the upper shape endpoint retains
the exact secant, improving the earlier rational-line necessary bound.
Its final exclusion sign remains open.

### Order forced by the two actual exterior floors

[MIXED_NONSHORT_REVERSE_ORDER_BOUND](MIXED_NONSHORT_REVERSE_ORDER_BOUND.md)
is accepted. The pointwise swapped-secant identity has positive factors
throughout the integration interior. Both actual missing-control floors
have the stated secant forms, and starting-point monotonicity applies
on the required positive intervals. If d>b*, the incoming comparison
forces r<c<d, and the outgoing comparison then forces A0>a, contrary
to A0<a. The equality argument and actual positive-duration strictness
are both valid. Therefore actual reverse-next data have d<b*, and
the enlarged shape domain may use k>=2t+x. No outgoing floor is
assigned to the artificial root. The three lower shape faces are necessary-domain reductions. The order
face is now excluded by the following hand argument; the other two
remain open.

### Complete exclusion of the reverse order face

[MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION](MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md)
is accepted. On k=2t+x, the actual incoming floor and the swapped-secant
order restrict the first-event factor to 1<q<=W/k. The exact residual is
concave on this interval, since its moving endpoint lies between t and
c<=p. Its value at q=1 is strictly positive by two positive atanh terms,
three completed squares and the already proved duration bound.

At q=W/k, the hand ratio and scale bounds imply x>1/4. The substitutions
h=1-2t and s=k-1 give the stated rectangle and h+s>1/4. The residual
decreases in both the incoming norm and log q, so the displayed rational
upper bounds give a strict lower residual comparison. Its eight explicit
coefficient polynomials contain only four negative higher terms; the two
shown absorptions remove them. The remaining constant and linear terms
are positive by an increasing polynomial for h>=1/4 and one concave
polynomial with positive rational endpoint values for 1/5<=h<=1/4.
This proves the entire face impossible, including lower-bound ties.
The k=1 and k=(29/4)t^2 faces still require separate exclusions.

## 2. Shape monotonicity of the retained central lower bound

Section 5 of
[MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md)
is accepted independently of its earlier sections. The derivative
numerator H has the stated form. When E<=0, the strictly positive
quantity C+E proves H>0 without requiring G itself to be positive.
When E>0, raising each norm lowers H and preserves that sign of E.
The norm-raised expression decreases with rho; its terminal value has
the explicit strictly positive factor (1-t^2)^2(1-2t)^2/t^2.

Hence the retained lower-bound expression decreases with k. For actual
a>=3/4, its necessary upper cap may legitimately be retained at a larger
shape endpoint. This monotonicity acts on the explicit lower comparison,
with the exact incoming secant held fixed. It does not justify replacing
that secant by an upper approximation inside the cap or transferring the
actual Casimir cap to the artificial PMP root.

## 3. Keep actual lower-Casimir information in the short cost score

The added effective-kappa formulas in
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
are accepted. The artificial determinant decreases, while the actual
period has kappa>9/8. The maximum of these lower comparisons is still
at most the original actual kappa. Applying the proved monotonicity of
the relaxed score gives the stated necessary cost inequality. No new
stopping face or lower bound on the artificial determinant is asserted.

The additional retained bound from the fixed incoming norm is accepted.
The explicit turn floor permits lowering the actual opposite norm to m;
Gamma increases with that norm throughout the relevant segment, by
E<=3rho and rho<=rt. With the norm fixed at m, the pairing increases
with the opposite ratio. Its squared magnitude is bounded by the larger
endpoint square, without an assumption about its sign. All resulting
data are fixed during root deformation, so G_ret remains a lower bound
on the actual determinant, supplies a necessary cap, and can be used in
the maximum defining the effective cost parameter. These statements
make no lower-bound assertion about the artificial determinant.

## 4. The remaining opposite-floor localization

Sections 6--7 of
[MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
are accepted. For positive signed diagonal, the retained outer pairing
ceiling and reverse scale give E>-1/2. Raising the scalar opposite ratio
and central scale gives the displayed upper comparison B(1+x), whose
derivative and rational endpoint value prove x<31/10.

The function phi(tau)=3tau/4-f(tau) strictly decreases beyond two.
Replacing tau by two therefore lowers L_tau because its coefficient
is negative. The resulting ell expression follows by multiplying by
(q+sigma)^2. Its derivative is positive on q+sigma>=2Q, by the fixed
incident ceiling u<=U(1/T_B). Each lower bound in q_min is justified by
one preserved actual constraint, and the entire scalar comparison
interval stays in this derivative domain. Thus ell(q_min)<0 is a valid
necessary alternative on the initial three endpoint subregions.

Section 8 excludes the outer-scale endpoint for alpha>=4/3. Its incoming
norm bound is strictly below 31/40; convexity of the rational logarithm
comparison gives B<87/140 on the permitted T_B interval. The completed
square and increasing alpha term give the positive margin 54479/76800.

Section 9 removes the T=2 endpoint entirely. Its sharper incoming norm
bound follows from the displayed positive logarithm derivative. Jensen's
inequality applied to the convex other secant gives two successive ratio
improvements. The convex D quadratic is strictly negative at both
endpoints after each required bootstrap. Thus T_B<7/2 is proved on the
entire remaining positive-diagonal floor domain. The root-interval entry
in q_min is redundant.

Section 10 excludes the remaining outer-scale region. Scale dominance
gives x<5/2 and u<49/64. The maximum of the resulting logarithmic bracket
occurs at T_B=8/3; the two-term atanh estimate yields B<67/140.
Completion of one square suffices for alpha>=10/9. On [1,10/9], the
short order and convex tangent bound on sqrt(6alpha^2+1) give the stated
decreasing lower bound delta_0. It stays above the minimum of the
quadratic in delta, so substitution has the correct direction. The
remaining degree-six identity has nonnegative higher terms and one
explicitly positive completed square. All these steps are hand sign
arguments; an executable sign check is not a premise.

Section 11 now excludes that last central-duration endpoint as well.
The coarse logarithm bound and completed square first reduce alpha
below 9/8; the positive-diagonal inequality then forces x<8/3.
The sharper norm and bracket estimates reduce alpha below 10/9.
At fixed alpha, the lower diagonal comparison delta_*(K) decreases
with K, while H=delta_*-4b/3 strictly increases. Its second derivative
has the stated positive lower comparison, and the initial derivative
has the strict rational margin 809/82215.

The quadratic minimum over delta>=max(0,delta_*) has exactly the two
displayed branches. When H>=0 it is nonnegative. When H<0, each branch
strictly increases with K, their derivatives agree at the transition,
and the initial value is positive by the already accepted Section 10
identity. The comparison at K=7 is only a scalar calculation; no
trajectory or original cap is assigned there.

Thus both endpoints contradict the necessary ell<0. The positive-D
opposite-norm floor is impossible, and the nonpositive-D part is
impossible or already on w=3/4. The separate v=3/4 stopping face is
redundant. Exactly three other short comparison faces remain:
t=r, v=U(t), and w=3/4. This review does not exclude those faces.

## 5. Shear, physical cost and every possible scale minimum

[MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md)
is accepted. The rotated lower row follows from the original physical
P,F,Q interface; its squared norm has the stated ratio of incident
ceilings. The determinant-one upper-row decomposition leaves a unique
real shear. Its affine dependence on rho/(1-rho) and the affine cost
identity follow from the displayed row multiplication and the actual
equal-secant physical cost. The equal-secant premise is retained.

The circle's tangent equation gives the stated half-angle formula and
inverse, with the correct continuous upper-angle branch. Differentiating
the completion expression gives its quadratic critical equation. The
discriminant cancels to the product of the two incident norm deficits.
The root locations and sign changes identify only the larger critical
angle as a possible local minimum. Its alternative formula as a sum of
two arcsines follows from the cosine addition identity.

The audit checked the zero-deficit case A=0 separately: the nonnegative
shear part is linear and its joining point h=0 is retained. The clipping
point at total angle pi/3 is also retained. Consequently the listed scale
endpoints, clipping point and possible interior minimum exhaust the
minimization on each closed scale interval.

The curvature changes sign at the displayed shear, so a universal
endpoint-only minimum claim would be unjustified. The note states the
additional explicit inequality needed for that simplification. Neither
it nor a uniform lower bound for every listed candidate is claimed
proved in this review.


## 6. Further comparison on the fixed outer-norm face

[MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION](MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
is accepted with its explicit E_L>=0 hypothesis. At fixed short geometry,
the outer root equation makes tau decrease as the pairing xi increases.
Solving the two-turn transport equations gives the displayed affine
E(xi), v(xi), and implicit differentiation gives the stated dt/dxi.
The comparison continues to a listed endpoint by compactness and the
nonvanishing central derivative away from the ceiling. The accepted
opposite-floor theorem rules out an additional v=3/4 stop.

The outer pairing ceiling gives 0<=xi<3/7, so the determinant stays
strictly positive and decreases with xi. The physical matrix and cost
stay fixed, and the relaxed completion score has the needed monotonicity.
The comparison therefore preserves its necessary upper cap and cost
inequality without assigning any actual lower Casimir bound to the
artificial determinant.

The retained actual outgoing-turn floor is also accepted. At a fixed
outer root, lowering the actual outgoing norm to Phi(1-1/tau) strictly
lowers the central Casimir because its norm derivative is positive.
Along the subsequent nonnegative-pairing comparison, the displayed
derivative proves G_out increases with tau. Hence tau decreasing retains
both the actual cap and the contribution of G_out to the effective
cost parameter. These are statements about the unchanged actual period.

Finally, lowering the opposite outer ratio to its zero-duration value
and then the fixed incoming norm to 3/4 gives
E_L>1+rho_A-1/(8rho_A). The right side increases with rho_A, and
A>=5/7 implies the explicit positive margin 359/44200. Thus any part
outside the nonnegative-pairing comparison has A<5/7. The negative-pairing
part and the terminal cost signs remain open; this result does not
close H-S.
