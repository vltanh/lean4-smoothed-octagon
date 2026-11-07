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

Consequently only the central-duration endpoint ell((1+x)^2)<0
remains for a separate v-floor face. This audit does not exclude that
last face, or any other short root-comparison face.

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
