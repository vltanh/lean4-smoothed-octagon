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


## 7. Retain the two actual stationary-control slacks

[MIXED_SMALLER_SHORT_SLACK_RETENTION](MIXED_SMALLER_SHORT_SLACK_RETENTION.md)
is accepted. Both slacks are the actual middle and outer entrance
inequalities of the physical short window, with positive prefactors
and the same primary multiplier. Their derivatives along the first
fixed-root comparison have the displayed signs. The middle derivative
uses only J<Q and tau/T<1, without assuming J>=0. The outer derivative
uses tau*rho_A<r_A and w'<0. Thus both weak inequalities persist to
all three terminal faces; no additional stopping face is needed.

The compact floor identity was independently expanded from the original
middle slack. Writing P_mid=B0^2+rho P1 gives
P1-B_mid^2=-B0^2. After the solved transport substitution, the rho^2*u
coefficient is exactly B0^2-J^2, and the other terms are precisely
the displayed constant and linear coefficients of N0. Hence the
fixed-w expression N_mid=N0+(rho J/lambda)xi is exact.

During the further fixed-w comparison, H_A strictly increases with xi.
N_mid increases when J>=0. For J<0, retaining it requires a possible
additional stop at N_mid=0; the note states that limitation explicitly.
The sufficient condition x<=2alpha implies J>0. None of these
preservation statements supplies an endpoint exclusion or closes H-S.


## 8. Concavity of the forward boundary determinant in physical scale

[MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR](MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md)
is accepted. Eliminating the central incident norm from the displayed
stationarity and transport equations gives J*h_d=B^2*w+v(s+J^2)-s(s+U_t).
The first-forward root equation supplies the second affine identity.
Solving these two equations gives exactly w*=1+A/B+C/B^2 and
h_d=alpha*B+beta, with all four coefficients independent of k.

At B=p^2, the polynomial identity fixes the constant numerator of
the determinant as the negative square
-(alpha*p^2+beta-2vJ)^2. Thus the determinant is a concave quadratic
in X=1/(k-t^2), including the affine exceptional case. This is an
algebraic evaluation; B=p^2 is not assigned a physical interpretation.

The transported next norm has the stated rational form and strictly
positive denominator. For any continuous varying threshold, the eligible
subset of a finite shape interval is compact. Its minimum and maximum
shape values suffice for the concave determinant bound, even if the
subset is disconnected. An interior extreme must saturate the norm
threshold, by continuity. This proves the endpoint reduction without
assuming monotonicity of the eligibility condition.

The actual r>=t bound guarantees 0<eta<1 on the proposed interval.
The piecewise U/Phi floor is continuous and is a proved lower bound
at the original actual next forward switch. Its applicability to the
original b-comparison uses only the unchanged d,r. In the subsequent
shape comparison it is retained by the eligible-subset argument.
At a saturated threshold w*=wPhi exactly, so that face joins the
stronger upper-w endpoint problem. The remaining shape endpoint
signs are not certified by this audit.

## 9. Two elementary bounds in the common low-scale region

[MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION](MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION.md)
is accepted. The root reviewer checked the exact bar-v minus derivative
floor factor and the strictly negative derivative of T(x). If t>=7/20,
the scale lower bound and centre gap force x>8/15, contradicting
t<T(x)<T(8/15)<7/20. Every rational endpoint comparison is displayed.

If x<=3/13, the same centre gap first gives t>41/169. The increasing
quadratic 17t^2-2t-87/169 already equals16/28561>0 at that endpoint,
contradicting k>=17t^2 and the upper centre gap. Hence x>3/13.
Neither proof uses the next-switch type or a cap on an artificial root.
The subsequent residual reduction retains the exact incoming floor;
the two face signs remain open.


## 10. The unit shape face is now excluded

The complete [unit-shape proof](MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md)
is accepted in its [dedicated audit](MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md).
It closes k_min=1 in the reverse lower-shape partition, including ties.
The subsequent complete reverse theorem below also closes the scale face.

The same theorem excludes the d<=c part of the common a<=1/2
domain. The previously proved t<7/20 lies strictly below 13/35,
and d<=c gives x<=1-2t. The centre gap, exact incoming secant and
incoming missing-control floor all meet the theorem's unchanged-coordinate
hypotheses. Shape monotonicity then lowers to k=1 in the correct
direction. No outgoing norm or artificial Casimir condition is used.
The common d>c region and the forward endpoint signs remain open.


## 11. Complete reverse successor and common strict order

The [complete reverse hand exclusion](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
is accepted in its [dedicated audit](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md).
The strengthened order-face scope is justified without the old extra scale
hypothesis. The displayed derivative polynomials increase the corrected
residual through the remaining scale strip, and the polynomial comparison
at its bottom does not transport an incoming norm floor to changed data.
The three cases cover every actual reverse successor, including overlaps
and weak lower-face ties. The alternative reverse upper-shape endpoint is
therefore no longer required by the active hand route.

The same audit accepts the common-order consequence: the scalar theorem
excludes k>=2t+x independently of the successor sign; the strict swapped
secant and original incoming floor then give q<(1+x)/(2t+x). The actual
next margin satisfies r<c, so the physical order is a<=r<c<=b*<d.
This excludes the common d<=c region at every allowed scale. It does not
exclude the remaining forward successor.


## 12. Conditional incident-ceiling Casimir rectangle

The [near-unit ceiling theorem](MIXED_NONSHORT_CEILING_CASIMIR_HAND_BOUND.md)
has an independent internal hand acceptance. The reviewer checked the
explicit radical floor for v, including the rational comparison
6936>6889; the strict positive derivative of the determinant in v; and
the substitution giving the denominator 112896 t^2(k-t^2)^2.
The two-variable polynomial identity was independently expanded and
matches all eighteen displayed terms. Every negative term is absorbed
by one of the three short bounds on 0<=a<=1/5 and 0<=b<=1, leaving
22453418+342984000000a>0. The proof supplies an elementary positive
rational margin, not an executable sign premise.

The conclusion is conditional on 1/3<=t<=2/5 and 1<=k<=51/50.
At the proposed upper shape endpoint the incident ceiling and unchanged
incoming norm have the stated values, so these hypotheses suffice for
its exclusion. This audit does not assert those extra t and k bounds
for every forward successor or every upper shape endpoint. It also
does not supply the other forward endpoint signs. H-N-forward remains
open.


## 13. The common low-scale exclusion is now complete

The [full low-scale hand theorem](MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION.md)
and [high-ratio derivative lemma](MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE.md)
are accepted in their [dedicated audit](MIXED_NONSHORT_LOW_SCALE_HAND_AUDIT.md).
The two lower shape faces cover every hypothetical a<=1/2 window.
The corrected rational quartic is positive by six explicit coefficient
inequalities and two elementary square identities. The displayed derivative
identities, tangent bounds and univariate endpoints supply every coefficient
sign. Moving the rational polynomials to t=1/4 does not move an actual
incoming floor; that floor is used only at the original coordinates.

Thus a>1/2 is now a common hand theorem, independent of the successor sign.
The old common low-a interval cover is not required by the active route.
This closes the formerly open residual signs mentioned in Sections 9--11;
the nonshort forward Casimir endpoints and the short case remain open.


## 14. A uniform corrected cap at the short upper envelope

The [corrected-envelope theorem](MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP.md)
is independently accepted as a necessary-condition reduction.
The common short norm satisfies \(u<5/6\) by the displayed integral
bound for \(V(x)-3/4\). At the fixed actual root, the pairing is
at most \(3\rho_A\); both envelope segments increase E and therefore
decrease the outer pairing. This preserves that bound without
asserting that a comparison endpoint is an actual switch.

The exact derivative ratio simplifies using
\(1-\rho_A=\lambda(1-\rho)\).
The term omitted for its upper bound is strictly negative because
\(\tau E_L\le3\tau\rho_A<3r_A<3/2<2u\).
Together with \(\tau>2,\rho_A<1/7,u<5/6\), this gives
\(245/1728<1/7\), by \(1715<1728\).
Both residual and determinant increase in the directions of the
two original comparisons. Integrating the ratio therefore yields
the correctly directed bound
\(\Gamma_*-R_\tau^*/7\le\Gamma_{\rm actual}\).

The three-case maximizer of \(R_\tau^*\) follows from its displayed
derivative and concavity on \([2,T]\). Replacing its value at the
actual root by its maximum decreases the lower bound. Thus
\(G_{\rm env}\) bounds the original actual determinant and can be
used, together with the retained central lower bound, in the monotone
completion score. The actual positive duration also supplies \(M>0\).
The geometry and equal-secant norm remain fixed, so \(t,v,\tau\)
are removed from this new necessary test. No upper cap or lower
bound is asserted for an artificial covector.

The remaining fixed-geometry sign is open. This audit accepts the
uniform correction and its original-period application, not H-S.

## 15. Affine scale monotonicity of the short residual

The [normalized-root scale comparison](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md)
is independently accepted in its stated scalar scope.
Substituting \(q=\rho_A,p=\tau q\) gives exactly the quadratic norm,
affine pairing and affine residual in (2)--(4) of that note.

For an independent check of the decisive slope identity, substitute
\(\delta=n+(1-B_0)/p\) directly in \(pL\).
The coefficient of \(uB_0^2\) is one. The coefficient of \(pB_0\)
reduces to
\((x-1+Z(1+\alpha^{-2}))/S\), while the remaining quadratic
coefficient in p is \(1-Z/\alpha^2\).
These are precisely the three terms in the displayed identity (5).
The order gives \(B_0/p\ge(x-1)/\alpha>0\);
\(u\ge3/4\) gives \(Z\le(x-1)^2/4\); and \(p\le r_A<1/2\)
gives \(U(p)\ge U(r_A)\ge u\).
The resulting strict lower bound on L has the correct direction.

Raising q at fixed p therefore retains the positive residual up
to one of the three explicit scale endpoints. On \(D\le1+x\),
the two exact norm derivatives also preserve the actual floor
through the original envelope comparison. Its further retention
uses the largest point of a compact closed eligible set; no
connectedness or monotonicity of that set is assumed.
If that largest point is an interior floor equality, the
\(\tau\)-derivative at \(w_*=3/4\) is nonpositive and lowering
\(\tau\) to two is legitimate.

Only the residual and the explicitly justified norm floor move
with scale. The physical score and the corrected cap depend on
scale, so neither is transferred. The source states this limitation
and leaves the endpoint signs and the \(D>1+x\) branch open.


## 16. Quantitative swapped secants

The [quantitative swap theorem](MIXED_NONSHORT_QUANTITATIVE_SWAP_BOUND.md)
is independently accepted. The reviewer re-derived both exact logarithm
expressions for the secant difference, checked the positive denominators,
and independently expanded the entire 23-term numerator.
Its grouping in powers of j agrees exactly with (5) of the source.

Every absorption in the lower bound (6) follows from
\(0<j<h\le1/2\). The constant and linear groups have the stated
positive lower bounds; the quadratic group absorbs the negative
part of the cubic, leaving \(67j^3/16\); and the remaining negative
tail is absorbed by \(20hj^3\), leaving \(j^4/8\).
The strict logarithm inequalities therefore give the strict
swapped-secant comparison.

For the actual application, the original derivative floor gives
\(t<T(x)\), hence \(x<1\) and \(4t+x<2\) when \(t\ge1/4\).
This supplies exactly \(j<h\). The incoming floor is the original
secant with first argument \(W/q-p\in(0,c)\). Its strict decrease in
that argument forces \(W/q-p>t+p-c\), proving
\(q<W/(4t+2x-1)\). No floor or cap is moved to a changed geometry.
A second independent internal reviewer also accepted the complete
lemma and this application.

## 17. Forward low-ratio reduction to one unit-shape sign

The [forward ratio reduction](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md)
is independently accepted in its stated scope.
Its first conclusion \(t>1/4\) is a completed common hand theorem:
the already proved unit-face argument needs no low-scale assumption
once the common strict order supplies \(x>1-2t\).
The earlier low-scale assumption was used only for its other face.

The reviewer reconstructed the affine root derivative \(N_u\),
the next-norm derivative, and identity (4) from the original transport.
The positive factor \(C_*\) and the combination
\(F=6N+C_*(3/4-\mathcal T_*)\) have the stated strict necessary
sign. Their quadratic coefficient in k is negative.
The elementary bounds on \(Je^2\) and \(WD/x\) justify both
substitution directions, including the case where the product in
\(F_v\) is negative.

The effective norm is below its incident ceiling on the full
enlarged rectangle. The reviewer checked the floor difference (14),
the exact factor in (15), its lower-t substitution, and
\(\rho\le13/8<2\). The source correctly uses a weak intermediate
inequality when \(v_3=g\); the final ceiling remains strict.

Differentiation in k has the same justified v/log signs.
Independent expansion of the original residual and transported norm
reproduces the entire cubic (18), including its prefactor.
The coefficient bounds in (19), together with \(y\le1/2\), prove
that this derivative is positive at \(k=o\), and concavity gives
the same direction throughout the shape interval.
Thus lowering k to one retains the necessary negative rational
residual. Only the polynomial inequality is changed; the incoming
floor was used at the original coordinates.

The quantitative swap theorem gives the final closed simplex (21).
Its remaining rational sign is explicitly open. This review does
not assert \(t>1/3\), next-norm exclusion or forward-case completion.


## 18. The corrected short cap also moves with scale

The [corrected-cap scale theorem](MIXED_SMALLER_SHORT_CORRECTED_CAP_SCALE.md)
is independently accepted. Lowering beta preserves the p-domain and
decreases \(B_0\), hence the slope L; the norm dependence is affine.
At the upper norm endpoint, all three elementary identities giving
\(4UA_2-A_3^2=3\) are exact, and the factored discriminant has the
correct nonpositive sign. Its only possible zero when \(\alpha=x\)
lies beyond \(p\le1/2\), so strict positivity persists in that closure.

At the lower norm endpoint, the reviewer reconstructed the cleared
expression directly from \(L=pA_2+p^{-1}-1-A_3\).
Substituting \(p=\alpha/(\alpha+x+k)\) gives exactly identity (5):
all twelve terms of P and all twenty-two terms of Q match the displayed
polynomials. Their positive terms prove strictness because \(x>1\).
This completes the slope inequality without a runtime sign premise.

The quadratic formula for \(16\Gamma_*\), its scale derivative and
the normalization \(s=q/(\alpha^2(1-q))\) are consistent.
The slope bound gives the stated constants \(49/384<1/7\) and
\(-41/2688\) for the corrected derivative.
Consequently the residual increases while the corrected cap expression
decreases to each scale endpoint. The extra \(w_*=3/4,\tau=2\)
stop also preserves both scalar tests: lowering tau there increases
the residual at fixed envelope determinant.

The comparison remains a numerical lower bound on the original actual
Casimir. It does not assert a cap on an artificial trajectory, and
it does not move the physical completion score. The latter comparison
or the remaining endpoint signs are still required to close H-S.

## 19. Conditional monotonicity of the forward Casimir

The [conditional forward lemma](MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY.md)
has independent hand acceptance. The additional \(t\ge1/3\) and
\(\chi=pq/W\ge4/7\) remain explicit hypotheses.

The reviewer checked the normalization of the first-event diagonal
against the physical stationarity equation; (4) is the same original
squared Casimir. The displayed turn-floor polynomial and its value
\(83/72\) prove \(j<1/4\). The bounds
\(s-p^2>7/144\), \(15/11\le A<2\), and \(A/\chi>2\)
follow with the stated directions.

The original incoming floor gives the lower bound (10) on L.
The derivative expression then decreases in v; substituting \(v=3/4\)
has the correct upper-bound direction. The remaining function decreases
in chi and is convex in A. Both exact endpoint fractions are correct,
giving the derivative margin \(135/108416\).
The original next forward switch has the strict norm floor from
HAND_PROOF_REFINEMENTS, Section 4, equation (13), so the comparison
from the actual w to \(w_{3/4}\) is strict.

This establishes a conditional route that would subsume the separate
lower-Casimir endpoint. It does not prove its additional ratio
hypotheses or the upper-endpoint lower bound. H-N-forward remains open.
