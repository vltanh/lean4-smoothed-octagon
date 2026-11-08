# Independent review of the three small-gap hand lemmas

Date: 2026-11-08 UTC. Internal independent mathematical review. The
accepted statements below are restricted to their stated domains.
They do not establish the actual bounds \(t\ge1/3\), \(j\le1/30\).

No Lean compilation, Lake, typechecking, CI or interval cover was used.
Exact algebraic reconstruction was used as a transcription safeguard;
the proof premises are the displayed identities and sign arguments.

## 1. Positive-integral secant bound

The [positive-integral note](MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND.md)
is accepted for every \(x>0\), \(0<t<1\).

The four weighted moments are respectively \(1/3,1/12,1/30,1/60\).
Substituting the displayed quadratic P verifies both orthogonality
equalities directly. With \(a=-1/x\), division by \(1+xu=x(u-a)\)
and \(P(u)-P(a)=(u-a)(u+a-2/3)\) gives the two integral identities
with the signs stated in that note. In particular the polynomial
part in its equation (7) is \(-1/(3x^2)-5/(36x)\), so the rational
remainder in equation (8) has the stated positive sign.

The denominator Q and \(P(a)=Q/x^2\) are positive. The remaining
integral of \((1-u)^2P(u)^2/(1+xu)\) is strictly positive, since
its integrand is nonnegative and not identically zero. Multiplication
by \(-x\) reverses the inequality in precisely the direction needed
for \(T_0<T_G\). The coefficient \(cx/W^2\) relating v to T_0
is positive. Thus the incoming-norm ceiling is valid at the original
coordinates. The weaker polynomial ceiling follows from the same
integral by a separate finite division identity. Neither ceiling
asserts a new admissible physical trajectory.

## 2. The conditional chi bound

The [small-gap chi theorem](MIXED_NONSHORT_SMALL_GAP_CHI_BOUND.md)
is accepted under its explicit hypotheses. The common inequalities
\(k>29t^2/4\) and \(k<1+j\) indeed imply \(t<19/50\), so the
closed h interval \([6/25,1/3]\) is a valid enlargement.
Lowering k uses the previously proved scalar monotonicity of N, with
the incoming secant unchanged. It gives \(N_1<N<0\) when k>1
and \(N_1=N<0\) when k=1; both suffice.

If \(\chi\le4/7\), the stated endpoint \(q_\chi=4W/(7p)\)
is at most 8/7 because \(p\ge c\). The concavity estimate uses
\(q\le8/7\) and \(v>3/4\) with the correct directions. The
five displayed coefficient polynomials of \(7C-16A_2\) have the
claimed positive signs on the full closed h interval by the given
rational endpoint bounds.

The identities at q=1 and q=q_chi were reconstructed from equation
(5) of that note, substituting the displayed V_2 and logarithm upper
bound. The positive denominators and polynomial coefficients agree.
For q=1, the negative terms are dominated by
\(12/25-1/30^3-4/30^2-4/30>0\). For the other endpoint, the
two derivative arguments for P_0 and P_1 have the claimed directions;
all remaining coefficients satisfy the stated coarse bounds by
substitution of h=6/25 or h=1/3 into terms of the appropriate sign.
The final loss is less than
\(13/30+26/900+1055/30^5\), leaving more than 2/15.

Concavity therefore puts the whole q interval above its positive
endpoint minimum, contradicting \(N_1<0\). This proves chi>4/7
without invoking a next-norm bound or transporting a cost cap.

## 3. Elimination of the event factor

The [factor-elimination theorem](MIXED_NONSHORT_FORWARD_Q_ELIMINATION.md)
is accepted for its full scalar domain, including every \(q\ge1\).

The logarithm upper bound follows from its displayed nonnegative
derivative and equality at one. Its multiplier in the difference
being estimated is strictly negative. The resulting quadratic has
the stated coefficients. All three coefficients increase with k:
the exact positive formula for \(\beta_k-\alpha_k\), together
with \(\beta_k<0\), proves this also for the middle coefficient.
They decrease with v because \(\alpha_v>0\). Thus evaluating
at k=1, v=V gives a lower polynomial for every y=q-1>=0.

The ceiling V<U(t), the factorization of 1-w_U(U(t)), and eta>=1/2
prove C_2>0 on the complete closed t,j rectangle. The bound
\(1-2x-x^2\ge119/900\) and the second positive bracket in that
factorization hold up to x=11/30. No unproved norm bound is used.

The discriminant is multiplied only by the positive square of
\(tpW^2QB_1\). Its recentered polynomial is concave in j: the
six displayed positive coefficient groups contribute less than
\(2\cdot10^{15}\), whereas the negative constant exceeds
\(8\cdot10^{15}\) in magnitude. These are upper bounds for
individual monomials on one fixed rectangle, not a cover requiring
an executable sign check.

At j=0, the weighted sum of the seven negative tail coefficients
is below the positive fifth-degree coefficient. At j=1/30, the
normalization u=15A gives exactly the coefficient comparisons in
equations (23)--(24). The positive sixth term absorbs the entire
negative tail. For the remaining quintic, the first three terms
are at least 1/12 on u<=1/2. For u=1/2+z, completing the square
in the constant, linear and quadratic terms leaves 1103/5760>0,
and the remaining terms are nonnegative. These signs include both
ends of every interval.

Consequently the discriminant is positive, and the completed-square
identity proves the quadratic positive for every real y at k=1,v=V.
Coefficient monotonicity extends the required sign to y>=0 on the
full stated domain. Strictness for q>1 and continuity at q=1 are
both accounted for. Using the original incoming floor then gives
\(h(q)\le h(1)+v-g\); the additional positivity needed to square
this estimate is supplied separately in the actual interface.

## 4. Acceptance boundary

These three lemmas are accepted as hand arguments. Together with the
independently reviewed final scalar sign, they supply the estimates
used in the [restricted actual exclusion](MIXED_NONSHORT_SMALL_GAP_HAND_EXCLUSION.md).
The missing actual t and j bounds remain distinct obligations. None
of these reviews closes H-S or the unrestricted H-N-forward gate.
