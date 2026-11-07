# Independent review of the common nonshort low-scale hand proof

Date: 2026-11-07 UTC.

**Verdict: accepted.** The [complete low-scale proof](MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION.md)
establishes \(a>1/2\) for every actual smaller-nonshort window under
its named hand prerequisites. The
[high-ratio derivative lemma](MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE.md)
is also accepted. These arguments replace the common low-\(a\)
interval exclusion. They do not close the remaining forward-successor
Casimir endpoint problem or the smaller-short case.

This is an independent internal mathematical review. No kernel-checking
or external peer-review claim is made. The proof premises are the
displayed identities and their elementary sign arguments.

## 1. Actual-domain reduction is exhaustive and preserves the needed floor

The common strict order gives \(k<2t+x\), while \(a\le1/2\) would give
\(k\ge\max(1,17t^2)\). The previously proved hand reduction gives
\(t<7/20\). The common duration bound gives \(x<7/3\).

For \(t\le1/4\), these facts imply \(x>1-2t\ge1/2\), and lowering
the shape to one preserves the exact incoming secant and floor.
For \(t\ge1/4\), the polynomial \(17t^2-2t-1/2\) is increasing
and already \(1/16\) at the left endpoint, so lowering to
\(k_h=2t+1/2\) is legitimate. Here \(x>17t^2-2t\ge9/16\).

The exact rational difference between the secant upper bound and its
turn derivative floor gives \(t<T(x)\). The displayed strictly negative
derivative of \(T\), and \(T(1)=19/81<1/4\), force \(x<1\) in
the high-ratio case. Thus the two stated scalar domains cover every
hypothetical actual low-scale point. The incoming missing-control floor
is independent of the changed shape. No new outgoing norm, next margin
or artificial Casimir assertion enters this reduction.

## 2. The corrected quartic has the claimed comparison direction

The reviewer reconstructed \(N=tBqWR\) from the original diagonal,
outgoing envelope and first-event residual. Differentiation gives
exactly \(N_v=-A\). On both selected faces, \(k-2t\ge1/2\), so
every factor needed for \(A>0\) is positive. The coefficient of
\(\log q\) is strictly negative as well.

Both logarithm estimates have the stated strict directions.
In particular,
\[
(L_+-\log q)'=\frac{(q-1)^4}{6q^2(q+1)^2}>0.
\]
Thus \(F_\ell<F_{p/W}(q)\le v<\bar v\), and subtracting
\(A(\bar v-F_\ell)>0\) lowers the rational comparison residual.
The implication from \(Q>0\) to \(N>0\) is therefore sound.

Independent collection of powers of \(y=q-1\) reproduces the five
formulas (8) of the source. The source also displays their short
derivation from \(Cq^2+Dq-E-LqL_+\), so the quartic's coefficients
are specified by finite identities rather than an executable
coefficient-sign assertion.

## 3. Six coefficient inequalities imply positivity for every q

After division by \(P_0>0\), let \(b=-P_2/P_0\).
The six signs give \(b<48\), the linear coefficient greater than
\(-2\), the cubic coefficient greater than
\(\max(1,4b)\), and the quartic coefficient greater than one.
For \(b\le0\), the discarded quadratic term is nonnegative.
For \(0\le b\le48\), the bound is affine on each side of \(b=1/4\);
checking \(0,1/4,48\) is exhaustive.

The two square identities in (10) are exact. Completing the remaining
linear/quadratic terms gives respectively
\(323/7047>0\) and \(23/144>0\). They apply on the entire half-line
\(y\ge0\), including its endpoint, with no subdivision or bound on
the first-event factor.

## 4. Unit-face derivative and endpoint signs

Independent substitution in the quartic gives all four factorizations
(11), every displayed polynomial in Appendix A, and the entire
Appendix B identity.

The derivative comparison in Section 4 has the correct direction.
The lone negative tail in the first derivative row is bounded by
\(26z^6-4z^7\ge(34/3)z^6\), since \(z\le11/3\).
For the fourth row, the four negative tail terms at \(s=0\) are
absorbed by the positive \(z^4\) term using the displayed rational
bound. Its negative \(s^3\) coefficients are absorbed into the
positive \(s\) coefficients because \(0\le s\le1\). Consequently
the whole derivative is at least its value at \(s=0\), not just
positive. This justifies the tangent lower bound used for \(x\ge1\).

For \(1/2\le x\le1\), all four base polynomials match their claimed
formulas. The three second derivatives of \(b_i'/x^2\) are strictly
negative on that interval; the left derivatives and both endpoint
values have exactly the fractions shown in the source. Concavity
therefore allows at most a positive-to-negative sign change of
\(b_i'\). Each polynomial's minimum is at an endpoint. The direct
lower bound for the first polynomial is positive as well.

For \(1\le x\le7/3\), all four tangent identities (17) were
independently expanded and match the stated \(h_i\).
The lower- and higher-degree negative terms are charged in the
correct directions using \(x\ge1\) and \(x\le7/3\), respectively.
The four displayed positive remainders prove the signs throughout
this interval. No incoming floor is assumed at \(t=1/4\) when that
value lies outside the actual turn domain.

The last two coefficient comparisons are valid at their distinct
lower faces. The Appendix B lower polynomial is exactly its constant
row plus the negative rows allowed by \(0\le s\le1\).
The values at \(t=(1-x)/2\) and \(t=0\) in (19)--(20) match
the direct substitution and are positive on their stated intervals.
For the final comparison, \(P_0\) decreases along the entire
interval from zero to the target \(t\), while \(P_4\) increases.
Its initial difference is the polynomial in (21), positive at
\(x=1/2\) with positive derivative thereafter. The apparent \(1/t\)
has already cancelled; this uses a continuous coefficient extension,
not a zero-duration geometric premise.

## 5. High-ratio derivative lemma

The reviewer independently reconstructed the same quartic with
\(k=2t+1/2\), substituted \(t=(1+u)/4\), \(x=(1+z)/2\),
and matched all six identities
\[
1024X^3\,dJ_i/dt
=g_i(1+z)^{m_i}
 \{A_i+u(1-u)B_i+u^2D_i\}.
\]
Every factor and every coefficient polynomial matches the lemma.
All \(B_i,D_i\) have nonnegative coefficients. Four \(A_i\) have
positive coefficients; the two others satisfy
\(A_0\ge7953>0\) and \(A_2\ge1051292>0\) on \(0\le z\le1\).
Since \(0\le u\le2/5\), the displayed decomposition is strictly
positive and proves every total derivative sign.

At \(t=1/4\), this shape equals one and the already established
base signs apply. Only a polynomial inequality moves with \(t\).
The exact incoming floor is used afterwards at the original
parameters in the implication from \(Q>0\) to \(N>0\).

## 6. Uniform actual-window conclusion

Every hypothetical actual point with \(a\le1/2\) therefore gives
a lower shape at which \(N<0\) by strict shape monotonicity.
The six coefficient signs and the quartic argument give \(N>0\)
there, a contradiction.

All upstream prerequisites in this argument are hand results:
the common shape monotonicity, low-scale ratio reduction, exact
turn-duration estimate and common-order corollary. The latter uses
the nonshort reverse scalar theorem; it does not assume the
computational low-\(a\) exclusion or the remaining forward case.
There is no circular dependency.

The conclusion is independent of the next switch sign and uniform
in the surrounding period. It keeps the same original incoming
covector data and genuine switch floor throughout their uses.
The full forward-successor and smaller-short exclusions remain open.
