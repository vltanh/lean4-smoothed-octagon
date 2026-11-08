# Independent hand audit of the nonshort ratio and scale bounds

Date: 2026-11-07 UTC. Independent internal mathematical review.

The following hand results are accepted:

- [The retained central Casimir bound](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md).
- [The high-ratio exclusion](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md), proving t<2/5.
- [The conditional scale estimate](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md), consequently proving a<4/5 for actual smaller-nonshort data.

These are necessary restrictions. Neither successor exclusion nor the
common low-a exclusion is declared complete by this audit.

## 1. Retain a bound on unchanged data

The incident Casimir numerator is strictly increasing in each norm on
the actual rectangle. The explicit turn floor therefore permits lowering
only u while keeping the exact incoming secant v. The remaining diagonal
increases with the actual opposite ratio, since its derivative is
(U(z)-m)/z^2>0. Bounding its square by the two endpoint squares is valid
without a sign assumption. Both resulting expressions depend only on
a,c,d, which the boundary comparison holds fixed.

Thus the necessary cap alternative is retained for its stated reason;
no upper Casimir cap is silently imposed on the artificial boundary
root. The single-endpoint simplification for a>=3/4 follows from the
explicit positive lower diagonal bound. The weaker 3/4-floor version
has the same verified direction.

## 2. Exclude t>=2/5

The residual numerator increases in the shape parameter, so the actual
k>7t^2 can be lowered to k=7t^2 while keeping its necessary negative
sign. At t>=2/5 this endpoint is still greater than one. The incoming
secant comparison and two-term logarithm bound give the displayed
factorization for bar-v minus g, hence x<1/3. The strict centre gap
gives x>1/7, since 15/49<8/25.

Both logarithm relaxations lower the residual. The sign of its v
derivative is negative on the full comparison domain and does not
require the relaxed norm to retain the actual upper ceiling. The
preserved incoming missing-control floor implies bar-v minus F-lower
is positive. Subtracting (q-1) times that quantity therefore makes a
stronger sufficient positive residual target, with the correct sign.

The displayed positive denominator clears that target to a cubic in
q-1. Its four coefficient derivatives are positive throughout the
stated rectangle. The review checked each coefficient bound in the
appendix using its four explicit t^2/t^3 envelopes: the remaining
expressions are affine, so their minima are at one of the two rational
t endpoints. The two positive tail bounds have the stated exact values
23396/729 and 1533791/39366. No coefficient-count premise is needed.

At t=2/5 the four complete polynomials match the cubic expansion.
The derivative of C1 divided by x decreases, and the derivative of H
divided by x increases; hence the asserted endpoint comparisons are
valid on each of the three scalar intervals. The positive-tail estimate
for J proves C3 increases. All rational endpoint estimates are strict.
For example, in the tight last row the C1 surplus over 77/50 is
2129/2733750, and the C2 surplus over -771/50 is 31823/8201250.
The three quadratic margins are respectively 71, 56 and 3079/2500.
This proves the whole cubic positive, not merely values at sampled q.

Thus t>=2/5 contradicts the actual negative residual and is excluded
by the complete displayed hand calculation.

## 3. The resulting scale a<4/5

If a>=4/5, the earlier hand bound gives 4/29<=rho<1/7. The explicit
turn floor and t<2/5 lower both actual norms to mu=94/125; the radical
comparison uses a difference of squares of 1/625. The lower diagonal
bound remains positive while the two ratios increase to 2/5, so the
resulting scalar Casimir is a valid lower comparison.

The one-variable comparison increases with rho: its derivative numerator
exceeds 179/522. At rho=4/29, the first positive logarithm-series term
gives the displayed exact rational lower bound, which exceeds the
competitive cap by 7438391/113906250000. The contradiction is strict.

The combined actual nonshort conclusions are therefore t<2/5 and
a<4/5. All geometric, scale and common-covector hypotheses used by
the scalar interface remain named. These stronger restrictions do
not assert that the remaining reverse or forward endpoint domains
have been excluded.
