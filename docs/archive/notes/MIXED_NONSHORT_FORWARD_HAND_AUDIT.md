# Independent acceptance of the complete nonshort forward hand proof

Date: 2026-11-08 UTC.

**Acceptance:** the [forward-successor hand theorem](MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md)
excludes the actual forward alternative in the smaller-nonshort case.
Together with the already accepted reverse-successor theorem, it closes
H-N. The smaller-short gate H-S remains a separate open obligation.

This review checks the complete actual domain and the exhaustive ratio
split, as well as the new multiplier, low-shape and upper-shape signs.
The high-ratio theorem has its own
[independent audit](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_AUDIT.md), and
the final small-gap scalar theorem and event-factor comparison were
reviewed before the domain bounds were supplied. No nonshort interval
cover, Lean compilation, Lake, typechecking or CI is a proof premise.

## 1. The original geometry and the necessary inequalities

The continuation theorem uses the actual labels and margins
0(a),2(c),0(d),1(r) after the central reverse centre, with the smaller
adjacent turn assigned to c by the allowed reflection/time reversal.
The normalization T=a+c gives exactly t=a/T, x=(d-a)/T,
k=(a^2+4)/T^2 and the event factor in equation (1) of the theorem.
Thus p=d/T, W=(c+d)/T, and j=(d-c)/T.

The common order result applies without assuming the successor is
reverse, and gives k<1+j and j>0. The strict ratio bounds and scale
bound a<4/5 are independently established hand prerequisites. The
latter indeed gives k/t^2=1+4/a^2>29/4. The stronger swap inequality
uses the unchanged incoming secant and its original missing-control
floor. These are the hypotheses required by the gap argument.

The solved boundary outgoing norm is below the actual outgoing norm.
The transported next norm decreases on that original stationary line,
so the actual next forward norm floor transfers in the claimed direction
to T_*>=3/4. N<0 is the corresponding incident-upper residual sign.
No competitive cap is assigned to the solved boundary point. These
facts are precisely those needed for the low-ratio theorem and both
large-gap multiplier combinations.

## 2. Multiplier signs and the actual large-gap domain

The [multiplier-sign theorem](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md)
has a complete hand proof. The exact incoming derivative floor gives
t<T_0<T_G. Since T_G decreases and T_G(3/5)<1/3, the hypothetical
large-gap domain has x<3/5. The displayed positive difference between
T_G and the linear majorant gives j<5h/7. This argument uses the
original incoming norm, before any scalar substitution.

The explicit quarter-version multipliers satisfy alpha>=8/15 and
M>=1/20. The bounds Je^2<17/16, WD/x<=41/24 and W^2Dek<3h
are proved by the stated rational identities. The alpha>=2 case
absorbs the possible positive transport derivative with the first
two bounds. In the alpha<2 case, the multiplier identity gives
M-3h>1/48, absorbing it with the third. Hence the coefficient of
v is strictly negative throughout the closed domain. The logarithm
coefficient is negative by alpha+1-Je^2>113/240 and M>0.

Raising v to the positive-integral bound and log q to its elementary
rational majorant therefore lowers the actual negative combination.
The resulting rational G remains negative. No incoming floor is
asserted at the larger scalar value V. Its quadratic coefficient in k
is strictly negative; the independent floor multiplier is constant
in k, and changing the N multiplier adds only an affine function of k.

## 3. The low-t unit-shape sign

The [unit-shape theorem](MIXED_NONSHORT_LARGE_GAP_LOW_T_SIGN.md)
uses the positive multiplier 192q(q+1)W^3R and a homogeneous change
of basis on the entire closed domain. The projective substitution
w=4a/(1-a) gives h=1/4+a/12, so its homogeneous identity has the
claimed factor 4^m and includes a=1 without a division by zero.
The separate positive scale sigma affects no sign.

Its complete negative part has exactly the three stated groups.
The first square uses the z-degrees four, five and six with the
same b-degree zero. The second uses z-degrees three, four and five
at b-degrees three through six. The last uses b-degrees eleven
through fifteen at z-degree six. These groups are disjoint, so no
positive coefficient is used twice.

The two square identities are exact. For the final group,
2bs^3<=2s^4+b^2s^2/2 follows from s^2(b-2s)^2>=0, and gives
the stated sum of squares for the remaining quartic. This argument
is homogeneous and includes b=0 and b=1. The strict neighbor
comparisons leave a positive remainder at the only corner coefficient
that is partially used.

The four corner monomials in each of rows zero and eighteen cover
the whole closed (b,z) square: at least one is positive at every
point. Row zero supplies strictness when a<1, and row eighteen
supplies it when a=1. Thus the proof gives P>0 everywhere,
including all parameter endpoints.

For independent transcription verification, this review reconstructed
the original rational G from the residual and transport formulas,
formed the homogeneous coefficient identity, and checked all 38
literal negative coefficients, all 78 displayed neighbor comparisons,
and all eight strict corner coefficients. They agree with the compact
definitions and the printed sparse negative part. The final proof
consists of those finite identities and the three elementary
absorptions; it does not require running a coefficient checker.

## 4. The upper-shape sign

At k=1+j, the identities B=kW and
E=(1+2ty+ky^2)/W give the compact polynomial in the
[upper-shape theorem](MIXED_NONSHORT_LARGE_GAP_UPPER_SHAPE_SIGN.md).
Its change y=z(h-j)/(1+2j) has exactly the derivative numerator
D=(1+2j)T_j-12T. The normalized positive-basis coefficients have
the binomial factors specified in that theorem; the convention
is consistent in the norm bounds and endpoint calculations.

The complete negative norms are bounded with b<=2/9, which contains
the original b<=43/210 domain. Terms with b-degree at least two
are charged to b squared; the remaining terms are charged to L_*.
The displayed constant and quadratic coefficients strictly exceed
their respective complete losses. Thus every derivative coefficient
is positive, so P increases in j at fixed h,z.

At j=1/30, six positive-basis coefficients have no negative terms.
The last has only the four displayed negative terms. Their combined
loss is below 1912a^2, while the retained constant and linear terms
give 16+200a-1912a^2. Concavity of this last quadratic and its two
positive endpoint values prove the endpoint sign, including a=0 and
a=2/15. Increasing j then proves the full upper-shape result.

Independent reconstruction in this review confirms its normalized
polynomial, the complete rounded negative-norm polynomials L_*,R_i,
all constant and quadratic lower bounds, all weighted upper bounds,
and the endpoint negative support and coefficient ceilings. These
are the finite arithmetic identities used in the displayed proof.

## 5. Both ratio cases and the final actual contradiction

For 1/3<t<=3/8, the actual k lies in [1,1+j]. Strict concavity and
the two accepted positive endpoint signs imply G>0, contradicting
the necessary G<0. Using k=1 is valid even when the actual scale
lower bound is larger.

For 3/8<=t<2/5, the separately audited high-ratio theorem uses
constant multipliers 4 and 1. Its shape derivative is positive on
the actual interval, and lowering k to 29t^2/4 retains the required
negative sign. The explicit polynomial sign on that lower face gives
the contradiction. Its later enlarged h and q comparisons are scalar
polynomial inequalities, not new physical admissibility assertions.

These two cases are exhaustive and include their common endpoint.
Together with the already accepted t>1/3 result, they prove
0<j<1/30. The small-gap chi lemma, event-factor elimination and
final Casimir sign therefore apply to every remaining actual point.
The actual outgoing norm is below the central upper-envelope norm;
the original stationary-line Casimir decreases between them.
Positivity of its diagonal is established before the upper estimate
is squared. The resulting squared Casimir exceeds 9193/50000,
contradicting the cap of the original competitive period.

## 6. Uniformity and ledger conclusion

The first event and successor are actual switches of the same finite
normal period. The same-covector continuation includes a successor
across the twisted seam. The proof uses no word count or numerical
upper bound on the number of arcs, and does not fit a fresh costate
or endpoint constraint at an intermediate switch.

The forward and reverse successor alternatives are exhaustive.
The new theorem and the earlier reverse hand theorem therefore close
the whole smaller-nonshort case H-N under the stated retained inputs.
This review does not close the smaller-short gate H-S or assert the
final hand-only Reinhardt theorem before that remaining gate is proved.
