# Independent review of the thirteen-sixths shape extensions

Date: 2026-11-08 UTC. **Upper-order extension and extended Casimir
floor accepted after independent final reading.**

This review covers the extension of
[the small-shape upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md)
from x<=15/7 to x<=13/6, and the new
[extended Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md).
The first conclusion is proved analytically. The second now has a
complete replacement proof of all six derivative signs, with the
finite polynomial bounds discussed below:
\[
\alpha\le1+3(\beta/x-1),
\qquad \Gamma_{\rm actual}>1829/10000.
\]
The hypotheses on x and beta/x-1 remain explicit. This review does
not derive the required actual upper-ratio or short-gap restriction.

## 1. The upper-order extension

The exact derivative formula, Simpson upper estimate, barrier contact
factorization and complete polynomial Q are unchanged from the already
accepted proof. The only enlargement is z=x-1<=7/6.

The reviewer checked every changed bound in the lower estimate:
\[
87-65z\ge67/6>0,\qquad
165-81z^2\ge219/4>0.
\]
For the last coefficient, on 1<=z<=7/6 one has
\(z^2-18z-15\ge-36\), and hence
\(2(z-1)(z^2-18z-15)\ge-12\). The subsequent uses of
\(h^6\le h^2\) and \(h<z/(z+3)\) preserve the lower-bound
direction. They give exactly the same cubic
\[
J(z)=100/3+49z-148z^2/5-26z^3.
\]
It is concave, and its new terminal value is exactly
\(J(7/6)=4819/540>0\). The derivative comparison therefore holds
throughout the enlarged contact domain. The continuation and strict
first-contact argument require no other change. The upper order is
accepted for x<=13/6 and beta/x-1<=1/19.

## 2. The extended scalar comparison domain

The strong lower order still supplies eta>=13/5 when x>=2. Together
with the reviewed upper order this gives the same parameter box
alpha=1+eta*delta, 13/5<=eta<=3, delta<=1/19.

The reviewer checked the new preliminary bounds independently:

- The first positive term in the incoming upper norm is at most
  49/4482. For its tail, x/(beta-1)<=2 gives the stated bound
  1/(24*19^3). Thus the unchanged upper bound 31/40 is valid.
- D>=116/171 follows by taking alpha>=1, beta<=130/57 and
  x-1<=7/6 in the displayed lower estimate. The old increasing-delta,
  decreasing-x upper polynomial for D-S remains valid.
- The bounds q_c<=121/843<1/6 and T>2 are unchanged and valid.
- The discriminant proof of A2>0 uses only S<5 and
  (S-2)^2/alpha^2<2, which hold throughout 3<=S<=19/6.
- The argument C0<=5 remains valid: E0+u>0, and the upper estimate
  2S(E0+u)<=13/5 still follows from its decreasing quadratic in S.

The new Casimir derivative bound is
\[
H\le49/456,\quad 2S-1\le16/3,
\qquad (\Gamma_*)_q\le49/475<11/100.
\]
Together with (R2*)'>1 this proves the asserted derivative bound
\(-23/700\) for the corrected expression. The fixed-p comparison
continues to use 27/200<1/7. Both scale moves still compare a lower
bound on the original Casimir, without transporting an upper cap.

## 3. Incoming substitution on the enlarged rectangle

The previous derivative estimates for R2 remain valid. In particular
z=D/Sigma<1/3, C=S^3/Sigma>=20/7 and 1/r_A>=30/11 are unchanged.
The coarse bound w_u>=-1 remains true even with C<=19/6:
its lower corner value is 1/9-19/18=-17/18>-1.

The upper duration estimate T<=S follows directly from
\[
S\alpha(\alpha+\beta)-\Sigma
=x\{\alpha^2+S\alpha(1+\delta)-(x+2)\}\ge0.
\]
Hence the second residual derivative has the claimed lower bound
2867/1386. At the new upper S endpoint, the minimum central pairing
is exactly
\[
E\big|_{u=3/4,S=19/6}=485/8664>0.
\]
Consequently the earlier Casimir derivative bound 81/320 remains
valid, and it is less than 2867/9702. Both corrected expressions
therefore still decrease when the incoming norm is raised to its
specified rational upper bound.

## 4. Replacement of all six coefficient-group premises

The new [derivative proof](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
replaces the earlier derivative section in its entirety. It does not
use any of the five extracted negative-coefficient norms, or any of
the seventeen degree-sixteen positive-basis coefficient minima.
Only the analytic scalar comparisons in Sections 1--3 of the original
small-shape floor survive as inputs to the extended theorem.

The new proof defines Phi and Psi by their exact central-scale
formulas, with the specified rational incoming upper value. It then
gives polynomial products for both rational numerators and denominators.
These products have been freshly compared with the original formulas:
the identities for u, E, w, E_L, Gamma, Phi and Psi all agree exactly.
The logarithmic derivative formula includes both derivatives of
alpha*(alpha+beta) and of Sigma, with the minus sign from
-log(2/T)/7. Thus every derivative is of the actual stated scalar
function, not a related approximation.

The six positive clearing factors are unchanged. The last two are
specialized at x=13/6, as required. Their positive normalization
origins are the rational values in (13) of the new proof. The quotient
Psi_eta/(x*delta) has an exact polynomial extension at delta=0;
its positive extended value is consistent with Psi_eta=0 there.

Here is the complete replacement sign mechanism:

- For row one, the positive univariate contribution is retained as
  (1+h)^9. The adverse part of h degrees at most ten is bounded by
  (1+h)^10*M, with M explicitly printed as a short polynomial and
  one product. The remaining h degrees are bounded by the single
  product H. The elementary estimates M<3/5 and H<10^-6 imply
  the normalized polynomial exceeds 1/4 on h<=1/6.
- For rows two through four, the complete adverse parts are bounded
  by the products E2, E3 and E4 printed in (18)--(20). The binomial
  coefficient rule (21) specifies every coefficient in those bounds.
  The uniform bounds are E2<1/2, E3<3/5 and E4<1/2.
- For row five, only powers three, five, six and eight can be adverse;
  the single product z^3*(1+z)^5/50 bounds all four and is below 1/100.
- For row six, every adverse coefficient is printed individually:
  the six powers are two, three, four, five, six and twelve. Their
  majorant is below 9/25 at delta=1/19 and hence on the whole interval.

The degree bounds in (14) account for all monomials. Exact expansion
of the fresh rational derivatives confirms each coefficientwise
inequality (16)--(20), not just its value on a sample or a net.
The scalar estimates in Section 4 use only small rational endpoints
and integer-power comparisons. In particular, the final row has

\[
E_6(1/19)=793869650016231/19^{12},
\]

and the positive integer difference for comparison with 9/25 is
73093021189674. These checks support the explicitly stated finite
polynomial derivation; the scratch calculations are not premises of
the hand theorem.

## 5. Endpoint direction and original-covector interface

The six signs produce exactly the required endpoint chain. For Phi,
increase delta first, then increase x on delta=1/19, then increase eta
on the terminal edge. For Psi, lower eta first, increase x second,
and apply the strict concavity in delta on the terminal edge. The
resulting alternatives are

\[
\Phi\ge\Phi(13/6,1/19,3),
\]
\[
\Psi\ge\min\{\Psi(13/6,0,13/5),\Psi(13/6,1/19,13/5)\}.
\]

A fresh reconstruction matches all three rational endpoint pairs
(y,Z0) in the extended floor. With z=(y-1)/(y+1)<0, the finite odd
logarithm upper estimate gives strict excesses over 1829/10000 larger
than 1/12500, 1/5000 and 3/10^6, respectively. These are exact rational
inequalities. The last margin is small but positive; a rounded decimal
comparison is not used.

The central outgoing norm can lie on either side of 3/4. The
max-of-two residual bound, and hence the min-of-two Casimir lower
bound, retain both possibilities. The incoming upper value is
substituted only after proving that both corrected expressions
decrease with that norm. The fixed-p and fixed-duration scale
comparisons still yield a lower bound on the original actual Casimir.
They do not assign the original competitive upper cap, physical cost
or period closure to a comparison point.

Thus the new six-sign proof removes the sole algebraic gap in the
extended floor. Its accepted conclusion is
Gamma_actual>1829/10000 for every actual smaller-short bridge with
2<=x<=13/6 and 0<=delta<=1/19. The strong lower order and the reviewed
extended upper order supply 13/5<=eta<=3, including alpha=1 when
delta=0. These are explicit actual-domain hypotheses; the ratio and
displacement theorems are responsible for supplying them before the
floor is used in the whole smaller-short exclusion.

The previous diagnostic group norms have no remaining role in the
proof.

## 6. Final independent acceptance

A separate reading checked the entire actual-to-scalar chain, the
extended upper-order barrier and all six new derivative arguments.
The incoming norm is changed only after both corrected expressions
have been proved decreasing in that norm. The original corrected
Casimir comparison extends to q_c<1/6 by its own derivative signs;
it does not transport the actual q<1/7 cap.

The reviewer rebuilt the two rational scalar functions from the
printed numerator and denominator products (6)--(9) of the new
derivative note, independently of the original-function expansion.
Quotient differentiation and the exact logarithmic derivative give
all six published W_i, including the removable x*delta factor in
row two and the second derivative on the terminal edge in row six.
Multiplication by the six positive Q_i and the stated normalizations
gives precisely the six polynomials used in the majorants.

Every coefficientwise comparison (16)--(20) was checked against
that reconstruction. The published elementary bounds give
M<3/5, H<10^-6, and E2,...,E6 below their stated rational limits.
The retained positive baseline in the first row is essential and
is preserved; it is not replaced by an adverse-coefficient sum.
The endpoint sign chain follows with the displayed monotonicity and
concavity directions. Independent evaluation of the three final
rational pairs reproduces all numerators and denominators in the
floor theorem, and their strict rational margins in (10).

These checks are supplementary transcription verification. The hand
deduction itself is the fully specified product comparisons, their
binomial expansion rule, and the printed rational bounds; it requires
no run of the checking code. The reviewer accepts the original
Casimir conclusion throughout the entire closed [2,13/6] interval,
including delta=0 and the strip beyond 15/7. S4 is complete once
its caller supplies the already stated actual ratio and displacement
hypotheses.
