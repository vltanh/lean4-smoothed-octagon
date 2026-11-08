# Independent review of the central low-ratio hand sign

Date: 2026-11-08 UTC. **Accepted scalar central-face theorem.**
This review independently checks the
[central low-ratio sign](MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md),
including its analytic reductions, complete polynomial identities
and exact terminal signs. Its role in the original-period
contradiction is the one stated in the
[lower-ratio assembly](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md).
The central theorem does not by itself replace the outer-face proof
or the actual corrected-cap comparison.

## 1. The two functions are the required central residuals

The proof uses \(c_*=7/96\) and \(g_*=9193/50000\).
Its letter E is the scaled pairing
\[
E=S^2\{S(u-1)+3/S-1/S^2\}=S^3(u-1)+3S-1.
\]
With this convention, all three displayed transport expressions
for w, E_L and Gamma agree with the central-scale envelope formulas.
In particular the Casimir numerator is
\[
4S^2(S^2-S+1)u-E^2,
\]
over \(16X^2\); no factor of \(S^2\) has been lost in the change
of notation.

For
\[
J=(u-1)(a+b)/a+a/(a+b)+1-q-E_L,\qquad h=w-3/4,
\]
one has
\[
J+2h+\log(2/T)=R_2.
\]
The other test uses exactly
\[
J+Th+\log(2/T)=R_2+(T-2)(w-3/4).
\]
Thus the functions F0 and F1 in the theorem are the two required
corrected Casimir excesses, with no change to the correction
coefficient or competitive constant.

The duration comparison uses
\[
\partial_\tau R_\tau=w-U(1/\tau)\le w-3/4.
\]
Integrating on \(2\le\tau\le T\) gives the maximum of the two
residual endpoints. This remains valid for either sign of \(w-3/4\);
there is no assumed outgoing norm floor after changing the scale.
Consequently positivity of both tests gives the claimed strict
corrected excess for every duration, including both endpoints.

## 2. Every actual central shape lies in the stated comparison domains

The condition \(q_c\le1/7\) is equivalent to
\(a^2\le x(x+2)/6\). Together with \(a\ge1\), it gives
\[
x\ge\sqrt7-1>23/14>8/5.
\]
The strict rational comparison is \(7>(37/14)^2\).
The exact square identity for the linear upper shape gives
\[
a\le a_U(x)=\frac{1013x+676}{2340}.
\]
At the upper endpoint,
\[
a_U(2)=1351/1170<7/6<6/5.
\]
The first inequality follows from \(1351<1365\), so the actual
alpha interval belongs to the rectangle used for the incoming and
beta derivatives.

The cone comparison is also in the necessary direction:
\[
(x+5)/6-a_U(x)=(1274-623x)/2340\ge28/2340>0.
\]
At \(x=23/14\), \(a_U=1+1/10920>1\). Therefore the complete
alpha segment from 1 to \(a_U(x)\) is nonempty and lies in the
stated cone for every actual terminal x. The proof applies its
alpha concavity only on that cone.

The two exact order inequalities imply the containing beta strip
\[
x+\frac47(a-1)\le b\le x+\frac{10}{13}(a-1).
\]
The lower coefficient comparison is precisely \(x\ge8/5\);
the upper comparison has numerator \((x-2)(51x+5)\le0\).
Both coefficients lie in \([1/2,4/5]\). The beta segment up to
\(b_+=x+10(a-1)/13\) therefore remains in the rectangle where
its derivative signs are proved.

The reviewer checked the denominator and duration bounds directly.
On that rectangle, decreasing \(K-2a(a+b)\) first by increasing
b, then by increasing a, gives
\[
K-2a(a+b)\ge x^2-x/3-301/180\ge319/900>0.
\]
Thus \(T>2\) everywhere used in the comparisons. Also
\[
14/15\le D\le229/36<7<S^3.
\]
For the lower bound, use \(a^2+1\ge2\), \(2x\ge16/5\),
\(b\le32/15\) and \(x-a\le1\). For the upper bound, discard the
nonpositive term \(-2b(x-a)\). It follows that
\[
w_u=D(D-S^3)/K^2<0.
\]
All denominator factors are positive on these enlarged sets.
Neither the central-cap condition nor the equal-secants condition
is asserted at their extra scalar points.

## 3. Incoming substitution and the derivative directions

The exact incoming bound has the cubic tail
\((b-x)^3/(48x^2)\). The new rational ceiling replaces this tail by
\((x-1)^2(b-x)/(8SZ)\). This replacement raises it once
\[
(b-x)^2SZ\le6x^2(x-1)^2.
\]
The strong order and \(a<6/5\) reduce that inequality to
\[
150(4x^2+11x+1)^2(x-1)^2-(7x+1)^2SZ>0.
\]
Its polynomial after \(x=3/2+v\) is exactly the positive polynomial
printed in equation (17) of the theorem. Since the actual x is
greater than \(23/14\), \(v>0\), and the required ceiling follows.
The case \(b=x\) already has zero tail and is covered.
This incoming ceiling is applied only to the original norm.

Both corrected tests have
\[
(F_j)_{uu}=-S^6/(8X^2)<0.
\]
Moreover,
\[
(F_1)_u-(F_0)_u=-c_*(T-2)w_u>0.
\]
The positive polynomial Pu therefore supplies the stronger needed
derivative bound: \((F_1)_u<0\) at \(u=3/4\). Concavity makes
it negative for every \(u\ge3/4\), and the displayed difference
then makes \((F_0)_u<0\) there too. Raising the original norm to
the proved ceiling lowers both tests, as required.

The beta derivative polynomials differentiate the substituted
functions at fixed x and a, including the beta dependence of the
incoming ceiling. The logarithm derivative is exactly \(1/(a+b)\).
Only after differentiating does the proof put
\(b=x+c(a-1)\) to describe a containing domain. Therefore the
argument is not a derivative at fixed c. At \(a=1\), the beta
segment has zero length; the polynomial formulas still extend
continuously and the weak endpoint comparison remains valid.

The alpha derivatives include the dependence of both \(b_+(x,a)\)
and the incoming ceiling. The first test decreases with alpha.
The second is strictly concave in alpha, so its minimum on
\([1,a_U(x)]\) is at 1 or \(a_U(x)\). All three resulting
one-variable tests are exactly those in Appendix C.

## 4. Complete finite polynomial signs

The clearing factors in Appendices A and B are positive. The
rational product formulas in (A1), together with the exact logarithm
derivatives, reproduce their stated derivative numerators.
The direct formula (A4) for Pu is consistent with
\[
(F_1)_u=\Gamma_u-c_*\{(a+b)/a-(E_L)_u+Tw_u\}.
\]
The corrected degree of Pu after the beta parametrization is
\((9,4,2)\) in \(x,a,c\).

The lower-polynomial constructions are valid term by term. In
Appendix A, \(|t|\le3/20\) bounds each nonconstant t term by its
absolute value. Since \(0\le A\le1/6\), a negative coefficient
of \(A^j\) can then be bounded at \(A=1/6\), while a positive
higher term can be discarded. This gives exactly (A6).
In Appendix B, the cone coordinate satisfies \(0\le A\le1\),
so the corresponding negative-coefficient bound is exactly (B4).
These are explicit finite inequalities, not asserted extrema.

The complete resulting univariate polynomials and their sign
arguments have the following accounting:

| Polynomial | Complete retained degree | Sign argument |
| --- | ---: | --- |
| Hu | 9 | All ten coefficients are positive. |
| Hb0 | 16 | Positive through degree 13, negative thereafter; the displayed value at \(2/5\) is positive. The additional positive \(2430z^{17}\) is discarded. |
| Hb1 | 15 | Positive through degree 13, negative thereafter; the displayed endpoint is positive. |
| Ha0 | 20 | Positive through degree 19, negative in degree 20; the displayed endpoint is positive. |
| Ha1 | 23 | Positive through degree 8, negative thereafter; the displayed endpoint is positive. |
| Q0U | 23 | Positive through degree 4, negative thereafter; the displayed endpoint is positive. |
| Q1U | 21 | Positive through degree 4, negative thereafter; the displayed endpoint is positive. |
| Q1b | 7 after discarding positive degrees 8--15 | Positive through degree 2, negative thereafter; the retained polynomial has positive endpoint. |

The elementary comparison
\[
H(z)\ge(z/r)^mH(r)\qquad(0<z\le r)
\]
is correct for a polynomial whose coefficients are nonnegative
through degree m and nonpositive afterwards. Each term has the
necessary inequality direction; the positive constant handles
z=0 separately. Here \(r=2/5\). Thus every row has a complete
hand sign argument on one interval.

As a supplemental transcription check, the reviewer inspected and
ran a reconstruction starting from the displayed rational transport
formulas and parsing the eight saved tables. It reproduced all five
derivative identities, both exact finite coefficient bounds,
all three terminal identities and every endpoint/sign-change claim.
It loaded no saved numerator polynomials. This checks the printed
arithmetic; the mathematical premises are the displayed finite
identities and the termwise sign arguments, without requiring that
calculation to be executed.

## 5. Logarithm direction, terminal scope and actual-period interface

The logarithm is differentiated exactly in every derivative argument.
Its rational upper bound is introduced only after all shape
comparisons. For \(0<y\le1\),
\[
\log y=2z+\frac23z^3+
       2\int_0^z\frac{t^4}{1-t^2}\,dt
\le2z+\frac23z^3,\qquad z=(y-1)/(y+1)\le0.
\]
Since the logarithm occurs with coefficient \(-c_*<0\), this
replacement lowers each terminal test. Positivity of the rational
lower function therefore proves positivity of the exact one.

All five low-degree factors in (C1) are positive for \(x\ge8/5\),
so the three clearing denominators in (C2) are positive. The exact
normalizations in (C3), including their constant multipliers, match
the printed polynomials. Their positive intervals contain
\(23/14\le x\le2\). At the extra polynomial points below \(23/14\)
no shape comparison is required: extending a numerator sign to
that larger interval does not assign actual geometry to it.
The \(x=2\) endpoints in all three tests are strictly positive.

The scalar conclusion therefore has the required scope:
on every actual central low-ratio face, the unchanged incoming norm
gives both corrected tests strictly above zero, and the maximum
residual comparison covers every retained duration. This supplies
\[
\Gamma_*-c_*R_\tau^*>g_*
\]
at that terminal face. The sharp corrected-cap theorem is the
separate input connecting this scalar value to a lower bound on
the squared Casimir of the original common covector. Its original
competitive upper cap is not moved to any changed shape or scale.

No small displacement, small-shape Casimir floor, root-to-shear
estimate or physical completion-cost theorem is assumed here.
Thus the central theorem can be used to prove the lower ratio
before those later short-case results, with no circularity.
The strict central-face sign, including all equality boundaries
in its stated domain, is accepted.
