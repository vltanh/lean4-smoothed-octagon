# Independent review of the large-ratio outer-scale sign

Date: 2026-11-08 UTC.

The proof in
[MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN](MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN.md)
is **accepted** as a hand scalar theorem on its stated enlarged
domain. Its three rational signs and their use in the piecewise
tangent bound are complete. This review does not by itself assert
the final smaller-short exclusion.

## 1. Reconstruction from the original transport

The review reconstructed the scalar expressions from the same-covector
transport formulas, independently of the author's A_1,A_2,A_3
expansion. At q=1/7 those original formulas give

\[
\rho=(6\alpha^2+1)^{-1},\qquad
\lambda=\frac{6\alpha^2+1}{7\alpha^2},\qquad
 d_{\rm tr}=\frac{D}{7\alpha^2},\qquad
 t_0=\rho(1+x).
\]

Writing S=1+x and E_0=S(u-1)+1/S, cancellation of the positive
scale denominators gives directly

\[
\begin{aligned}
49\alpha^4w={}&(6\alpha^2+1)^2-S(6\alpha^2+1)+S^2+D^2u\\
&-D\{(6\alpha^2+1)E_0+2S-1\},\\
7\alpha^2E_L={}&2Du-(6\alpha^2+1)E_0-2S+1.
\end{aligned}
\tag{1}
\]

These agree with the expressions in the sign note. The distinction
between its normalized d=D/alpha^2 and the transported diagonal
coefficient d_tr=q*d is correct.

The review inserted the original incoming upper bound, with its cubic
tail, into (1). It then reconstructed each of F_T,F_8,F_2 and cleared
the common denominator exactly as specified in that note. All three
polynomials have degree at most six in beta, and the common
normalization is correct. In particular, the 8 and 2 faces are not
silently multiplied by the extra factors 9 and 3 that would be needed
to make their individual coefficients integral.

## 2. Enlarged domain and the beta substitution

The lower affine alpha bound follows from the actual outer-scale
inequality alpha^2>=x(x+2)/6. The displayed difference of squares
has positive numerator on x>=12/5, and both quantities being compared
are positive. The enlargement is therefore in the required direction.
The interval parameter in alpha has positive width because
33x-20>0.

The lower and upper beta bounds follow from the accepted two order
lemmas. Their difference is

\[
\frac{x^2(19x-11)(\alpha-1)}
 {(5x+4)(4x^2+11x+1)}\ge0.
\]

The substitution in the sign note runs exactly between these two
endpoints. All factors of its clearing denominator L and of the
original scalar denominator are positive. Thus no denominator sign
or additional boundary case is omitted.

## 3. Complete coefficient and norm review

Starting from the freshly reconstructed polynomials, the review
independently repeated the exact substitutions and the stated
degree-six binomial coefficient conversion in beta. It confirmed
that the resulting polynomials have degree at most 29 in X, eight in
the alpha parameter z, and six in the beta parameter t.

Every bound in the complete 30-row group table was reconstructed
with rational arithmetic directly from the specified coefficients.
For each of the 21 face/beta-index pairs and each X row, the three
lower coefficient bounds and the upper bound for the entire remaining
negative part hold. This checks all 2520 listed inequalities, with the
same common denominator convention. The independent reconstruction
used the exact rational definitions, not floating-point samples of
the continuous domain.

The mathematical sign argument attached to those finite identities
is sound. On 0<=z<=1, each negative coefficient of degree at least
three may be absorbed into its quadratic coefficient, because
z^j<=z^2. Each resulting lower quadratic has positive constant,
positive linear coefficient, and positive value at z=1. If its
quadratic coefficient is negative, concavity bounds it below by the
positive endpoint chord; otherwise positivity is immediate.
All thirty lower quadratics satisfy these elementary conditions.

The X powers and the binomial basis functions in t are nonnegative.
The k=0 row remains strictly positive at every endpoint, so strict
positivity is preserved on the whole closed scalar domain, including
z=0,1 and t=0,1. This establishes all three strict negative residual
signs after the positive denominators are restored.

## 4. Root parameter and actual scope

Both logarithm tangents are valid for all positive arguments. Their
intersection is y=8/9. On either tangent interval the scalar residual
has second derivative 2/tau^3>0, so its upper maximum is controlled by
2,T and the interior breakpoint when present. At tau=2, using the
single second tangent is an upper bound even if it is not the smaller
of the two tangent bounds.

In particular, the standalone F_2 sign remains valid when scale
comparison has passed T=2. The proof does not incorrectly apply a
root-parameter interval argument to an empty interval in that case.
The later incoming-upper substitution at such a tau=2 face is supplied
by the separate direct 2d_tr<1 argument; no tau<=T hypothesis is
transported to it.

No upper Casimir cap is used in the sign theorem. No outgoing norm
floor is assigned to the artificial envelope. Its application to an
actual bridge is through the previously proved positive
floor-weighted scalar expression and its scale comparisons. The
review accepts precisely this interface.
