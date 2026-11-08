# Independent audit of the high-ratio large-gap exclusion

Date: 2026-11-08 UTC. Accepted hand theorem, under the retained actual
nonshort forward hypotheses.

This review accepts
[MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION.md):
no actual eligible nonshort forward window can have
\[
3/8\le t<2/5,\qquad j\ge1/30.
\]
The result is a whole-domain scalar contradiction. It does not use
either of the nonshort forward interval certificates. The separate
low-ratio large-gap sign remains a separate input to a full gap bound.

## 1. The actual input and rational substitutions are unchanged

The theorem starts with the three retained inequalities
\[
N<0,\qquad\mathcal T_*\ge3/4,\qquad F_{p/W}(q)\le v.
\]
The transported norm is the same solved-boundary scalar from the
accepted continuation; the incoming floor is imposed at the original
incoming coordinates. The exact transport identity makes their
positive combination
\[
4N+C_*(3/4-\mathcal T_*)+F_{p/W}(q)-v
\]
strictly negative. The strictness follows already from N<0.

The domain needed for the scalar comparison follows from the
derivative floor, quantitative swap bound, common order, and common
scale inequalities. In particular
\[
h\in[1/5,1/4],\quad j\in[1/30,5h/7],\quad
q\le W/(1+2j),\quad 29t^2/4<k\le1+j.
\]
The local bounds \(Je^2<17/16\), \(WD/x\le41/24\), and
\(-N_v\ge xeWk>0\) were proved in the
[multiplier reduction](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md).
With constant multipliers 4 and 1, their coefficient calculation gives
\[
(\mathcal H_4)_v<-
\left(\frac{63}{16}-\frac{41}{24}\right)(-N_v)-1<0.
\]
The logarithm coefficient is also negative, since both
\((5-Je^2)N_\ell\) and the floor's logarithm coefficient are negative.
Therefore replacing v by its proved upper bound V and log q by
L_+ lowers the scalar combination. The required sign G_4<0 is a
valid consequence of actual eligibility. It does not assert a
switching floor for V itself.

## 2. Shape monotonicity has the required direction and domain

The identity
\[
U(t)-V=\frac{cx}{W^2}\{1-tW-T_G(x)\}
\]
is correct. The two estimates used to make it positive are
\[
T_G(x)\le T_G(1/5)=2231/5112<7/16,
\qquad tW\le361/672<11/20.
\]
For the latter, the only variable quadratic is
\((5h-12h^2)/14\); completing its square gives the stated
maximum. Hence the brace exceeds 1/80.

The coefficient \((F_4)_{kv}\) is strictly negative. Its potentially
positive transport contribution is bounded by W^2De, while the
negative residual contribution is controlled by
\(-N_{kv}\ge xeW\). The same ratio WD/x therefore proves the
displayed strict sign. The mixed derivative in k and log q is
negative as well. Consequently the substitutions V<U(t) and
L_+<q-1 give a lower bound for the shape derivative in precisely the
direction used in the proof.

The quadratic coefficient in k is
\(-tW^2De^3/4\). Thus the derivative decreases in k, and evaluating
it at k=1+j gives a lower bound throughout the actual interval.
The four displayed d_i in equation (10) satisfy the exact derivative
identity. In particular d_2<0, d_0>0, and d_3>0. The polynomial
4d_1+d_2 in equation (11) is also exact. Its constant and linear
terms contribute at least 144/125 when x>=1/5; its other three
coefficients are strictly positive. Since y<=1/4,
\(d_1+d_2y\ge d_1+d_2/4>0\). This proves (G_4)_k>0.

At an actual point, 29t^2/4>1 and 29t^2/4<k<=1+j. The segment
along which k is lowered therefore stays inside the domain where
this derivative sign was proved. The negative necessary sign passes
to the lower scale face. The later scalar positivity theorem may
enlarge that face beyond k<=1+j; no actual comparison uses those
extra points.

## 3. The cleared polynomial and both endpoint identities match

The scale-face polynomial was reconstructed directly from the
stationarity numerator and the transported norm, independently of its
expanded coefficient data. It is exactly
\[
P=192q(q+1)W^3R\,G_4
\]
with k=29t^2/4, t=(1-h)/2, x=h+j, q=1+y. The compact
specification in
[MIXED_NONSHORT_HIGH_RATIO_POLYNOMIAL_MONOTONICITY](MIXED_NONSHORT_HIGH_RATIO_POLYNOMIAL_MONOTONICITY.md)
has the same normalization. Its derivative is taken after substituting
the scale face, as required. The derivative inequality P_h<-237
holds on a rectangle containing every fixed-j,y comparison segment
to h=1/4. The allowed y interval expands when h increases, so no
endpoint parameter restriction is lost.

At h=1/4 the literal polynomials S_2 through S_6 in Appendix A
satisfy the complete second-derivative identity (16). The sole
negative constant in S_2 is dominated by its linear term at j=1/30;
the remaining displayed signs prove strict concavity in y throughout
the required interval.

The first endpoint has exactly the factorization
\[
P(1/4,j,0)=-5(4j+1)F_6(j)/33554432.
\]
The two displayed rational values of F_6 are correct. Since F_6
is convex on j>=0, the negative endpoint values bound it from above
by a negative chord, proving this endpoint sign.

The other endpoint has exactly the factorization (19), with the
entire Q_13 polynomial displayed in Appendix B. Its high-degree
coefficient sum is
\[
\sum_{i=4}^{13}a_i(5/28)^{i-2}
=\frac{8859712500098641534000}{1977326743}
<4500000000000<6238486162096.
\]
Thus its negative quadratic term dominates all positive terms of
degree four and above. The remaining constant is strictly negative,
and the linear and cubic terms are nonpositive. This proves Q_13<0
on the full closed interval, including both endpoints.

Concavity in y now supplies the whole endpoint rectangle, and the
decreasing h comparison supplies the whole scale face. The strict
positive sign there contradicts the necessary negative sign obtained
from the actual window.

## 4. Verification and scope

The derivative formulas, normalization, literal S-polynomials, both
endpoint factorizations, endpoint fractions, and weighted positive sum
were separately checked as exact algebraic identities. These checks
confirm the transcription; the inequalities in the proof are the
displayed rational comparisons, monotonicity, and concavity arguments.
No executable sign certificate is a mathematical premise.

The argument retains one actual normal covector and its original
incoming and forward-successor conditions until the scalar
comparisons begin. It introduces no artificial competitive Casimir
cap, no extra switch, and no closed competitor. Its use in the full
nonshort forward gap bound is therefore accepted on the stated
high-ratio domain.
