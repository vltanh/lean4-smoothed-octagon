# One rational logarithm bound with a small derivative identity

This is a shared replacement tool for the large-sign proofs. It gives one
rational function, its orientation on both sides of one, a curvature bound,
and a compact upper bound for the incoming secant. **It does not by itself
close any requested S1--S6 sign.**

## 1. The bound and its range

For every \(y>0\), define the same rational function
\[
L_P(y)=
\frac{(y-1)(11y^2+38y+11)}
 {3(y+1)(y^2+8y+1)}.
\tag{1}
\]
Then
\[
\boxed{\log y\le L_P(y)\quad(0<y\le1),\qquad
       \log y\ge L_P(y)\quad(y\ge1).}
\tag{2}
\]
Both inequalities are strict except at \(y=1\).
All denominator factors in (1) are positive on the stated range.

The complete cubic numerator and denominator before the factor 3 are
\[
N(y)=11y^3+27y^2-27y-11,\qquad
B(y)=y^3+9y^2+9y+1.
\]
Their derivative identity is
\[
3B(y)^2-y\{N'(y)B(y)-N(y)B'(y)\}=3P(y),
\tag{3}
\]
where
\[
P(y)=y^6-6y^5+15y^4-20y^3+15y^2-6y+1=(y-1)^6.
\tag{4}
\]
The two cubics each have four monomials. Identity (3) is an identity of
degree six; its resulting polynomial has seven monomials and coefficients
of absolute value at most 60. In particular
\[
\boxed{\frac1y-L_P'(y)
 =\frac{(y-1)^6}{y(y+1)^2(y^2+8y+1)^2}\ge0.}
\tag{5}
\]
The function \(\log y-L_P(y)\) is increasing and is zero at one.
Integrating this derivative proves both orientations in (2).

There is no second approximation hidden in a reciprocal change:
\[
L_P(1/y)=-L_P(y).
\tag{6}
\]
This follows immediately from the printed reciprocal cubic identities
\(y^3N(1/y)=-N(y)\) and \(y^3B(1/y)=B(y)\).
Thus a lower bound for a logarithm above one gives the identical upper
bound for its reciprocal below one.

## 2. Curvature without a degree-nine expansion

On \(0<y\le1\), let the nonnegative error term in (5) be \(E(y)\).
It is the product
\[
E(y)=(1-y)^6\,y^{-1}(1+y)^{-2}(y^2+8y+1)^{-2}.
\]
Each factor is nonnegative and nonincreasing on this range. Consequently
\(E\) is nonincreasing, and
\[
\boxed{L_P''(y)\ge-1/y^2\qquad(0<y\le1).}
\tag{7}
\]
Equivalently, the product rule writes \(-E'\) as the sum of four
nonnegative terms:
\[
\begin{aligned}
-E'={}&\frac{6(1-y)^5}{y(1+y)^2(y^2+8y+1)^2}\\
&+\frac{(1-y)^6}{y^2(1+y)^2(y^2+8y+1)^2}\\
&+\frac{2(1-y)^6}{y(1+y)^3(y^2+8y+1)^2}\\
&+\frac{2(2y+8)(1-y)^6}{y(1+y)^2(y^2+8y+1)^3}.
\end{aligned}
\tag{8}
\]
Keep these as products and use the derivative rule for each factor.
Clearing their common denominator and expanding a degree-nine polynomial
is unnecessary.

In particular the beta-concavity argument in
[SHORT_OUTER_BETA](SHORT_OUTER_BETA.md) can use \(L_P\) in place of
the old cubic atanh truncation: it needs only (7). Its positive
division coefficient and all shape-derivative polynomials are unchanged.
The improved \(F_0\) beta-derivative argument can use (5); its logarithm
error is no larger than the old one, since
\[
\frac{(y-1)^6}{y(y+1)^2(y^2+8y+1)^2}
\le\frac{(y-1)^4}{y(y+1)^4}
\quad(0<y\le1).
\]
For this last comparison cancel nonnegative factors and use
\((1-y)(1+y)=1-y^2\le1+8y+y^2\).

## 3. A quantitative error estimate, when needed

Writing \(z=(y-1)/(y+1)\in(-1,1)\), the same function is
\[
L_P(y)=2z+\frac{10z^3}{15-9z^2}.
\]
Differentiation in \(z\) gives
\[
\frac{d}{dz}\left(
 \log\frac{1+z}{1-z}-2z-\frac{10z^3}{15-9z^2}
\right)
=\frac{8z^6}{(1-z^2)(5-3z^2)^2}.
\tag{9}
\]
Its numerator is one monomial of degree six. The denominator factors
are positive for \(|z|<1\). The error is odd, so integration yields
\[
\left|\log y-L_P(y)\right|
\le\frac{8|z|^7}
 {7(1-z^2)(5-3z^2)^2}.
\tag{10}
\]
This is an error estimate for the same rational bound, not an additional
approximation substituted in a sign proof.

## 4. Direct upper bound for the incoming secant

For \(x>0,\ \beta>1\), the incoming secant is
\[
u=1+\frac{x^2}{(x+1)(x+\beta)}
 -\frac{x}{\beta-1}\log\frac{x+\beta}{x+1}.
\]
The logarithm's argument exceeds one. Therefore (2) gives
\[
\boxed{u\le U_P(x,\beta)
=1+\frac{x^2}{SA}
 -\frac{x\,N_I}{3(A+S)H_I},}
\tag{11}
\]
where every polynomial factor is printed:
\[
\begin{aligned}
S&=x+1,\qquad A=x+\beta,\qquad A+S=2x+\beta+1,\\
SA&=x^2+x\beta+x+\beta,\\
H_I&=A^2+8AS+S^2
 =10x^2+10x\beta+10x+\beta^2+8\beta+1,\\
N_I&=11A^2+38AS+11S^2
 =60x^2+60x\beta+60x+11\beta^2+38\beta+11.
\end{aligned}
\tag{12}
\]
The factor \(\beta-1\) cancels before (11) is expanded. The formula
extends continuously to \(\beta=1\), where it is the exact secant
endpoint \(1-x/(x+1)^2\).

For a complete polynomial normalization, put
\[
D_I=3(x+\beta)(x+1)(2x+\beta+1)H_I.
\]
It is positive. Then \(D_IU_P=P_I\), with the full polynomial
\[
\begin{aligned}
P_I={}&3\beta^4x+3\beta^4
 +31\beta^3x^2+55\beta^3x+27\beta^3\\
&+91\beta^2x^3+179\beta^2x^2+124\beta^2x+27\beta^2\\
&+120\beta x^4+238\beta x^3+179\beta x^2+55\beta x+3\beta\\
&+60x^5+120x^4+91x^3+31x^2+3x.
\end{aligned}
\tag{13}
\]
This has 19 monomials, total degree five in two variables, and
coefficients of absolute value at most 238. The factored denominator
also has 19 monomials and degree five if expanded, with coefficients
of absolute value at most 348. No large numerator is needed to check
this incoming substitution itself.

A replacement of the norm inside another residual still needs that
residual's monotonicity or concavity argument. In particular (11)
does not authorize assigning actual root, norm-floor, Casimir or
completion properties to the changed scalar norm.

## 5. A sharper small bound for V(x)

At \(\beta=x>1\), (11) simplifies to
\[
V(x)-\frac34
\le \frac{(x-1)^2(43x^2+34x+3)}
 {12(x+1)(3x+1)(21x^2+18x+1)}.
\tag{14}
\]
Equivalently,
\[
U_P(x,x)=
\frac{305x^4+595x^3+421x^2+113x+6}
 {6(x+1)(3x+1)(21x^2+18x+1)}.
\tag{15}
\]
The numerator has five monomials and degree four. This improves the
older bound \(u_v=3/4+2(x-1)^2/[(x+1)(35x+13)]\), since
\[
u_v-U_P(x,x)=
\frac{(x-1)^3(7x^2+58x+15)}
 {12(x+1)(3x+1)(35x+13)(21x^2+18x+1)}\ge0.
\tag{16}
\]
The numerator expands to the six-term, degree-five polynomial
\[
7x^5+37x^4-138x^3+122x^2-13x-15,
\]
whose sign is proved by the factors in (16).

At \(x=2\), the new upper value is exactly \(642/847\).
The error estimate (10), with \(z=1/7\), proves the rational bound
\[
0<U_P(2,2)-V(2)\le\frac1{8608908}.
\tag{17}
\]
This establishes the accuracy of the low-degree rational bound
without a numerical logarithm calculation. It is not a proof of
any S3 or S4 residual sign.

All displayed polynomial identities were checked by exact symbolic
arithmetic as a transcription check. Their derivative and factor
arguments are the proofs. No Lean compilation or CI was run.

