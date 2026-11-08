# Outer S1 beta concavity with a constant norm interval

## Statement

Use \(F_1,\Gamma,w,E_L\) and the single fixed logarithm majorant \(\ell\)
from [the beta reduction](SHORT_OUTER_BETA.md). On the enlarged rectangle
\[
 3/2\le x\le2,\quad 1\le a\le6/5,\quad
 x\le\beta\le ax,\quad 3/4\le u\le19/25,
 \tag{1}
\]
the function \(F_1\) is strictly concave in \(\beta\), with \(x,a,u\) fixed.
This allows a constant norm interval to be used for the \(a=6/5\)
terminal shared by the outer S1 comparisons.

This is a separate derivative sign. It does not prove any terminal
\(F_1\) value by itself.

## 1. The beta-independent quadratic coefficient

Put
\[
 S=x+1,\quad K=6a^2+1,\quad B=a+\beta,\quad
 D_0=(a+1)(2x+1-a),
\]
\[
 E_0=S(u-1)+1/S,\quad J=KE_0+2S-1,\quad M=K^2-SK+S^2.
\]
The complete structured expression for the part of \(w\) independent of
\(B\) is
\[
 w_0=\frac{M+uD_0^2-D_0J}{49a^4}.
 \tag{2}
\]
Indeed, the numerator \(D\) in the original \(w\) satisfies
\[
 D=D_0+2(a-x)B.
 \tag{3}
\]
This is a six-monomial quadratic identity in \(a,x,B\); it can also be
checked coefficientwise in \(B\), leaving identities in \(a,x\) of degree
at most two. Thus \(w\) is quadratic in \(B\), with constant coefficient
\(w_0\).

For fixed \(x,a\),
\[
 \partial_uw_0=\frac{D_0(D_0-KS)}{49a^4}<0.
 \tag{4}
\]
Here \(D_0>0\), and the following four-monomial degree-three polynomial
has a positive-factor decomposition:
\[
\begin{aligned}
 KS-D_0
 &=6a^2x+7a^2-2ax-x\\
 &=(a-1)\{(a+1)(6x+7)-2x\}+3x+7>0.
\end{aligned}
 \tag{5}
\]
For the bracket, use \(a+1\ge2\), giving \(10x+14>0\).
It is therefore enough to bound \(w_0\) at \(u=19/25\).

The exact identity is
\[
 w_0(x,a,19/25)-6/7=\frac{N(x,a)}{1225a^4S},
 \tag{6}
\]
where the complete sixteen-monomial polynomial of degree six is
\[
\begin{aligned}
 N={}&-36a^4x^2-203a^4x-17a^4
       +72a^3x^3+68a^3x^2-304a^3x\\
    &+148a^2x^3+74a^2x^2-207a^2x+42a^2\\
    &+64ax^3+102ax^2-12ax+13x^3+32x^2-6x.
\end{aligned}
 \tag{7}
\]

## 2. A small positive lower polynomial

Put \(c=6/5-a\in[0,1/5]\) and \(z=x-3/2\in[0,1/2]\).
The complete shift identity is
\[
\begin{aligned}
 N(3/2+z,6/5-c)={}&
 -36c^4z^2-311c^4z-\frac{805}{2}c^4\\
 &-72c^3z^3-\frac{1096}{5}c^3z^2
       +\frac{5534}{5}c^3z+1992c^3\\
 &+\frac{2036}{5}c^2z^3+\frac{46004}{25}c^2z^2
       -\frac{7086}{25}c^2z-\frac{32961}{10}c^2\\
 &-\frac{18256}{25}cz^3-\frac{451326}{125}cz^2
       -\frac{334686}{125}cz+\frac{82989}{50}c\\
 &+\frac{53417}{125}z^3+\frac{2783533}{1250}z^2
       +\frac{6328071}{2500}z+\frac{253971}{1000}.
\end{aligned}
 \tag{8}
\]
It has nineteen monomials and degree six. Clearing the denominator 5000
leaves coefficients of at most eight digits.

Discard the positive terms containing \(c\). For each negative such term
use \(c^n\le5^{-n}\), without changing its power of \(z\). This gives
\[
 N\ge
 \frac{35089}{125}z^3+\frac{1878617}{1250}z^2
 +\frac{4959739}{2500}z+\frac{121483}{1000}>0.
 \tag{9}
\]
The lower polynomial has four monomials and degree three; every coefficient
is positive. Equations (4)--(9) prove
\[
 \boxed{w_0>6/7}
 \tag{10}
\]
on the entire rectangle (1), with no dependence on \(\beta\).

## 3. The separate beta derivative sign

The source expression simplifies exactly to
\[
 F_1=\Gamma-\frac7{96}
 \left\{\frac{a}{B}(7w-17/4)-E_L+(u-1)\frac Ba
                   +\frac67+\ell\!\left(\frac{2B}{7a}\right)\right\}
       -\frac{9193}{50000}.
 \tag{11}
\]
Use the quadratic form of \(w\) in \(B\); \(E_L\) is affine in \(B\).
Only \(w_0/B\) contributes a second derivative to the rational term.
For the expression in braces, denoted \(R_1\), this gives
\[
 (R_1)_{\beta\beta}
 =\frac{2a(7w_0-17/4)}{B^3}
       +\frac{d^2}{d\beta^2}\ell\!\left(\frac{2B}{7a}\right).
 \tag{12}
\]
The same rational logarithm majorant obeys
\(\ell''(y)\ge-1/y^2\) on \(0<y\le1\), as proved in the beta note.
Here \(0<2B/(7a)\le6/7\), because \(\beta\le ax\) and \(x\le2\).
Consequently its contribution in (12) is at least \(-1/B^2\).
Using (10),
\[
 (R_1)_{\beta\beta}>
 \frac{7a/2-B}{B^3}\ge\frac{a}{2B^3}>0,
 \tag{13}
\]
where \(B\le3a\). Since \(\Gamma\) is independent of \(\beta\),
\((F_1)_{\beta\beta}=-(7/96)(R_1)_{\beta\beta}<0\).

Thus any beta segment contained in (1) reduces to its two endpoints
while keeping \(u\) fixed anywhere in the same constant interval.
All required polynomial expansions are the quadratic source coefficient
identities, (5), the sixteen-term identity (6), and the nineteen-term
shift (8). Their degrees are at most six and their coefficients are
smaller than twelve digits.
