# The S1 outer S branch: reciprocal-shape concavity at a fixed slope

Use the exact functions of [the beta reduction](SHORT_OUTER_S_BETA.md).
For each fixed \(u\in\{3/4,19/25\}\), put
\[
 \beta=x+\frac8{17}(a-1),\qquad r=1/a,
 \qquad 1\le x\le\frac32,\quad\frac1x\le r\le1.
 \tag{1}
\]
We prove that \(F_1\), considered as a function of r at fixed x and u, is strictly
concave. Thus its minimum in shape is attained at \(a=1\) or \(a=x\).
The fixed-slope terminal values are proved in the
[terminal companion](SHORT_OUTER_S_TERMINAL.md); this note supplies its shape
reduction.

## 1. A coefficient-preserving source interface

Put
\[
\begin{gathered}
 S=x+1,\quad d=25/17,\quad e=x-8/17,\quad Z=d+er=B/a,\\
 d_0=33/17,\quad d_1=(18x-16)/17,\quad
 d_2=(-34x^2+50x+17)/17,\\
 A_0=(x^2+x+1)/S,\quad E_0=S(u-1)+1/S,\quad J_2=Su+A_0.
\end{gathered}
\tag{2}
\]
In these variables the normalized transport parameters are
\[
 \lambda=(6+r^2)/7,\qquad
 \delta=(d_0+d_1r+d_2r^2)/7.
\]
Their source substitutions have total degree at most four in r,x; their
coefficient identities have one free variable x.

Write \(49w=W_0+W_1r+W_2r^2+W_3r^3+W_4r^4\). This identity is used only
as univariate polynomial arithmetic in r. Its five coefficient identities are
\[
\begin{aligned}
 W_0&=36+u d_0^2-6d_0E_0,\\
 W_1&=d_1(2u d_0-6E_0),\\
 W_2&=12-6S+u(d_1^2+2d_0d_2)-6d_2E_0-d_0J_2,\\
 W_3&=d_1(2u d_2-J_2),\\
 W_4&=(S-d_2)(A_0-u d_2).
\end{aligned}
\tag{3}
\]
Here are all five expanded two-variable numerators, with \(289S W_i=U_i(x,u)\).
No product with the outer powers of r is expanded in x,u,r.

\[
\begin{aligned}
U_0(x,u)={}&- 3366 u x^{2} + 3366 x^{2} - 5643 u x + 17136 x\\
&{}- 2277 u + 10404
\end{aligned}
\]
This polynomial has 6 monomials, total degree 3, and largest cleared coefficient 17136.

\[
\begin{aligned}
U_1(x,u)={}&- 1836 u x^{3} + 1836 x^{3} - 852 u x^{2} + 2040 x^{2}\\
&{}+ 1560 u x - 3264 x + 576 u
\end{aligned}
\]
This polynomial has 7 monomials, total degree 4, and largest cleared coefficient 3264.

\[
\begin{aligned}
U_2(x,u)={}&3468 u x^{4} - 3468 x^{4} - 84 u x^{3} - 1836 x^{3}\\
&{}- 8223 u x^{2} + 9639 x^{2} - 5588 u x + 2907 x\\
&{}- 917 u + 1173
\end{aligned}
\]
This polynomial has 10 monomials, total degree 5, and largest cleared coefficient 9639.

\[
\begin{aligned}
U_3(x,u)={}&- 1224 u x^{4} + 1358 u x^{3} - 306 x^{3} + 1560 u x^{2}\\
&{}- 34 x^{2} - 1294 u x - 34 x - 272 u\\
&{}+ 272
\end{aligned}
\]
This polynomial has 9 monomials, total degree 5, and largest cleared coefficient 1560.

\[
\begin{aligned}
U_4(x,u)={}&1156 u x^{5} - 1666 u x^{4} + 578 x^{4} - 1750 u x^{3}\\
&{}+ 17 x^{3} + 1633 u x^{2} + 17 x^{2} + 561 u x\\
&{}- 561 x
\end{aligned}
\]
This polynomial has 9 monomials, total degree 6, and largest cleared coefficient 1750.

The pairing is only quadratic in r:
\[
 E_L=\frac{2u d_0-6E_0+2u d_1r+(2u d_2-J_2)r^2}{7}.
 \tag{4}
\]
The Casimir has the coefficient-preserving representation
\[
 \Gamma_*=\gamma_0+\gamma_2r^2+\gamma_4r^4,
\quad
 \gamma_0=u/4-E_0^2/16,
\quad
 \gamma_2=\frac{4(2-S)u-2E_0J_2}{96},
\quad
 \gamma_4=-\frac{(Su-A_0)^2}{576}\le0.
 \tag{5}
\]
For the last square the polynomial being squared, after clearing S, is
\(ux^2+2ux+u-x^2-x-1\), with six monomials and degree three.
The source coefficient identity for \(\gamma_4\) is
\[
 4u(S^2-S+1)-(Su+A_0)^2=-(Su-A_0)^2,
 \qquad SA_0=S^2-S+1.
\]
It is the two-variable identity \(4UV-(U+V)^2=-(U-V)^2\), after retaining
\(U=Su,V=A_0\). The other coefficients in (4)--(5) follow by the ordinary
product rule for polynomials of degree two in r. Their two-variable numerator
checks in x,u have degree at most six.

Remove the unchanged logarithm term by setting
\(Q=F_1+(7/96)\ell(2Z/7)\). By the original residual identity,
\[
 Q=\Gamma_*-\frac7{96}
 \left[\frac67+(u-1)Z-E_L+\frac{7w-17/4}{Z}\right]-g.
 \tag{6}
\]
Only the quadratic and higher powers of r affect its second derivative.

Here is the generic division rule used to avoid a global expansion. For a
quartic \(W(r)=\sum_{i=0}^4W_i r^i\), division by \(d+er\) has cubic
coefficient \(W_4/e\), quadratic coefficient \(W_3/e-dW_4/e^2\), and
remainder \(W(-d/e)\). This follows term by term from
\[
 r^n-\xi^n=(r-\xi)\sum_{j=0}^{n-1}r^{n-1-j}\xi^j
 \qquad(1\le n\le4),\qquad\xi=-d/e.
 \tag{7}
\]
Each identity (7) has degree at most four in two variables; the product on its
right has at most eight monomial contributions before collection. Its scalar
coefficient factors are kept outside. Differentiating the quotient twice
annihilates its constant and linear terms.

Consequently
\[
 Q_{rr}=12\gamma_4r^2+6b_3r+2b_2+\frac{2e^2R}{Z^3},
 \tag{8}
\]
where the source interfaces for the three remaining coefficients are
\[
\begin{aligned}
 b_3&=-\frac{W_4}{96e},\\
 b_2&=\frac{4(2-S)u-2E_0J_2+2u d_2-J_2}{96}
       -\frac{W_3}{96e}+\frac{dW_4}{96e^2},\\
 R&=-\frac1{96}\left[W_0-\frac{119}{4}
 -\frac d eW_1+\frac{d^2}{e^2}W_2
 -\frac{d^3}{e^3}W_3+\frac{d^4}{e^4}W_4\right].
\end{aligned}
\tag{9}
\]
These are checked separately after setting the norm endpoint. Each check is
univariate in x and has degree at most six. The complete endpoint polynomials
are given next.

## 2. The cubic coefficient and remainder are negative

For \(u=3/4\),
\[
 b_3=-\frac{x(34x-33)(102x^3+20x^2-133x+17)}{6528S(17x-8)},
 \qquad
 b_2=\frac{B_f(x)}{13056S^2(17x-8)^2},
 \qquad R=\frac{R_f(x)}{384S(17x-8)^4}.
 \tag{10}
\]
For \(u=19/25\),
\[
 b_3=-\frac{x(34x-33)(646x^3+121x^2-848x+102)}{40800S(17x-8)},
 \qquad
 b_2=\frac{B_v(x)}{510000S^2(17x-8)^2},
 \qquad R=\frac{R_v(x)}{9600S(17x-8)^4}.
 \tag{11}
\]
Both displayed b3 numerator products have five monomials after expansion and
degree five. With \(z=x-1\in[0,1/2]\), their cubic factors are exactly
\[
\begin{aligned}
102x^3+20x^2-133x+17&=102z^3+326z^2+213z+6,\\
646x^3+121x^2-848x+102&=646z^3+2059z^2+1332z+21.
\end{aligned}
\tag{12}
\]
Each has four monomials and degree three. This proves \(b_3<0\).
The other complete numerators are:

\[
\begin{aligned}
B_f(x)={}&214727 x^{6} - 44302 x^{5} - 520588 x^{4} + 193724 x^{3}\\
&{}+ 214209 x^{2} - 65634 x + 5440
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 520588.

\[
\begin{aligned}
R_f(x)={}&1975026 x^{6} - 7221532 x^{5} - 3269729 x^{4} + 23644974 x^{3}\\
&{}- 20302414 x^{2} + 5261025 x -468416
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 23644974.

\[
\begin{aligned}
R_f(1+z)={}&1975026 z^{6} + 4628624 z^{5} - 9751999 z^{4} - 22148742 z^{3}\\
&{}- 11575796 z^{2} - 1745301 z -381066
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 22148742.

\[
\begin{aligned}
B_v(x)={}&8435332 x^{6} - 1970708 x^{5} - 20734420 x^{4} + 7702440 x^{3}\\
&{}+ 8629280 x^{2} - 2555283 x + 205632
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 20734420.

\[
\begin{aligned}
R_v(x)={}&47400624 x^{6} - 180594077 x^{5} - 73567245 x^{4} + 592675520 x^{3}\\
&{}- 512832600 x^{2} + 131210264 x -11459072
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 592675520.

\[
\begin{aligned}
R_v(1+z)={}&47400624 z^{6} + 103809667 z^{5} - 265528270 z^{4} - 559521750 z^{3}\\
&{}- 271140920 z^{2} - 29263997 z -7166586
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 559521750.

The only positive terms in either shifted R polynomial have powers six and
five. Use \(z^6\le z^4/4\) and \(z^5\le z^4/2\). Their combined coefficients
are smaller than the magnitude of the negative quartic coefficient:
\[
 1975026/4+4628624/2<9751999,
 \qquad47400624/4+103809667/2<265528270.
\]
Every remaining coefficient is negative. Therefore \(R<0\) at both norm
endpoints, throughout the interval in (1).

## 3. Reduce the second derivative to two small x-polynomials

The domain gives \(2\le Z\le S\). By the logarithm derivative inequality
\(\ell''(y)\ge-1/y^2\) from the beta note,
\[
 (F_1)_{rr}\le Q_{rr}+\frac7{96}\frac{e^2}{Z^2}.
\]
Use \(\gamma_4\le0\), \(b_3<0\), \(r\ge1/x\), \(R<0\), and
\(2\le Z\le S\), in that order. The resulting upper bound is
\[
 (F_1)_{rr}\le\mathcal H(x):=
 \frac{6b_3}{x}+2b_2+\frac{2e^2R}{S^3}+\frac7{384}e^2.
 \tag{13}
\]
The x factor in b3 is canceled before any denominator clearing.
At the two norm endpoints,
\[
 \mathcal H(x)=
 \begin{cases}
 H_f(z)/[110976S^4(17x-8)],&u=3/4,\\
 H_v(z)/[69360000S^4(17x-8)],&u=19/25,
 \end{cases}
 \qquad z=x-1.
 \tag{14}
\]
\[
\begin{aligned}
H_f(z)={}&- 104618 z^{7} - 944350 z^{6} - 3078173 z^{5} - 5115909 z^{4}\\
&{}- 5655650 z^{3} - 3066570 z^{2} - 473814 z -26244
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 5655650.

\[
\begin{aligned}
H_v(z)={}&- 67573113 z^{7} - 612084507 z^{6} - 2020804467 z^{5} - 3435750315 z^{4}\\
&{}- 3860747930 z^{3} - 2142156386 z^{2} - 362867574 z -25280964
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 3860747930.

Every printed coefficient of both H polynomials is negative. Hence
\((F_1)_{rr}<0\) on (1). Concavity gives
\[
 F_1\bigl(x,a,x+\tfrac8{17}(a-1),u\bigr)
 \ge\min\{F_1(x,1,x,u),\ F_1(x,x,x+\tfrac8{17}(x-1),u)\}.
 \tag{15}
\]
This removes the shape variable before any terminal sign check.

## 4. Expansion audit and interface limits

The five transport coefficient identities (3) have at most ten monomials and
degree six in x,u. Their generic convolution in r is not expanded in x,u,r.
The endpoint identities (9) have at most seven monomials and degree six in x.
Their largest coefficient before collecting separate source contributions is
171283225280, twelve digits. For (13)--(14), use the common positive denominator
proportional to \(S^4(17x-8)^2\). Each of the four source contributions, and the
target \((17x-8)H_i\), then has at most nine monomials and degree eight in x
or z. The largest coefficient before collection is 318887547000, twelve digits.
Thus the canceled extra factor in (14) does not hide a larger-degree identity.

The proof requires no expansion of the entire rational F1 numerator and no
identity in the three free variables x,r,u of degree greater than four.
The sign premises are the printed univariate b3 factors, R polynomials, and
H polynomials, together with the explicit square in (5).
