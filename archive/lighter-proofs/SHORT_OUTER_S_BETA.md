# The S1 outer S branch: norm, transported norm, and beta reductions

This note proves two reductions for the S branch of
[MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md).
They are proved on the enlarged domain
\[
 1\le a\le x\le\frac32,\qquad x\le\beta\le ax,
 \qquad \frac34\le u\le\frac{19}{25}.
 \tag{1}
\]
The conclusions are
\[
 w>\frac34,\qquad
 (F_1)_\beta\ge-\frac7{2400}.
 \tag{2}
\]
Consequently, for \(8/17\le C\le10/13\) and \(\beta=x+C(a-1)\),
\[
 \boxed{F_0\ge F_1\ge
 F_1\bigl(x,a,x+\tfrac8{17}(a-1),u\bigr)-\frac{77}{176800}.}
 \tag{3}
\]
The [reciprocal-shape](SHORT_OUTER_S_RECIPROCAL.md) and
[terminal-face](SHORT_OUTER_S_TERMINAL.md) companions supply the fixed-slope
sign and close this S branch. These derivative estimates are subordinate
reductions; they do not replace the other S1 branches.

## 1. Exact source and the uniform incoming interval

Set \(S=x+1\), \(B=a+\beta\), \(c=7/96\), \(g=9193/50000\), and
\[
\begin{gathered}
 K=6a^2+1,\qquad D=a^2+2a\beta+1+2x-2\beta x,\\
 E_0=S(u-1)+1/S,\qquad J=KE_0+2S-1,
 \qquad M=K^2-SK+S^2,\\
 w=\frac{M+uD^2-DJ}{49a^4},\qquad
 E_L=\frac{2Du-J}{7a^2},\qquad
 \Gamma_* =\frac{4uM-J^2}{576a^4},\\
 T=\frac{7a}{B},\qquad y=\frac{2B}{7a},\qquad
 \ell(y)=\frac{8(y^3-1)}{3(y+1)^3},\\
 \overline R_2=2w-\frac12+(u-1)\frac Ba+\frac aB-\frac17-E_L+\ell(y),\\
 R_1=\overline R_2+(T-2)(w-3/4),\qquad
 F_i=\Gamma_*-cR_i-g\quad(i=0,1),\qquad R_0=\overline R_2.
\end{gathered}
\tag{4}
\]
These are exactly the original rational tests, with the same cubic logarithm
majorant. The display is a factored arithmetic circuit; a global expansion in
\(x,a,\beta,u\) is neither needed nor allowed in this proof.

The logarithm estimate \(\log y\le\ell(y)\) is valid for \(0<y\le1\).
Here \(4/7\le y\le5/7\). Its derivative identities are
\[
\begin{aligned}
\ell'(y)&=\frac{8(y^2+1)}{(y+1)^4},\qquad
\ell''(y)=-\frac{16(y^2-y+2)}{(y+1)^5},\\
\ell'(y)-1/y&=-\frac{(y-1)^4}{y(y+1)^4},\\
\ell''(y)+1/y^2&=
 \frac{(1-y)^3(1+8y-y^2)}{y^2(y+1)^5}\ge0.
\end{aligned}
\tag{5}
\]
The two cleared error numerators are respectively
\[
 -y^4+4y^3-6y^2+4y-1,
 \qquad y^5-11y^4+26y^3-22y^2+5y+1.
\]
They have five and six monomials and degrees four and five. Positivity in the
second identity follows from the printed factors, since \(0<y\le1\).

The actual norm lies between \(u_f\) and \(u_v\) from the original note.
The lower bound is at least \(3/4\), and
\[
 u_v-\frac34=\frac{2(x-1)^2}{(x+1)(35x+13)}
 \le\frac1{192}<\frac1{100}.
\]
Thus (1) contains the full original S norm interval. Also
\(\beta\le ax\), since \(C\le10/13<1\le x\).

Both tests are concave in the norm:
\[
 (F_i)_{uu}=-\frac{K^2S^2}{288a^4}<0.
 \tag{6}
\]
The complete numerator is
\[
 K^2S^2=36a^4x^2+72a^4x+36a^4
 +12a^2x^2+24a^2x+12a^2+x^2+2x+1.
\]
This identity has nine monomials and total degree six in \(a,x\).
Hence a lower bound for \(F_1\) at \(u=3/4,19/25\) gives the same lower bound
throughout the norm interval.

For every subsequent two-variable certificate put
\[
 A=a-1,\qquad X=x-a,\qquad 0\le A,X\le\frac12.
 \tag{7}
\]
We use the containing square in (7); no further subdivision is required.

## 2. A positive transported pairing and a norm floor

First, \(0<D\le4a^2\). For the lower bound, decrease D by increasing beta to ax.
The complete identity there is
\[
 D(x,a,ax)=A^2(1-2X)+A(4-4X-2X^2)+4-2X^2\ge\frac72.
 \tag{8}
\]
Its expanded polynomial has seven monomials and degree three. For the upper bound,
\[
\begin{aligned}
4a^2-D&\ge3a^2-2ax-1-2x+2x^2\\
&=(a-1)(3a+3-2x)+2(x-1)^2\ge0.
\end{aligned}
\tag{9}
\]
The expanded polynomial has six monomials and degree two.
Since \(S\ge2\), this proves
\[
 (E_L)_u=\frac{2D-KS}{7a^2}\le-\frac47,
 \qquad (E_L)_\beta=\frac{4u(a-x)}{7a^2}\le0.
\]
The minimum of \(E_L\) is therefore bounded by setting \(u=19/25,\beta=ax\).
At that point,
\[
 E_L=\frac{P_E(A,X)}{175a^2S}.
 \tag{10}
\]
\[
\begin{aligned}
P_E(A,X)={}&36 A^{4} - 4 A^{3} X + 254 A^{3} - 116 A^{2} X^{2}\\
&{}+ 22 A^{2} X + 502 A^{2} - 76 A X^{3} - 308 A X^{2}\\
&{}+ 120 A X + 437 A - 76 X^{3} - 160 X^{2}\\
&{}+ 145 X + 147
\end{aligned}
\]
This polynomial has 14 monomials, total degree 4, and largest cleared coefficient 502.

Using \(X\le1/2\) only in negative terms gives
\[
 P_E\ge36A^4+252A^3+473A^2+\frac{701}{2}A+\frac{195}{2}>0.
\]
For example, the coefficient of A is at least
\(437-308/4-76/8=701/2\); the constant group is at least
\(147-160/4-76/8=195/2\). Thus \(E_L>0\) throughout (1).

Differentiating the factored transport now gives
\[
 w_\beta=\frac{2(a-x)}{7a^2}E_L\le0,
 \qquad w_u=\frac{D(D-KS)}{49a^4}<0.
\]
Therefore it suffices to lower-bound w at \(\beta=ax,u=19/25\). There
\[
 w-\frac34=\frac{P_w(A,X)}{4900a^4S}.
 \tag{11}
\]
\[
\begin{aligned}
P_w(A,X)={}&- 288 A^{6} X + 144 A^{6} - 560 A^{5} X^{2} - 2320 A^{5} X\\
&{}+ 1441 A^{5} + 48 A^{4} X^{3} - 4112 A^{4} X^{2} - 5775 A^{4} X\\
&{}+ 4838 A^{4} + 624 A^{3} X^{4} - 80 A^{3} X^{3} - 10144 A^{3} X^{2}\\
&{}- 5572 A^{3} X + 7454 A^{3} + 304 A^{2} X^{5} + 2176 A^{2} X^{4}\\
&{}- 1008 A^{2} X^{3} - 11928 A^{2} X^{2} - 1162 A^{2} X + 5832 A^{2}\\
&{}+ 608 A X^{5} + 2224 A X^{4} - 1992 A X^{3} - 6868 A X^{2}\\
&{}+ 1420 A X + 2289 A + 304 X^{5} + 672 X^{4}\\
&{}- 1060 X^{3} - 1404 X^{2} + 729 X + 370
\end{aligned}
\]
This polynomial has 32 monomials, total degree 7, and largest cleared coefficient 11928.

The groups multiplying \(A^6,A^5,A^4,A^3,A^2,A\) are bounded below by
\(0,141,1845/2,2122,2143,323\), respectively, using \(X\le1/2\) in
negative terms and discarding positive terms. The constant group satisfies
\[
370+729X-1404X^2-1060X^3+672X^4+304X^5
\ge370-238X\ge251.
\]
Thus
\[
 P_w\ge251+323A+2143A^2+2122A^3+\frac{1845}{2}A^4+141A^5>0,
\]
which proves \(w>3/4\). Since \(T\ge14/5>2\), it follows that \(F_0\ge F_1\).

## 3. Beta concavity on the enlarged constant norm interval

This argument proves the extension to (1) directly. It does not invoke a beta
lemma that requires \(u\le u_0(x)\), which would fail near \(x=1\) for the
constant upper endpoint \(19/25\).

Let \(D_0=D|_{\beta=-a}=(a+1)(2x+1-a)\) and \(w_0=w|_{\beta=-a}\).
This is a coefficient evaluation of the quadratic transport, not a comparison
point asserted to satisfy the actual beta domain. We have \(D_0>0\) and
\[
 KS-D_0=6a^2x+7a^2-2ax-x\ge3x+7>0.
\]
This polynomial has four monomials and degree three. Hence
\((w_0)_u=D_0(D_0-KS)/(49a^4)<0\). At \(u=19/25\),
\[
 w_0-\frac{19+2x}{28}=\frac{P_0(A,X)}{4900a^4S}.
 \tag{12}
\]
\[
\begin{aligned}
P_0(A,X)={}&- 206 A^{6} - 124 A^{5} X - 659 A^{5} + 370 A^{4} X^{2}\\
&{}+ 1413 A^{4} X - 62 A^{4} + 288 A^{3} X^{3} + 3528 A^{3} X^{2}\\
&{}+ 7036 A^{3} X + 1854 A^{3} + 1456 A^{2} X^{3} + 9428 A^{2} X^{2}\\
&{}+ 11534 A^{2} X + 2682 A^{2} + 2304 A X^{3} + 10316 A X^{2}\\
&{}+ 8440 A X + 1589 A + 1188 X^{3} + 4174 X^{2}\\
&{}+ 2381 X + 370
\end{aligned}
\]
This polynomial has 22 monomials, total degree 6, and largest cleared coefficient 11534.

Only four terms in this polynomial are negative. Using \(A,X\le1/2\),
\[
 -206A^6-124A^5X-659A^5-62A^4\ge-237A^3.
\]
They are absorbed by \(1854A^3\); every other coefficient is positive.
Thus \(P_0\ge370>0\), and
\[
 w_0>\frac{19+2x}{28}
 \quad\hbox{for every }3/4\le u\le19/25.
 \tag{13}
\]

The original residual has the factor-preserving identity
\[
 R_1=\frac aB(7w-17/4)+(u-1)\frac Ba-E_L+\ell(y)+\frac67.
 \tag{14}
\]
Write the quadratic w as \(w=w_2B^2+w_1B+w_0\); its leading coefficient is
\(w_2=4u(x-a)^2/(49a^4)\). The affine terms disappear after two beta derivatives.
Using (5),
\[
 (R_1)_{\beta\beta}
 \ge\frac{a(14w_0-17/2)-B}{B^3}
 >\frac{ax-\beta}{B^3}\ge0.
 \tag{15}
\]
This reduces the first derivative to the upper beta face \(\beta=ax\).

## 4. A small derivative loss replaces the whole slope interval

The same quadratic division gives
\[
 (R_1)_\beta=
 \frac{4ux(x-a)}{7a^3}+\frac{u-1}{a}+\ell'(y)\frac2{7a}
 -\frac{a(7w_0-17/4)}{B^2}.
\]
By (5) and (15),
\[
 (R_1)_\beta\le\mathcal R(x,a,u):=
 \frac{4ux(x-a)}{7a^3}+\frac{u-1}{a}+\frac1{aS}
 -\frac{7w_0-17/4}{aS^2}.
 \tag{16}
\]
The right side is affine in u. Its derivative has the identity
\[
 \mathcal R_u=\frac{N_u(A,X)}{7a^5S^3}.
 \tag{17}
\]
\[
\begin{aligned}
N_u(A,X)={}&7 A^{7} + 25 A^{6} X + 76 A^{6} + 37 A^{5} X^{2}\\
&{}+ 228 A^{5} X + 353 A^{5} + 31 A^{4} X^{3} + 272 A^{4} X^{2}\\
&{}+ 865 A^{4} X + 909 A^{4} + 16 A^{3} X^{4} + 172 A^{3} X^{3}\\
&{}+ 794 A^{3} X^{2} + 1740 A^{3} X + 1399 A^{3} + 4 A^{2} X^{5}\\
&{}+ 60 A^{2} X^{4} + 350 A^{2} X^{3} + 1135 A^{2} X^{2} + 1941 A^{2} X\\
&{}+ 1282 A^{2} + 8 A X^{5} + 72 A X^{4} + 302 A X^{3}\\
&{}+ 777 A X^{2} + 1124 A X + 644 A + 4 X^{5}\\
&{}+ 28 X^{4} + 91 X^{3} + 198 X^{2} + 260 X\\
&{}+ 136
\end{aligned}
\]
This polynomial has 33 monomials, total degree 7, and largest cleared coefficient 1941.

All its coefficients are positive. Hence raise u to \(19/25\).
The final two-variable identity is
\[
 \frac1{25}-\mathcal R(x,a,19/25)
 =\frac{P_\beta(A,X)}{700a^5S^3}.
 \tag{18}
\]
\[
\begin{aligned}
P_\beta(A,X)={}&28 A^{8} + 84 A^{7} X + 476 A^{7} + 84 A^{6} X^{2}\\
&{}+ 956 A^{6} X + 2580 A^{6} + 28 A^{5} X^{3} - 124 A^{5} X^{2}\\
&{}+ 3328 A^{5} X + 7461 A^{5} - 1516 A^{4} X^{3} - 4092 A^{4} X^{2}\\
&{}+ 6165 A^{4} X + 13266 A^{4} - 1216 A^{3} X^{4} - 8792 A^{3} X^{3}\\
&{}- 13224 A^{3} X^{2} + 7400 A^{3} X + 14594 A^{3} - 304 A^{2} X^{5}\\
&{}- 4560 A^{2} X^{4} - 17320 A^{2} X^{3} - 16860 A^{2} X^{2} + 6058 A^{2} X\\
&{}+ 9556 A^{2} - 608 A X^{5} - 5472 A X^{4} - 14212 A X^{3}\\
&{}- 8728 A X^{2} + 3292 A X + 3437 A - 304 X^{5}\\
&{}- 2128 X^{4} - 4088 X^{3} - 1080 X^{2} + 901 X\\
&{}+ 538
\end{aligned}
\]
This polynomial has 37 monomials, total degree 8, and largest cleared coefficient 17320.

Each group in powers of A has a direct lower bound from \(X\le1/2\):
\[
\begin{aligned}
 P_\beta\ge{}&28A^8+476A^7+2580A^6+7430A^5
 +\frac{24107}{2}A^4+10113A^3\\
 &+\frac{5763}{2}A^2+\frac{1527}{2}A+65>0.
\end{aligned}
\tag{19}
\]
For the A and constant groups, first use \(X^j\le X/2^{j-1}\) for \(j\ge2\).
They become at least \(3437-5347X\ge1527/2\) and
\(538-946X\ge65\), respectively. The remaining groups follow by substituting
\(X=1/2\) only into negative terms. The lower polynomial in (19) has nine
monomials and degree eight in one variable.

Thus \((R_1)_\beta<1/25\), so \((F_1)_\beta>-7/2400\).
Integrating this derivative between
\(\beta_0=x+(8/17)(a-1)\) and \(\beta=x+C(a-1)\) yields
\[
 F_1(x,a,\beta,u)\ge F_1(x,a,\beta_0,u)
 -\frac7{2400}\Bigl(C-\frac8{17}\Bigr)(a-1)
 \ge F_1(x,a,\beta_0,u)-\frac{77}{176800}.
\]
This proves (2)--(3). It replaces an exact slope monotonicity claim by a
quantified loss; the terminal companion supplies a \(1/1000\) margin before the loss.

## 5. Expansion audit

Every source-to-certificate identity above is taken after the norm and beta
substitutions specified beside it. The only free variables are A and X.
The largest certificate is \(P_\beta\), with 37 monomials and total degree eight.
All printed coefficient bounds are below 20000. The signs in (5) and the norm
concavity identity are separate one- and two-variable checks.

The factored source formulas (4), quadratic division in (14)--(16), and generic
product differentiation are algebraic interfaces; no four-variable clearing
identity is asserted. In particular, retain the displayed outer positive
denominators and products when using (10)--(18).
