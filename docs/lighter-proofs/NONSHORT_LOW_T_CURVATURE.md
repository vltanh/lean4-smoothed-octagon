# Low-t unit residual: positive second derivative in h

## Scope

This note proves derivative lemmas for the residual `G_n` defined in
[the shape note](NONSHORT_LOW_T_SHAPE.md). They are components of the
[completed first-priority caller replacement](NONSHORT_LOW_T_CALLER.md).

Put
\[
 h=1-2t,\quad j=x-h,\quad q=1+y,\quad
 W=1+x,\quad D=17x+76,
\]
and
\[
 S(t,x,q)=96q(q+1)W^3D\,G_n(t,x,q,1).
\]
The directional derivative at fixed \(j,y\) is
\(\mathcal H=\partial_x-\tfrac12\partial_t\).

**Claim.** On
\[
 \frac14\le h\le\frac13,\quad
 \frac1{30}\le j\le\frac5{21},\quad
 0\le y\le\frac9{32},\quad x=h+j\le\frac47,
 \tag{C1}
\]
we have \(\mathcal H^2S>0\). In particular this holds on the original low-t domain.

The proof first establishes \(\mathcal H^3S>0\) on the larger rectangle
\(1/3\le t\le3/8\), \(1/4\le x\le4/7\), \(0\le y\le1/3\).
It then checks \(\mathcal H^2S>0\) on \(h=1/4\), where only \(x,y\) remain.
Every expansion below is bivariate of degree at most 8 or univariate of degree at most 7.

## 1. A source interface that cancels W before differentiation

Keep the event variable \(q\) opaque when checking coefficients.
For free incoming scalar \(v\) and logarithm scalar \(\ell\), use the same
residual as in the shape note, with the floor expression
\(1+p^2q/W^2-pq\ell/(W(q-1))-v\).
Here \(p=t+x\), \(B_s=1+2tx+x^2\), \(J=t+x(x+2)\),
\(a=27/2-10q\), and \(m=16t+8x+8q-97/6\).
The affine residual is
\[
 G(v,\ell)=\frac{C}{4qW^2}+\frac{A}{qW}v
       -\frac{pqB}{W(q-1)}\ell.
 \tag{C2}
\]
This is an algebraic interface for \(q>1\); after substituting the fixed
rational logarithm bound, its removable value at \(q=1\) is used.
Write \(A=\sum_{i=0}^4 A_iq^i\), \(B=\sum_{i=0}^3B_iq^i\),
and \(C=\sum_{i=0}^5 C_iq^i\). Their complete coefficients follow.
The checks of (C2) are made one coefficient of \(q\) at a time.
The numerator for the \(v\) coefficient has the visible factor \(W\);
its cancellation is a bivariate identity of degree at most 7.

\[
\begin{aligned}
A_{0}={}&t^{2} x^{4} + 4 t^{2} x^{3} + 6 t^{2} x^{2} + 4 t^{2} x\\
&{}+t^{2} + t x^{5} + 4 t x^{4} + 6 t x^{3}\\
&{}+4 t x^{2} + t x
\end{aligned}
\]
This displayed polynomial has 10 monomials and total degree 6.
\[
\begin{aligned}
A_{1}={}&\frac{1}{6}\bigl[- 6 t^{2} x^{3} - 18 t^{2} x^{2} - 18 t^{2} x - 6 t^{2}\\
&{}- 6 t x^{5} - 30 t x^{4} - 54 t x^{3} - 42 t x^{2}\\
&{}- 108 t x - 96 t - 48 x^{2} + 49 x\\
&{}+97\bigr]
\end{aligned}
\]
This displayed polynomial has 13 monomials and total degree 6.
\[
\begin{aligned}
A_{2}={}&\frac{1}{2}\bigl[- 4 t^{2} x^{4} + 42 t^{2} x^{3} + 96 t^{2} x^{2} + 50 t^{2} x\\
&{}+25 t x^{5} + 129 t x^{4} + 154 t x^{3} + 19 t x^{2}\\
&{}- 33 t x - 2 t + 27 x^{3} + 54 x^{2}\\
&{}+11 x - 16\bigr]
\end{aligned}
\]
This displayed polynomial has 14 monomials and total degree 6.
\[
\begin{aligned}
A_{3}={}&\frac{1}{2}\bigl[- 36 t^{2} x^{3} - 68 t^{2} x^{2} - 32 t^{2} x - 45 t x^{5}\\
&{}- 225 t x^{4} - 320 t x^{3} - 120 t x^{2} + 22 t x\\
&{}+2 t - 47 x^{3} - 121 x^{2} - 74 x\bigr]
\end{aligned}
\]
This displayed polynomial has 12 monomials and total degree 6.
\[
\begin{aligned}
A_{4}={}&- 2 t^{3} x + t^{2} x^{4} + t^{2} x^{3} - 3 t^{2} x^{2}\\
&{}+t^{2} x + 10 t x^{5} + 49 t x^{4} + 79 t x^{3}\\
&{}+43 t x^{2} + t x + 10 x^{3} + 30 x^{2}\\
&{}+20 x
\end{aligned}
\]
This displayed polynomial has 13 monomials and total degree 6.
\[
\begin{aligned}
B_{0}={}&\frac{1}{6}\bigl[- 174 t^{2} x^{3} - 348 t^{2} x^{2} - 174 t^{2} x - 87 t x^{4}\\
&{}- 174 t x^{3} - 174 t x^{2} - 174 t x + 9 t\\
&{}+48 x - 97\bigr]
\end{aligned}
\]
This displayed polynomial has 10 monomials and total degree 5.
\[
\begin{aligned}
B_{1}={}&\frac{1}{2}\bigl[98 t^{2} x^{3} + 196 t^{2} x^{2} + 98 t^{2} x + 49 t x^{4}\\
&{}+98 t x^{3} + 98 t x^{2} + 98 t x + 49 t\\
&{}+16\bigr]
\end{aligned}
\]
This displayed polynomial has 9 monomials and total degree 5.
\[
\begin{aligned}
B_{2}={}&2 t^{3} x - 18 t^{2} x^{3} - 35 t^{2} x^{2} - 20 t^{2} x\\
&{}+t^{2} - 9 t x^{4} - 18 t x^{3} - 19 t x^{2}\\
&{}- 18 t x - 10 t
\end{aligned}
\]
This displayed polynomial has 10 monomials and total degree 5.
\[
\begin{aligned}
B_{3}={}&- 2 t^{3} x - 2 t^{2} x^{3} - 5 t^{2} x^{2} - t^{2}\\
&{}- t x^{4} - 2 t x^{3} - t x^{2} - 2 t x
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 5.
\[
\begin{aligned}
C_{0}={}&3\bigl[- t^{2} x^{5} - 5 t^{2} x^{4} - 10 t^{2} x^{3} - 10 t^{2} x^{2}\\
&{}- 5 t^{2} x - t^{2} - t x^{6} - 5 t x^{5}\\
&{}- 10 t x^{4} - 10 t x^{3} - 5 t x^{2} - t x\bigr]
\end{aligned}
\]
This displayed polynomial has 12 monomials and total degree 7.
\[
\begin{aligned}
C_{1}={}&\frac{1}{3}\bigl[- 138 t^{3} x^{4} - 552 t^{3} x^{3} - 828 t^{3} x^{2} - 552 t^{3} x\\
&{}- 138 t^{3} - 276 t^{2} x^{5} - 1095 t^{2} x^{4} - 1620 t^{2} x^{3}\\
&{}- 1050 t^{2} x^{2} - 240 t^{2} x + 9 t^{2} - 129 t x^{6}\\
&{}- 498 t x^{5} - 702 t x^{4} - 408 t x^{3} + 135 t x^{2}\\
&{}+402 t x + 192 t + 96 x^{3} - 2 x^{2}\\
&{}- 292 x - 194\bigr]
\end{aligned}
\]
This displayed polynomial has 22 monomials and total degree 7.
\[
\begin{aligned}
C_{2}={}&\frac{2}{3}\bigl[- 186 t^{4} x^{3} - 384 t^{4} x^{2} - 210 t^{4} x - 12 t^{4}\\
&{}- 441 t^{3} x^{4} - 603 t^{3} x^{3} + 315 t^{3} x^{2} + 675 t^{3} x\\
&{}+294 t^{3} - 153 t^{2} x^{5} + 372 t^{2} x^{4} + 1416 t^{2} x^{3}\\
&{}+1008 t^{2} x^{2} + 261 t^{2} x - 193 t^{2} + 15 t x^{6}\\
&{}+243 t x^{5} + 456 t x^{4} + 240 t x^{3} + 207 t x^{2}\\
&{}- 185 t x + 6 t - 81 x^{4} - 195 x^{3}\\
&{}- 292 x^{2} + 15 x + 48\bigr]
\end{aligned}
\]
This displayed polynomial has 27 monomials and total degree 7.
\[
\begin{aligned}
C_{3}={}&2\bigl[52 t^{4} x^{3} + 110 t^{4} x^{2} + 64 t^{4} x + 6 t^{4}\\
&{}+281 t^{3} x^{4} + 594 t^{3} x^{3} + 288 t^{3} x^{2} - 82 t^{3} x\\
&{}- 57 t^{3} + 202 t^{2} x^{5} + 238 t^{2} x^{4} - 204 t^{2} x^{3}\\
&{}- 262 t^{2} x^{2} + 30 t^{2} x + 68 t^{2} + 46 t x^{6}\\
&{}+74 t x^{5} + 77 t x^{4} + 122 t x^{3} + 77 t x^{2}\\
&{}+34 t x - 2 t + 47 x^{4} + 168 x^{3}\\
&{}+211 x^{2} + 74 x\bigr]
\end{aligned}
\]
This displayed polynomial has 26 monomials and total degree 7.
\[
\begin{aligned}
C_{4}={}&8 t^{5} x - 8 t^{4} x^{3} - 12 t^{4} x^{2} - 40 t^{4} x\\
&{}- 4 t^{4} - 232 t^{3} x^{4} - 576 t^{3} x^{3} - 444 t^{3} x^{2}\\
&{}- 24 t^{3} x + 28 t^{3} - 203 t^{2} x^{5} - 335 t^{2} x^{4}\\
&{}+10 t^{2} x^{3} + 182 t^{2} x^{2} - 31 t^{2} x - 39 t^{2}\\
&{}- 55 t x^{6} - 127 t x^{5} - 178 t x^{4} - 206 t x^{3}\\
&{}- 111 t x^{2} - 3 t x - 40 x^{4} - 160 x^{3}\\
&{}- 200 x^{2} - 80 x
\end{aligned}
\]
This displayed polynomial has 26 monomials and total degree 7.
\[
\begin{aligned}
C_{5}={}&- 4 t^{4} x^{2} - 4 t^{3} x^{4} - 12 t^{3} x^{3} - 4 t^{3} x\\
&{}- 4 t^{2} x^{5} - 9 t^{2} x^{4} - 4 t^{2} x^{3} - 10 t^{2} x^{2}\\
&{}- t^{2} - t x^{6} - 2 t x^{5} - 2 t x^{4}\\
&{}- 4 t x^{3} - t x^{2} - 2 t x
\end{aligned}
\]
This displayed polynomial has 15 monomials and total degree 7.
\[
\begin{aligned}
V_n={}&408 t^{2} x^{2} + 2232 t^{2} x + 1824 t^{2} + 401 t x^{2}\\
&{}- 1320 t x - 1824 t + 408 x^{3} + 1831 x^{2}\\
&{}+3144 x + 1824
\end{aligned}
\]
This displayed polynomial has 10 monomials and total degree 4.
The incoming and logarithm substitutions are
\[
 V_L=\frac{V_n}{24W^2D},\qquad
 L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
Consequently the positive normalization is the following **unexpanded product circuit**:
\[
 S=24WD(q+1)C+4(q+1)AV_n
       -16W^2DpqB(q^2+10q+1).
 \tag{C3}
\]
For each fixed power of \(q\), its product degree in \((t,x)\) is at most 10.
Apply \(\mathcal H^3\) by the product rule **before** expanding; each resulting
coefficient identity then has degree at most 7 and at most 36 monomials.
There is no expansion of the degree-10 coefficients of (C3).
The same source gives the second derivative at \(t=3/8\) by differentiating
twice before expansion: its coefficient identities have degree at most 8,
and after that substitution are univariate of degree at most 7.

## 2. The third derivative: first reduce y

Write
\[
 \mathcal H^3 S=R_0+R_1y+\cdots+R_6y^6.
 \tag{C4}
\]
The seven complete bivariate polynomials are:

\[
\begin{aligned}
R_{0}={}&2\bigl[39168 t^{4} x + 14736 t^{4} - 685440 t^{3} x^{3} - 1661424 t^{3} x^{2}\\
&{}- 1642656 t^{3} x - 593160 t^{3} + 771120 t^{2} x^{4} + 3745512 t^{2} x^{3}\\
&{}+6651192 t^{2} x^{2} + 5618676 t^{2} x + 2142900 t^{2} - 154224 t x^{5}\\
&{}- 1612026 t x^{4} - 4946328 t x^{3} - 7302714 t x^{2} - 5411964 t x\\
&{}- 2065804 t + 4284 x^{6} + 122115 x^{5} + 691590 x^{4}\\
&{}+1583469 x^{3} + 2107503 x^{2} + 1454466 x + 577374\bigr]
\end{aligned}
\]
This displayed polynomial has 24 monomials and total degree 6.
\[
\begin{aligned}
R_{1}={}&3\bigl[- 65280 t^{4} x^{2} - 103680 t^{4} x - 98640 t^{4} - 799680 t^{3} x^{4}\\
&{}- 2401920 t^{3} x^{3} - 222320 t^{3} x^{2} + 2755808 t^{3} x + 1325144 t^{3}\\
&{}+719712 t^{2} x^{5} + 4413160 t^{2} x^{4} + 8356040 t^{2} x^{3} + 2620472 t^{2} x^{2}\\
&{}- 4160988 t^{2} x - 1550012 t^{2} - 119952 t x^{6} - 1534392 t x^{5}\\
&{}- 6784090 t x^{4} - 11440024 t x^{3} - 6893026 t x^{2} - 28 t x\\
&{}+101044 t + 2856 x^{7} + 96482 x^{6} + 829051 x^{5}\\
&{}+2866176 x^{4} + 4024657 x^{3} + 2592179 x^{2} + 601730 x\\
&{}+169246\bigr]
\end{aligned}
\]
This displayed polynomial has 29 monomials and total degree 7.
\[
\begin{aligned}
R_{2}={}&1566720 t^{4} x^{3} + 5754240 t^{4} x^{2} + 5280768 t^{4} x + 994944 t^{4}\\
&{}- 122400 t^{3} x^{4} + 6885120 t^{3} x^{3} + 10647216 t^{3} x^{2} + 9603360 t^{3} x\\
&{}+2588952 t^{3} - 1299888 t^{2} x^{5} - 19328460 t^{2} x^{4} - 74970648 t^{2} x^{3}\\
&{}- 115704936 t^{2} x^{2} - 82511724 t^{2} x - 17094828 t^{2} + 294984 t x^{6}\\
&{}+3702420 t x^{5} + 28606074 t x^{4} + 83677896 t x^{3} + 119675262 t x^{2}\\
&{}+80876220 t x + 16214932 t - 7956 x^{7} + 217281 x^{6}\\
&{}+342729 x^{5} - 6386787 x^{4} - 22231959 x^{3} - 33218373 x^{2}\\
&{}- 22332574 x - 4580546
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
\[
\begin{aligned}
R_{3}={}&2350080 t^{4} x^{3} + 7994880 t^{4} x^{2} + 5503488 t^{4} x + 85152 t^{4}\\
&{}+10183680 t^{3} x^{4} + 40892160 t^{3} x^{3} + 19305456 t^{3} x^{2} - 10717632 t^{3} x\\
&{}- 6093240 t^{3} - 11280384 t^{2} x^{5} - 86248560 t^{2} x^{4} - 215175528 t^{2} x^{3}\\
&{}- 191536176 t^{2} x^{2} - 61633908 t^{2} x + 693780 t^{2} + 1997568 t x^{6}\\
&{}+29304528 t x^{5} + 154239354 t x^{4} + 316808304 t x^{3} + 301123482 t x^{2}\\
&{}+130825380 t x + 15564656 t - 48960 x^{7} - 1756716 x^{6}\\
&{}- 17440563 x^{5} - 67649640 x^{4} - 111067917 x^{3} - 97535265 x^{2}\\
&{}- 44763640 x - 6815720
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
\[
\begin{aligned}
R_{4}={}&3\bigl[391680 t^{4} x^{3} + 1136640 t^{4} x^{2} + 258048 t^{4} x - 399264 t^{4}\\
&{}+3696480 t^{3} x^{4} + 12341440 t^{3} x^{3} + 2347776 t^{3} x^{2} - 7265472 t^{3} x\\
&{}- 2640752 t^{3} - 3679344 t^{2} x^{5} - 26144100 t^{2} x^{4} - 58031568 t^{2} x^{3}\\
&{}- 37282032 t^{2} x^{2} + 199864 t^{2} x + 4451912 t^{2} + 632808 t x^{6}\\
&{}+10006220 t x^{5} + 50878104 t x^{4} + 97155840 t x^{3} + 79679788 t x^{2}\\
&{}+26076696 t x + 1267736 t - 15300 x^{7} - 729525 x^{6}\\
&{}- 6900552 x^{5} - 24468162 x^{4} - 35988006 x^{3} - 26543870 x^{2}\\
&{}- 9797116 x - 1126408\bigr]
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
\[
\begin{aligned}
R_{5}={}&3\bigl[65280 t^{4} x^{3} + 145920 t^{4} x^{2} - 117504 t^{4} x - 176912 t^{4}\\
&{}+1044480 t^{3} x^{4} + 2843040 t^{3} x^{3} - 1377008 t^{3} x^{2} - 3901184 t^{3} x\\
&{}- 1192360 t^{3} - 998784 t^{2} x^{5} - 7349620 t^{2} x^{4} - 16235736 t^{2} x^{3}\\
&{}- 9280208 t^{2} x^{2} + 1295668 t^{2} x + 1399184 t^{2} + 169728 t x^{6}\\
&{}+2813732 t x^{5} + 14399158 t x^{4} + 26918464 t x^{3} + 20545558 t x^{2}\\
&{}+5583088 t x - 10320 t - 4080 x^{7} - 155281 x^{6}\\
&{}- 1690229 x^{5} - 6389397 x^{4} - 9217283 x^{3} - 6162532 x^{2}\\
&{}- 1897560 x - 155744\bigr]
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
\[
\begin{aligned}
R_{6}={}&12\bigl[- 2176 t^{4} x - 2704 t^{4} - 10880 t^{3} x^{3} - 35472 t^{3} x^{2}\\
&{}- 16480 t^{3} x + 944 t^{3} - 2040 t^{2} x^{4} + 5576 t^{2} x^{3}\\
&{}+19856 t^{2} x^{2} - 7128 t^{2} x - 5744 t^{2} + 2312 t x^{5}\\
&{}+12122 t x^{4} + 12304 t x^{3} + 7084 t x^{2} + 11424 t x\\
&{}+1078 t + 306 x^{6} + 369 x^{5} - 1893 x^{4}\\
&{}+22 x^{3} + 1488 x^{2} + 747 x + 1065\bigr]
\end{aligned}
\]
This displayed polynomial has 24 monomials and total degree 6.
For reproducible interval comparisons, the rule used below is elementary:
for a printed polynomial \(P(t,x)\), replace each positive monomial coefficient
\(c t^r x^s\) by \(c(1/3)^r x^s\), each negative one by
\(c(3/8)^r x^s\), and then round each resulting coefficient down to its printed
integer. When \(u=t-1/3\) is specified, use \(0\le u\le1/24\) instead.
All powers of \(x\) are nonnegative. Thus these are sums of products of factors
with known signs, not numerical samples or unexplained coefficient certificates.

The direct comparisons give
\[
 R_0\ge Q_0,\qquad -R_3\ge Q_3,\qquad -R_4\ge Q_4,
 \qquad R_6\ge Q_6,
 \tag{C5}
\]
with the following polynomials.

\[
\begin{aligned}
Q_{0}={}&8568 x^{6} + 128562 x^{5} + 345520 x^{4} + 217235 x^{3}\\
&{}+40784 x^{2} - 73729 x + 19399
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
Q_{3}={}&48960 x^{7} + 1007628 x^{6} + 7704741 x^{5} + 18856025 x^{4}\\
&{}+13970298 x^{3} + 4719593 x^{2} + 2840450 x + 1105402
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
Q_{4}={}&45900 x^{7} + 1476666 x^{6} + 10671106 x^{5} + 24296524 x^{4}\\
&{}+16031862 x^{3} + 1980334 x^{2} + 762713 x + 383075
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
Q_{6}={}&3672 x^{6} + 13676 x^{5} + 22329 x^{4} + 50029 x^{3}\\
&{}+50219 x^{2} + 31686 x + 7176
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
The polynomials \(Q_3,Q_4,Q_6\) have positive coefficients.
For \(z=x-1/4\ge0\), the remaining identity is:
\[
\begin{aligned}
128Q_0(1/4+z)={}&1096704 z^{6} + 18100992 z^{5} + 65824640 z^{4} + 82660320 z^{3}\\
&{}+45295372 z^{2} + 1478495 z + 1073584
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
All its coefficients are positive. In particular \(R_0,R_6>0\) and \(R_3,R_4<0\).

For the two remaining comparisons set \(u=t-1/3\). The full shifted source polynomials are:

\[
\begin{aligned}
K_2(u,x)=-R_2(u+1/3,x)-\tfrac5{27}R_6(u+1/3,x)={}&\frac{1}{729}\bigl[- 1142138880 u^{4} x^{3} - 4194840960 u^{4} x^{2} - 3846154752 u^{4} x - 720933696 u^{4}\\
&{}+89229600 u^{3} x^{4} - 6524478720 u^{3} x^{3} - 13297477104 u^{3} x^{2} - 12102358176 u^{3} x\\
&{}- 2850120216 u^{3} + 947618352 u^{2} x^{5} + 14182981740 u^{2} x^{4} + 48881516472 u^{2} x^{3}\\
&{}+73815815160 u^{2} x^{2} + 50624339148 u^{2} x + 10101937140 u^{2} - 215043336 u x^{6}\\
&{}- 2071064052 u x^{5} - 11447887626 u x^{4} - 26427820536 u x^{3} - 34233164190 u x^{2}\\
&{}- 21763393140 u x - 4244571948 u + 5799924 x^{7} - 230574681 x^{6}\\
&{}- 1046092833 x^{5} - 729510219 x^{4} + 1738962471 x^{3} + 4160260395 x^{2}\\
&{}+2999093258 x + 703538366\bigr]
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
\[
\begin{aligned}
K_5(u,x)=-R_5(u+1/3,x)={}&\frac{1}{27}\bigl[- 5287680 u^{4} x^{3} - 11819520 u^{4} x^{2} + 9517824 u^{4} x + 14329872 u^{4}\\
&{}- 84602880 u^{3} x^{4} - 237336480 u^{3} x^{3} + 95778288 u^{3} x^{2} + 328686336 u^{3} x\\
&{}+115687656 u^{3} + 80901504 u^{2} x^{5} + 510716340 u^{2} x^{4} + 1081283256 u^{2} x^{3}\\
&{}+855354816 u^{2} x^{2} + 217392012 u^{2} x - 7199496 u^{2} - 13747968 u x^{6}\\
&{}- 173977956 u x^{5} - 797653278 u x^{4} - 1381211280 u x^{3} - 1127630790 u x^{2}\\
&{}- 415454184 u x - 40403352 u + 330480 x^{7} + 7995105 x^{6}\\
&{}+69926841 x^{5} + 191777031 x^{4} + 157328619 x^{3} + 31942002 x^{2}\\
&{}+3119028 x + 4055240\bigr]
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
The same monomial comparison on \(0\le u\le1/24\) gives \(K_2\ge Q_2\), \(K_5\ge Q_5\), where
\[
\begin{aligned}
Q_{2}={}&7956 x^{7} - 328580 x^{6} - 1553344 x^{5} - 1655015 x^{4}\\
&{}+874249 x^{3} + 3748839 x^{2} + 2868858 x + 722184
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
Q_{5}={}&12240 x^{7} + 274899 x^{6} + 2321398 x^{5} + 5871679 x^{4}\\
&{}+3694850 x^{3} - 557136 x^{2} - 525614 x + 87380
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
Since \(0<x\le4/7<1\), the three negative terms of \(Q_2\) are bounded below by
\(-(328580+1553344+1655015)x^2\). Hence
\[
 Q_2\ge7956x^7+874249x^3+211900x^2+2868858x+722184>0.
 \tag{C6}
\]
This inequality uses five monomials of degree at most 7. For \(Q_5\), use
\[
\begin{aligned}
4096Q_5(1/4+z)={}&50135040 z^{7} + 1213722624 z^{6} + 11263227904 z^{5} + 37018984704 z^{4}\\
&{}+45486006784 z^{3} + 19640147728 z^{2} + 1239260248 z + 17033743
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
Its coefficients are positive. Therefore
\[
 R_3,R_4,R_5<0,\quad R_6>0,\quad R_2+\tfrac5{27}R_6<0.
\]
For \(0\le y\le1/3\),
\[
 \partial_y^2(\mathcal H^3S)
 =2R_2+6R_3y+12R_4y^2+20R_5y^3+30R_6y^4
 \le2(R_2+\tfrac5{27}R_6)<0.
 \tag{C7}
\]
Thus it suffices to check \(y=0,1/3\). The first endpoint is (C5).

## 3. The endpoint y=1/3: reduce t, then x

Put \(E(t,x)=\mathcal H^3S(t,x,4/3)\). Its complete polynomial is:
\[
\begin{aligned}
E(t,x)={}&\frac{1}{243}\bigl[67173120 t^{4} x^{3} + 222122880 t^{4} x^{2} + 187914752 t^{4} x + 6687104 t^{4}\\
&{}- 69572160 t^{3} x^{4} - 243304160 t^{3} x^{3} - 383394816 t^{3} x^{2} - 42996160 t^{3} x\\
&{}+21456704 t^{3} + 2159136 t^{2} x^{5} - 108297180 t^{2} x^{4} - 680919712 t^{2} x^{3}\\
&{}- 1341904336 t^{2} x^{2} - 1057308000 t^{2} x + 253721932 t^{2} + 2998800 t x^{6}\\
&{}+14402396 t x^{5} + 229688576 t x^{4} + 881943856 t x^{3} + 1496002192 t x^{2}\\
&{}+982350276 t x - 390159008 t - 111384 x^{7} + 8552949 x^{6}\\
&{}+45921720 x^{5} + 11914278 x^{4} - 203860376 x^{3} - 377943975 x^{2}\\
&{}- 246625128 x + 126113676\bigr]
\end{aligned}
\]
This displayed polynomial has 30 monomials and total degree 7.
The next derivative polynomial is:
\[
\begin{aligned}
-E_{tt}(t,x)={}&\frac{8}{243}\bigl[- 100759680 t^{2} x^{3} - 333184320 t^{2} x^{2} - 281872128 t^{2} x - 10030656 t^{2}\\
&{}+52179120 t x^{4} + 182478120 t x^{3} + 287546112 t x^{2} + 32247120 t x\\
&{}- 16092528 t - 539784 x^{5} + 27074295 x^{4} + 170229928 x^{3}\\
&{}+335476084 x^{2} + 264327000 x - 63430483\bigr]
\end{aligned}
\]
This displayed polynomial has 15 monomials and total degree 5.
Direct monomial comparison on \(1/3\le t\le3/8\) gives \(-E_{tt}\ge Q_T\), where
\[
\begin{aligned}
Q_T(x)={}&- 17771 x^{5} + 1463945 x^{4} + 7140300 x^{3} + 12657473 x^{2}\\
&{}+7751037 x - 2333358
\end{aligned}
\]
This displayed polynomial has 6 monomials and total degree 5.
\[
\begin{aligned}
1024Q_T(1/4+z)={}&- 18197504 z^{5} + 1476332800 z^{4} + 8799373440 z^{3} + 19004314272 z^{2}\\
&{}+15881962724 z + 525067961
\end{aligned}
\]
This displayed polynomial has 6 monomials and total degree 5.
Here \(0\le z\le9/28<1\), so the negative \(z^5\) term is absorbed by the positive \(z^4\) term. Hence \(E_{tt}<0\), and only \(t=1/3,3/8\) remain.

The exact endpoints, before harmless rounding, are:
For \(t=\frac{1}{3}\), \(E=\frac{1}{19683}P_a\), with
\[
\begin{aligned}
P_a(x)={}&- 9022104 x^{7} + 773756469 x^{6} + 4127956236 x^{5} + 5983256970 x^{4}\\
&{}+508776888 x^{3} - 3226603383 x^{2} - 2910023644 x + 2035469144
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
Coefficientwise, \(P_a\ge1000U_a\), with
\[
\begin{aligned}
U_a(x)={}&- 9023 x^{7} + 773756 x^{6} + 4127956 x^{5} + 5983256 x^{4}\\
&{}+508776 x^{3} - 3226604 x^{2} - 2910024 x + 2035469
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
128U_a^{\prime\prime}(1/4+z)={}&\frac{1}{4}\bigl[- 194030592 z^{5} + 11642353920 z^{4} + 54033892480 z^{3} + 72890344224 z^{2}\\
&{}+28608213924 z + 90976613\bigr]
\end{aligned}
\]
This displayed polynomial has 6 monomials and total degree 5.
The only negative term in this last polynomial is the leading \(z^5\) term; \(z<1\) absorbs it in the positive \(z^4\) term. Hence \(U_a\) is convex. Its tangent at \(x=1/2\) gives
\[
 U_a(x)\ge \frac{45103945}{128}+(- \frac{85077721}{64})(x-1/2)\ge \frac{115324947}{448}>0.
\]
For \(t=\frac{3}{8}\), \(E=\frac{1}{7776}P_b\), with
\[
\begin{aligned}
P_b(x)={}&- 3564288 x^{7} + 309679968 x^{6} + 1652039904 x^{5} + 2532779478 x^{4}\\
&{}+627587756 x^{3} - 687167025 x^{2} - 815328000 x + 535918101
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
Coefficientwise, \(P_b\ge1000U_b\), with
\[
\begin{aligned}
U_b(x)={}&- 3565 x^{7} + 309679 x^{6} + 1652039 x^{5} + 2532779 x^{4}\\
&{}+627587 x^{3} - 687168 x^{2} - 815328 x + 535918
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
128U_b^{\prime\prime}(1/4+z)={}&\frac{1}{4}\bigl[- 76661760 z^{5} + 4660842240 z^{4} + 21625635200 z^{3} + 30020826336 z^{2}\\
&{}+13176353772 z + 1033746035\bigr]
\end{aligned}
\]
This displayed polynomial has 6 monomials and total degree 5.
The only negative term in this last polynomial is the leading \(z^5\) term; \(z<1\) absorbs it in the positive \(z^4\) term. Hence \(U_b\) is convex. Its tangent at \(x=1/2\) gives
\[
 U_b(x)\ge \frac{31954709}{128}+(\frac{51745333}{64})(x-1/2)\ge \frac{12164085}{256}>0.
\]
The endpoint checks prove \(E>0\). Together with (C7), this proves
\[
 \boxed{\mathcal H^3S>0\quad
 (1/3\le t\le3/8,\ 1/4\le x\le4/7,\ 0\le y\le1/3).}
 \tag{C8}
\]

## 4. The second derivative on h=1/4

Set \(f(x,y)=\mathcal H^2S(3/8,x,1+y)\).
For this section it is enough to prove positivity on the rectangle
\[
 9/32\le x\le1/2,\qquad 0\le y\le3/10.
 \tag{C9}
\]
It contains the lower jets needed for (C1), because \(x_0=j+1/4\) lies in
\([17/60,41/84]\). Write \(f=E_0+E_1y+\cdots+E_6y^6\).
Here are the seven complete univariate coefficients:

\[
\begin{aligned}
E_{0}(x)={}&\frac{1}{384}\bigl[1919232 x^{6} + 6589632 x^{5} - 7253856 x^{4} - 2114184 x^{3}\\
&{}+6137832 x^{2} + 2519527 x + 8308288\bigr]
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
E_{1}(x)={}&\frac{1}{256}\bigl[1304576 x^{7} + 14048384 x^{6} + 45903104 x^{5} - 2872160 x^{4}\\
&{}- 36972536 x^{3} + 14610056 x^{2} + 7161165 x + 3350288\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
E_{2}(x)={}&\frac{1}{192}\bigl[8570112 x^{7} + 51634128 x^{6} + 74564136 x^{5} + 17552280 x^{4}\\
&{}- 81599928 x^{3} - 116940258 x^{2} - 78497143 x - 26690370\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
E_{3}(x)={}&\frac{1}{384}\bigl[- 11312640 x^{7} - 151837440 x^{6} - 508502400 x^{5} + 95269872 x^{4}\\
&{}+956561796 x^{3} + 432188304 x^{2} - 87639991 x - 65420540\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
E_{4}(x)={}&\frac{1}{128}\bigl[- 9282560 x^{7} - 91149984 x^{6} - 241812432 x^{5} + 64643568 x^{4}\\
&{}+516879072 x^{3} + 308744176 x^{2} + 10046253 x - 17221952\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
E_{5}(x)={}&\frac{1}{256}\bigl[- 384000 x^{7} - 23459392 x^{6} - 85768352 x^{5} + 87420792 x^{4}\\
&{}+322409624 x^{3} + 161436160 x^{2} - 33072663 x - 24958196\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
E_{6}(x)={}&\frac{1}{64}\bigl[43520 x^{7} + 212224 x^{6} + 342752 x^{5} + 625008 x^{4}\\
&{}+664296 x^{3} + 288020 x^{2} - 11107 x - 106491\bigr]
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
The coefficient \(E_2\) is negative: in its displayed numerator,
use \(x^7\le x^3/16\), \(x^6\le x^3/8\), \(x^5\le x^3/4\),
\(x^4\le x^3/2\). The four positive coefficients then sum to less than
\(81599928x^3\), and all the remaining terms are negative.

For the fourth derivative use the following three elementary bounds:
\[
 E_4>120000,\qquad E_5>-70000,\qquad E_6>-1300.
 \tag{C10}
\]
Their explicit small certificates follow. Rounding coefficients down gives
\(E_4'-1000000\ge J_4\), \(E_5+70000\ge J_5\), and \(E_6+1300\ge J_6\):

\[
\begin{aligned}
J_4(x)={}&- 507640 x^{6} - 4272656 x^{5} - 9445799 x^{4} + 2020111 x^{3}\\
&{}+12114353 x^{2} + 4824127 x - 921514
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
512J_4(1/4+z)={}&- 259911680 z^{6} - 2577467392 z^{5} - 7814416128 z^{4} - 5250424576 z^{3}\\
&{}+4807636272 z^{2} + 5418643000 z + 528401891
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
J_5(x)={}&- 1500 x^{7} - 91639 x^{6} - 335033 x^{5} + 341487 x^{4}\\
&{}+1259412 x^{3} + 630610 x^{2} - 129191 x - 27493
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
2048J_5(1/4+z)={}&- 3072000 z^{7} - 193052672 z^{6} - 971694592 z^{5} - 335945984 z^{4}\\
&{}+2790729952 z^{3} + 3369937888 z^{2} + 893979778 z + 583631
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
J_6(x)={}&680 x^{7} + 3316 x^{6} + 5355 x^{5} + 9765 x^{4}\\
&{}+10379 x^{3} + 4500 x^{2} - 174 x - 364
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
2048J_6(1/4+z)={}&1392640 z^{7} + 9228288 z^{6} + 22981632 z^{5} + 40835840 z^{4}\\
&{}+50421952 z^{3} + 34797744 z^{2} + 9743476 z + 164141
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
Here \(0\le z\le1/4\). In the shifted \(J_4\), absorb the four negative
terms of degree at least 3 into \(4807636272z^2\), using \(z^r\le z^2/4^{r-2}\).
Their total coefficient is less than \(2000000000\). In the shifted \(J_5\),
absorb its four negative terms into \(2790729952z^3\), using
\(z^r\le z^3/4^{r-3}\); their total is less than \(150000000\).
The shifted \(J_6\) already has positive coefficients.
Thus all three \(J_i\) are positive. Moreover \(E_4(1/4)>98000\), so
\[
 E_4(x)>98000+1000000(x-1/4)
 \ge98000+1000000/32=129250>120000.
\]
Now (C10) gives
\[
 f_{yyyy}=24E_4+120E_5y+360E_6y^2
 >2880000-2520000-42120=317880>0.
 \tag{C11}
\]

It remains to check \(f(x,0)>0\), \(f(x,3/10)>0\), and
\(f_y(x,3/10)<0\). Coefficientwise downward rounding gives
\[
 f(x,0)\ge L_0(x),\quad f(x,3/10)\ge L_1(x),\quad
 -f_y(x,3/10)\ge L_2(x).
 \tag{C12}
\]
Each comparison is a scalar comparison of the explicitly printed \(E_i\) coefficients;
no large endpoint polynomial needs to be expanded.
The three lower polynomials and their shifts are:

\[
\begin{aligned}
L_0(x)={}&4998 x^{6} + 17160 x^{5} - 18891 x^{4} - 5506 x^{3}\\
&{}+15983 x^{2} + 6561 x + 21636
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
2048L_0(1/4+z)={}&10235904 z^{6} + 50497536 z^{5} + 14836992 z^{4} - 24801536 z^{3}\\
&{}+15858640 z^{2} + 26017544 z + 49425083
\end{aligned}
\]
This displayed polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
L_1(x)={}&4160 x^{7} + 29000 x^{6} + 54038 x^{5} - 2403 x^{4}\\
&{}+15952 x^{3} + 29750 x^{2} - 27683 x + 7123
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
128L_1(1/4+z)={}&532480 z^{7} + 4643840 z^{6} + 13183744 z^{5} + 12109696 z^{4}\\
&{}+7290112 z^{3} + 6533228 z^{2} - 1118045 z + 302284
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
L_2(x)={}&- 16041 x^{7} - 28902 x^{6} + 162738 x^{5} - 179134 x^{4}\\
&{}- 760434 x^{3} - 281623 x^{2} + 275710 x + 134822
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
16384L_2(1/4+z)={}&- 262815744 z^{7} - 933457920 z^{6} + 1611058176 z^{5} - 189719296 z^{4}\\
&{}- 13911355072 z^{3} - 14675449936 z^{2} - 260457020 z + 2846186335
\end{aligned}
\]
This displayed polynomial has 8 monomials and total degree 7.
For \(L_0\), absorb \(-24801536z^3\) in \(15858640z^2\) using \(z\le1/4\).
For \(L_1\), discard its positive terms of degree at least 3 and use
\[
 6533228z^2-1118045z+302284
 \ge6000000z^2-1200000z+300000
 =6000000(z-1/10)^2+240000>0.
 \tag{C13}
\]
This square completion has three monomials and degree 2.
For \(L_2\), discard its positive \(z^5\) term, bound every negative power
of degree at least 2 by \(z^2\), and then use \(z^2\le1/16\), \(z\le1/4\).
The resulting lower bound is
\[
 2846186335-29972797968/16-260457020/4
 =14524355312/16>0.
 \tag{C14}
\]
Thus (C12) has the required signs.

For completeness, the one-variable calculus step is as follows.
By (C11), \(f_{yy}\) is strictly convex in \(y\), and
\(f_{yy}(x,0)=2E_2<0\). It is negative up to at most one crossing, and positive
thereafter. Consequently \(f_y\) first decreases and then increases.
Since its terminal value is negative by (C12), \(f_y\) can have only an initial
positive interval. Therefore \(f\) first increases and then decreases, or
just decreases, and its minimum is at one of the two endpoints.
The endpoint signs in (C12) prove \(f>0\) throughout (C9).

## 5. Transport the positive lower jet

Fix \(j,y\) satisfying (C1) and increase \(h\) from \(1/4\) to its given value.
Along that segment, \(t=(1-h)/2\in[1/3,3/8]\),
\(x=h+j\in[1/4,4/7]\), and \(y\le9/32<1/3\).
By (C8), the function \(\mathcal H^2S\) strictly increases in \(h\).
Its initial value is positive by section 4, proving (C1).

This establishes curvature only. The additional claim \(\mathcal H S>0\)
on the actual low-t domain, needed to reduce the unit sign to its three lower
faces, is not asserted here.


## 6. A quantitative fourth derivative for the next Taylor step

The following stronger auxiliary bound supplies the
[first-derivative reduction](NONSHORT_LOW_T_H_REDUCTION.md):
\[
 \boxed{\mathcal H^4S>500000\quad
 (1/3\le t\le3/8,\ 1/4\le x\le4/7,\ 0\le y\le2/7).}
 \tag{C15}
\]
It follows by the same two-dimensional mechanism, with more slack.
Differentiate the source circuit (C3) four times before expansion and write
\(\mathcal H^4S=F_0+F_1y+\cdots+F_6y^6\).
Its complete coefficients are:
\[
\begin{aligned}
F_0={}&8\bigl[9792 t^{4} - 514080 t^{3} x^{2} - 850296 t^{3} x - 418032 t^{3}\\
&{}+1028160 t^{2} x^{3} + 3432168 t^{2} x^{2} + 3941592 t^{2} x + 1627104 t^{2}\\
&{}- 385560 t x^{4} - 2548404 t x^{3} - 5372544 t x^{2} - 5056026 t x\\
&{}- 1888716 t + 25704 x^{5} + 354147 x^{4} + 1309881 x^{3}\\
&{}+2100441 x^{2} + 1730247 x + 621842\bigr]
\end{aligned}
\]
This polynomial has 19 monomials and total degree 5.
\[
\begin{aligned}
F_1={}&12\bigl[- 32640 t^{4} x - 25920 t^{4} - 799680 t^{3} x^{3} - 1768800 t^{3} x^{2}\\
&{}- 59320 t^{3} x + 738272 t^{3} + 1199520 t^{2} x^{4} + 5313880 t^{2} x^{3}\\
&{}+6350400 t^{2} x^{2} + 276808 t^{2} x - 1537176 t^{2} - 359856 t x^{5}\\
&{}- 3021280 t x^{4} - 8873100 t x^{3} - 9235136 t x^{2} - 2406266 t x\\
&{}+387496 t + 19992 x^{6} + 336522 x^{5} + 1884325 x^{4}\\
&{}+4296179 x^{3} + 3880121 x^{2} + 1296093 x + 137802\bigr]
\end{aligned}
\]
This polynomial has 24 monomials and total degree 6.
\[
\begin{aligned}
F_2={}&12\bigl[391680 t^{4} x^{2} + 959040 t^{4} x + 440064 t^{4} - 301920 t^{3} x^{3}\\
&{}+762240 t^{3} x^{2} + 894408 t^{3} x + 634456 t^{3} - 526320 t^{2} x^{4}\\
&{}- 7303460 t^{2} x^{3} - 20073564 t^{2} x^{2} - 20484576 t^{2} x - 7199596 t^{2}\\
&{}+255816 t x^{5} + 3153380 t x^{4} + 15782912 t x^{3} + 30561552 t x^{2}\\
&{}+26821854 t x + 8164254 t - 16932 x^{6} - 45627 x^{5}\\
&{}- 1049116 x^{4} - 5615508 x^{3} - 10544459 x^{2} - 8906238 x\\
&{}-2536670\bigr]
\end{aligned}
\]
This polynomial has 25 monomials and total degree 6.
\[
\begin{aligned}
F_3={}&4\bigl[1762560 t^{4} x^{2} + 3997440 t^{4} x + 1375872 t^{4} + 9008640 t^{3} x^{3}\\
&{}+26671680 t^{3} x^{2} + 6900984 t^{3} x - 2721984 t^{3} - 17919360 t^{2} x^{4}\\
&{}- 101583120 t^{2} x^{3} - 168621192 t^{2} x^{2} - 91748976 t^{2} x - 13123512 t^{2}\\
&{}+5816448 t x^{5} + 58192800 t x^{4} + 208033236 t x^{3} + 285490272 t x^{2}\\
&{}+165970218 t x + 32532900 t - 335376 x^{6} - 6298140 x^{5}\\
&{}- 41080623 x^{4} - 107250678 x^{3} - 120941373 x^{2} - 65120805 x\\
&{}-13136492\bigr]
\end{aligned}
\]
This polynomial has 25 monomials and total degree 6.
\[
\begin{aligned}
F_4={}&12\bigl[293760 t^{4} x^{2} + 568320 t^{4} x + 64512 t^{4} + 3500640 t^{3} x^{3}\\
&{}+8687760 t^{3} x^{2} + 1044864 t^{3} x - 1616736 t^{3} - 5985360 t^{2} x^{4}\\
&{}- 30772140 t^{2} x^{3} - 44404092 t^{2} x^{2} - 15916464 t^{2} x + 1040248 t^{2}\\
&{}+1869048 t x^{5} + 19043800 t x^{4} + 65385996 t x^{3} + 82187388 t x^{2}\\
&{}+39789928 t x + 5406196 t - 105876 x^{6} - 2345065 x^{5}\\
&{}- 14985453 x^{4} - 36612642 x^{3} - 36950978 x^{2} - 16531522 x\\
&{}-2607746\bigr]
\end{aligned}
\]
This polynomial has 25 monomials and total degree 6.
\[
\begin{aligned}
F_5={}&12\bigl[48960 t^{4} x^{2} + 72960 t^{4} x - 29376 t^{4} + 1011840 t^{3} x^{3}\\
&{}+2059320 t^{3} x^{2} - 629752 t^{3} x - 886840 t^{3} - 1640160 t^{2} x^{4}\\
&{}- 8415760 t^{2} x^{3} - 11660424 t^{2} x^{2} - 3177160 t^{2} x + 771052 t^{2}\\
&{}+504288 t x^{5} + 5354570 t x^{4} + 18458092 t x^{3} + 22508900 t x^{2}\\
&{}+9948862 t x + 1045976 t - 28356 x^{6} - 584638 x^{5}\\
&{}- 3912681 x^{4} - 9754205 x^{3} - 9481157 x^{2} - 3779152 x\\
&{}-473100\bigr]
\end{aligned}
\]
This polynomial has 25 monomials and total degree 6.
\[
\begin{aligned}
F_6={}&48\bigl[- 544 t^{4} - 8160 t^{3} x^{2} - 16648 t^{3} x - 2768 t^{3}\\
&{}+2040 t^{2} x^{3} + 17484 t^{2} x^{2} + 16108 t^{2} x - 2136 t^{2}\\
&{}+3400 t x^{4} + 10728 t x^{3} + 4264 t x^{2} + 5324 t x\\
&{}+4292 t + 170 x^{5} - 1054 x^{4} - 3431 x^{3}\\
&{}- 869 x^{2} - 684 x + 52\bigr]
\end{aligned}
\]
This polynomial has 19 monomials and total degree 5.
For y-concavity, direct monomial comparison in \(t\) gives
\[
 -F_2-\frac{240}{2401}F_6\ge B_2,\quad
 -F_3\ge B_3,\quad -F_4\ge B_4,\quad -F_5\ge B_5,\quad F_6\ge B_6,
\]
where the complete lower polynomials are:
\[
\begin{aligned}
B_2(x)={}&203184 x^{6} - 604464 x^{5} - 900119 x^{4} + 6231197 x^{3}\\
&{}+15185214 x^{2} + 12685031 x + 2788356
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
B_3(x)={}&1341504 x^{6} + 16467888 x^{5} + 84997452 x^{4} + 160200651 x^{3}\\
&{}+124707357 x^{2} + 50533335 x + 9873713
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
B_4(x)={}&1270512 x^{6} + 19730064 x^{5} + 102108816 x^{4} + 183928993 x^{3}\\
&{}+127206512 x^{2} + 39749472 x + 5912891
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
B_5(x)={}&340272 x^{6} + 4746360 x^{5} + 25043487 x^{4} + 44569754 x^{3}\\
&{}+26716284 x^{2} + 5078734 x + 67660
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
\[
\begin{aligned}
B_6(x)={}&8160 x^{5} + 3808 x^{4} + 17840 x^{3} + 99105 x^{2}\\
&{}+96121 x + 49227
\end{aligned}
\]
This polynomial has 6 monomials and total degree 5.
The lower polynomials \(B_3,B_4,B_5,B_6\) have positive coefficients.
For \(B_2\), absorb \(-604464x^5-900119x^4\) in \(6231197x^3\), using \(x<1\).
Thus \(F_3,F_4,F_5<0\), \(F_6>0\), and \(F_2+240F_6/2401<0\).
Since \(15(2/7)^4=240/2401\),
\[
 \partial_y^2(\mathcal H^4S)
 \le2(F_2+240F_6/2401)<0.
\]
Only the two endpoints \(y=0,2/7\) remain.
At the first, direct monomial comparison gives \(F_0-500000\ge B_0>0\), with
\[
\begin{aligned}
B_0(x)={}&6\bigl[34272 x^{5} + 279416 x^{4} + 624626 x^{3} + 586639 x^{2}\\
&{}+303136 x + 13252\bigr]
\end{aligned}
\]
This polynomial has 6 monomials and total degree 5.
At the second endpoint, round each coefficient down before collecting any large integer numerator.
This gives \(\mathcal H^4S(t,x,9/7)-500000\ge B_E(t,x)\), where
\[
\begin{aligned}
B_E(t,x)={}&572733 t^{4} x^{2} + 1247611 t^{4} x + 553385 t^{4} - 1894010 t^{3} x^{3}\\
&{}- 6200525 t^{3} x^{2} - 5417042 t^{3} x - 595096 t^{3} + 1409181 t^{2} x^{4}\\
&{}+7159772 t^{2} x^{3} + 10018017 t^{2} x^{2} + 2510640 t^{2} x - 429757 t^{2}\\
&{}- 279572 t x^{5} - 3279766 t x^{4} - 10289425 t x^{3} - 10984529 t x^{2}\\
&{}- 3530377 t x - 2292069 t + 11554 x^{6} + 526264 x^{5}\\
&{}+3145658 x^{4} + 6551263 x^{3} + 5322882 x^{2} + 2077501 x\\
&{}+1017396
\end{aligned}
\]
This polynomial has 25 monomials and total degree 6.
The comparison is coefficientwise in the printed \(F_i\), hence is a collection of scalar rational comparisons.
It does not require expanding an endpoint polynomial with a large common denominator.
Direct monomial comparison in \(t\) gives \(B_E\ge B_{EE}>0\), where
\[
\begin{aligned}
B_{EE}(x)={}&11554 x^{6} + 421424 x^{5} + 2072321 x^{4} + 3388379 x^{3}\\
&{}+1996886 x^{2} + 762307 x + 72885
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
All coefficients are positive. Concavity in \(y\) now proves (C15).
In particular, wherever (C1) holds, Taylor's theorem in the increasing h direction gives
\[
 \mathcal HS(h,j,y)\ge P_0+rP_1+\frac{r^2}{2}P_2+\frac{250000}{3}r^3,
 \quad r=h-1/4,
 \tag{C16}
\]
where \(P_i=\mathcal H^{i+1}S(3/8,j+1/4,1+y)\) for \(i=0,1,2\).
The domain has \(y\le9/32<2/7\), so (C15) applies along the segment.
This Taylor lower bound is an exact analytic consequence of the derivative bound;
its sign on the constrained domain remains the next task.
