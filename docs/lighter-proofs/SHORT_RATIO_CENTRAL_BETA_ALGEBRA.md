# Central ratio: beta monotonicity algebra

Companion to [the beta reduction](SHORT_RATIO_CENTRAL_BETA.md).
Every identity below is expanded only after differentiation or restriction
to the indicated one- or two-variable face. The letters are defined in
that proof. All polynomials are printed in full.


## The positive beta-pole residue

\[
419904\,(2aK^3p_c/J)=P_c(r,t)=\begin{aligned}&1119744 t^{7} + 26780544 t^{6} + 250387200 t^{5} + 1173100320 t^{4} + 2866310496 t^{3} + 3368723400 t^{2} + 1484854560 t + 14128078\\
&+\bigl(- 839808 t^{7} - 19455552 t^{6} - 160893216 t^{5} - 552449808 t^{4} - 358646616 t^{3} + 2213193780 t^{2} + 4285560618 t + 2005349277\bigr)r\\
&+\bigl(- 13436928 t^{5} - 210231936 t^{4} - 1244953152 t^{3} - 3211106976 t^{2} - 2832178608 t - 369824976\bigr)r^{2}\\
&+\bigl(1679616 t^{5} + 25754112 t^{4} + 131989824 t^{3} + 128545056 t^{2} - 729806112 t - 837538056\bigr)r^{3}\\
&+\bigl(4898880 t^{3} + 72573408 t^{2} + 312256944 t + 166238568\bigr)r^{4}\\
&+\bigl(- 419904 t^{3} - 6508512 t^{2} - 28588464 t + 20748312\bigr)r^{5}\\
&+\bigl(-7698240\bigr)r^{6}\\
&+\bigl(419904\bigr)r^{7}\end{aligned}
\]

38 monomials; total degree 8; largest coefficient numerator 4285560618.

Here \(r=4/3-a\in[0,1/3]\), \(t=x-13/6\in[0,7/30]\).
Retain the constant and linear terms in \(r\); discard every positive
higher term and replace each negative \(qr^i\), \(i\ge2\), by
\(qr/3^{i-1}\). This gives
\[
P_c(r,t)\ge P_c(0,t)+rL_c(t).
\]
The polynomial \(P_c(0,t)\) printed above has positive coefficients.


## Residue lower polynomial

\[
L_c(t)=- 839808 t^{7} - 19455552 t^{6} - 165372192 t^{5} - 622527120 t^{4} - 773636184 t^{3} + 1142744436 t^{2} + 3260058570 t + 1788982821
\]

8 monomials; total degree 7; largest coefficient numerator 3260058570.

Discarding positive nonconstant terms and substituting
\(t=7/30\) into negative terms gives \(L_c(t)>10^9\).
Thus \(p_c>0\).


## curvature identity

\[
19200S^2K^3(6p_3B_{\max}+2p_2-1/10)=P_G(c,h)=\begin{aligned}&- 1920 h^{8} - 46080 h^{7} + 44268 h^{6} + 3376688 h^{5} + 19886188 h^{4} + 53826080 h^{3} + 78279908 h^{2} + 59575216 h + 18031940\\
&+\bigl(55596 h^{6} - 1370620 h^{5} - 18237705 h^{4} - 78889760 h^{3} - 156043642 h^{2} - 145233924 h - 55231433\bigr)c\\
&+\bigl(- 5760 h^{6} - 170796 h^{5} + 148427 h^{4} + 12027610 h^{3} + 57543720 h^{2} + 94427186 h + 42329773\bigr)c^{2}\\
&+\bigl(- 23040 h^{4} + 881306 h^{3} + 3633501 h^{2} - 4939536 h - 21553975\bigr)c^{3}\\
&+\bigl(- 5760 h^{4} - 69120 h^{3} - 1738665 h^{2} - 9187830 h - 13315185\bigr)c^{4}\\
&+\bigl(- 11520 h^{2} - 69120 h - 103680\bigr)c^{5}\\
&+\bigl(- 1920 h^{2} - 11520 h - 17280\bigr)c^{6}\end{aligned}
\]

39 monomials; total degree 8; largest coefficient numerator 156043642.


## curvature lower polynomial

\[
L_{curvature}(h)=- 1920 h^{8} - 46080 h^{7} + 43628 h^{6} + \frac{8702512 h^{5}}{3} + \frac{124254257 h^{4}}{9} + 27528640 h^{3} + \frac{6377254487 h^{2}}{243} + \frac{880245790 h}{81} - \frac{36225047}{27}
\]

9 monomials; total degree 8; largest coefficient numerator 6377254487.


## A1 identity

\[
9600aS^2K(A_1-9/2)=P_A(c,h)=\begin{aligned}&1354 h^{7} + 30920 h^{6} + 300518 h^{5} + 1605372 h^{4} + 4874158 h^{3} + 7942376 h^{2} + 5741954 h + 801524\\
&+\bigl(4117 h^{6} + 65884 h^{5} + 456281 h^{4} + 1457140 h^{3} + 1587715 h^{2} - 1403536 h - 3042225\bigr)c\\
&+\bigl(- 2397 h^{5} - 9235 h^{4} - 59520 h^{3} - 574224 h^{2} - 1935619 h - 2047677\bigr)c^{2}\\
&+\bigl(- 29489 h^{3} - 237303 h^{2} - 635775 h - 562361\bigr)c^{3}\\
&+\bigl(9603 h^{2} + 57618 h + 86427\bigr)c^{4}\end{aligned}
\]

28 monomials; total degree 7; largest coefficient numerator 7942376.


## A1 lower polynomial

\[
L_{A1}(h)=1354 h^{7} + 30920 h^{6} + \frac{900755 h^{5}}{3} + \frac{14439113 h^{4}}{9} + \frac{131394217 h^{3}}{27} + \frac{23609353 h^{2}}{3} + \frac{15106478 h}{3} - \frac{12444269}{27}
\]

8 monomials; total degree 7; largest coefficient numerator 131394217.


## Pc identity

\[
4aK^2(P_c/J+2)=P_H(c,h)=\begin{aligned}&- 4 h^{5} - 44 h^{4} - 172 h^{3} - 252 h^{2} + 232\\
&+\bigl(12 h^{4} + 128 h^{3} + 552 h^{2} + 1152 h + 1020\bigr)c\\
&+\bigl(- 9 h^{3} - 17 h^{2} + 141 h + 421\bigr)c^{2}\\
&+\bigl(- h^{3} + 11 h^{2} + 93 h + 249\bigr)c^{3}\\
&+\bigl(49\bigr)c^{4}\\
&+\bigl(9\bigr)c^{5}\end{aligned}
\]

20 monomials; total degree 6; largest coefficient numerator 1152.


## Pc lower polynomial

\[
L_{Pc}(h)=- 4 h^{5} - 44 h^{4} - \frac{4672 h^{3}}{27} - \frac{2285 h^{2}}{9} + 232
\]

5 monomials; total degree 5; largest coefficient numerator 4672.

For these three identities \(c=a-1\in[0,1/3]\) and
\(h=x-2\in[1/6,2/5]\). In each positive term with a positive power
of \(c\), replace that term by zero; in each negative such term put
\(c=1/3\). The displayed lower polynomials result exactly. For the
first two, put \(h=1/6\) in positive terms and \(h=2/5\) in negative
terms; their lower bounds are respectively \(10^6\) and \(600000\).
For the third discard positive nonconstant terms and put \(h=2/5\)
in negative terms; the lower bound is \(179\). All are strict.


## Second x derivative of the first base-face numerator

\[
(N_0)_{xx}(2+h,1+c)=\begin{aligned}&- 2592 h^{7} - 298032 h^{6} - 1948968 h^{5} - 1398900 h^{4} + 18989120 h^{3} + 60645720 h^{2} + 70067400 h + 28296844\\
&+\bigl(- 2448 h^{7} - 274848 h^{6} - 1461936 h^{5} + 1082760 h^{4} + 19656880 h^{3} + 38408496 h^{2} + 19198608 h - 4557240\bigr)c\\
&+\bigl(- 8400 h^{6} - 13692 h^{5} - 530370 h^{4} - 10144280 h^{3} - 45284076 h^{2} - 73423116 h - 38200754\bigr)c^{2}\\
&+\bigl(- 2772 h^{5} + 304320 h^{4} + 791540 h^{3} + 583020 h^{2} + 6691464 h + 11708988\bigr)c^{3}\\
&+\bigl(5310 h^{4} - 19760 h^{3} + 885072 h^{2} + 6077982 h + 7177588\bigr)c^{4}\\
&+\bigl(2260 h^{3} - 103668 h^{2} - 6690 h - 332708\bigr)c^{5}\\
&+\bigl(- 276 h^{2} - 14106 h - 199582\bigr)c^{6}\\
&+\bigl(- 54 h - 560\bigr)c^{7}\end{aligned}
\]

43 monomials; total degree 8; largest coefficient numerator 73423116.


## Its x=2 first x derivative

\[
(N_0)_x(2,1+c)=27 c^{8} - 38399 c^{7} - 596192 c^{6} - 1487652 c^{5} + 3968851 c^{4} + 9907773 c^{3} - 13314906 c^{2} - 6164570 c + 8694156
\]

9 monomials; total degree 8; largest coefficient numerator 13314906.


## Its decreasing shape derivative at x=2

\[
-(N_0)_a(2,1+c)=- 81 c^{8} + 26344 c^{7} + 719887 c^{6} + 5433210 c^{5} + 11799365 c^{4} - 977204 c^{3} - 14957595 c^{2} + 5851730 c + 2922648
\]

9 monomials; total degree 8; largest coefficient numerator 14957595.


## Second-derivative lower polynomial

\[
L_{xx}(h)=- 3408 h^{7} - \frac{1171744 h^{6}}{3} - 2437904 h^{5} - 1457830 h^{4} + \frac{1446800440 h^{3}}{81} + \frac{13514136148 h^{2}}{243} + \frac{15043942670 h}{243} + \frac{49276592968}{2187}
\]

8 monomials; total degree 7; largest coefficient numerator 49276592968.

The same rule in \(c\) gives
\((N_0)_{xx}\ge L_{xx}(h)>22000000\) for \(0\le h\le2/5\):
discard positive nonconstant terms and use \(h\le2/5\) in negative
ones. Directly applying the rule to the two univariate polynomials gives
\((N_0)_x(2,a)>5000000\) and \(-(N_0)_a(2,a)>1000000\).
Finally, without expanding the degree-ten parent numerator,
\[
N_0(2,4/3)=\frac{6582707200}{6561}>1000000.
\]
Hence \(N_0(2,a)>0\), then \((N_0)_x(x,a)>0\), then
\(N_0(x,a)>0\) for \(2\le x\le12/5\).


## The second base-face numerator

\[
N_1(2+h,1+c)=\begin{aligned}&- 72 h^{8} - 1370 h^{7} - 5314 h^{6} + 35682 h^{5} + 356450 h^{4} + 1174538 h^{3} + 1841138 h^{2} + 1363278 h + 380502\\
&+\bigl(26 h^{7} - 2020 h^{6} - 17202 h^{5} - 51776 h^{4} - 132442 h^{3} - 440356 h^{2} - 750574 h - 383192\bigr)c\\
&+\bigl(- 70 h^{6} - 449 h^{5} - 12365 h^{4} - 125502 h^{3} - 556668 h^{2} - 910721 h - 390881\bigr)c^{2}\\
&+\bigl(39 h^{5} - 831 h^{4} - 6030 h^{3} - 86674 h^{2} - 145849 h + 54065\bigr)c^{3}\\
&+\bigl(24 h^{4} + 1669 h^{3} - 9700 h^{2} + 7769 h + 94918\bigr)c^{4}\\
&+\bigl(9 h^{3} + 88 h^{2} + 10871 h + 33072\bigr)c^{5}\\
&+\bigl(1861 - 22 h\bigr)c^{6}\\
&+\bigl(-9\bigr)c^{7}\end{aligned}
\]

42 monomials; total degree 8; largest coefficient numerator 1841138.


## Its lower polynomial

\[
L_1(h)=- 72 h^{8} - 1370 h^{7} - \frac{53956 h^{6}}{9} + \frac{269083 h^{5}}{9} + \frac{1013360 h^{4}}{3} + \frac{3348668 h^{3}}{3} + \frac{131962832 h^{2}}{81} + \frac{733733834 h}{729} + \frac{50869646}{243}
\]

9 monomials; total degree 8; largest coefficient numerator 733733834.

The same two termwise rules give \(N_1>200000\) for
\(0\le c\le1/3\), \(0\le h\le2/5\).

The largest identity here has 43 monomials and degree eight. The
shifted residue has coefficient numerators below \(5\times10^9\).
In the factored source for \(N_0\), every separately differentiated
contribution also has degree at most eight and coefficient numerators
at most 106263048 after the stated shift; for \(N_1\) the analogous
bound is 6280416. The degree-ten parent \(N_0\) and its degree-nine
first derivative are never expanded as proof premises.
