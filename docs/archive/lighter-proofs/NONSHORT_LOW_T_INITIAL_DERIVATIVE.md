# Low-t unit residual: the initial h derivative

## Claim and caller

Use the residual and the complete factored source interface of
[the curvature note](NONSHORT_LOW_T_CURVATURE.md). In particular
\[
 S=96q(q+1)(1+x)^3(17x+76)G_n(t,x,q,1),\qquad
 \mathcal H=\partial_x-\tfrac12\partial_t.
\]
Here the derivative is taken at fixed \(j=x-(1-2t)\) and \(y=q-1\).
This note proves the enlarged initial-face bound
\[
 \boxed{P(x,y):=\mathcal HS(3/8,x,1+y)\ge68>0}
 \tag{I1}
\]
on
\[
 \frac{17}{60}\le x\le\frac37,\qquad
 0\le y\le b(x):=\frac{3931}{8640}-\frac89x.
 \tag{I2}
\]
It supplies the initial derivative required by the h-reduction of the
first-priority low-t unit sign. It also supplies the outer-face base at
\(x=3/7,\ 0\le y\le2/31\). It is a derivative lemma, not by itself a proof
of the full low-t caller.

The enlargement is explicit:
\[
 b(x)-\frac{1-2x}{1+4x}
 =\frac{(60x-17)(277-512x)}{8640(1+4x)}\ge0,
 \qquad b(3/7)=\frac{4477}{60480}>\frac2{31}.
 \tag{I3}
\]
The numerator comparison has three monomials and degree two. Also
\(0<b(x)\le13/64\).

The proof first shows \(P_y<0\), so it suffices to use \(y=b(x)\).
It then proves that this one-variable boundary function is strictly concave,
using a separate directional second-derivative sign on a rectangle.
Only the two scalar endpoints remain. The degree-14 polynomial obtained
by substituting \(b(x)\) and expanding \(P\) is never formed or used.

## 1. Seven small source coefficients

Write \(P=\sum_{i=0}^6c_i(x)y^i\). Differentiate each of the three products
in the curvature note's source interface once by \(\mathcal H\), specialize
\(t=3/8\), and only then collect each coefficient of the opaque event
variable \(q\). Each individual product has x-degree at most eight at
this stage. Changing from \(q\) to \(1+y\) is a linear combination of
these univariate coefficients. The following seven identities therefore
require only univariate degree-eight expansions.

\[
\begin{aligned}
c_{0}(x)={}&\frac{1}{768}\bigl[- 342720 x^{6} - 9255120 x^{5} - 14563956 x^{4} + 14020592 x^{3}\\
&{}- 11376409 x^{2} + 507008 x + 1896960\bigr]
\end{aligned}
\]
This identity has 7 monomials, degree 6, and largest cleared coefficient 14563956.

\[
\begin{aligned}
c_{1}(x)={}&\frac{1}{512}\bigl[- 215936 x^{7} - 3193984 x^{6} - 49549264 x^{5} - 82440236 x^{4}\\
&{}+17689168 x^{3} + 9390957 x^{2} - 6577632 x + 836704\bigr]
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 82440236.

\[
\begin{aligned}
c_{2}(x)={}&\frac{1}{384}\bigl[1096704 x^{8} + 6502512 x^{7} - 7299096 x^{6} - 53154060 x^{5}\\
&{}- 63832296 x^{4} + 2594904 x^{3} + 6734773 x^{2} - 27306340 x\\
&{}-10887034\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 63832296.

\[
\begin{aligned}
c_{3}(x)={}&\frac{1}{768}\bigl[52224 x^{8} + 1862400 x^{7} + 31403808 x^{6} + 570176232 x^{5}\\
&{}+1400713986 x^{4} + 1200322088 x^{3} + 389312905 x^{2} - 6152664 x\\
&{}-23142722\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 1400713986.

\[
\begin{aligned}
c_{4}(x)={}&\frac{1}{256}\bigl[- 504832 x^{8} - 3058080 x^{7} + 17026272 x^{6} + 261773024 x^{5}\\
&{}+609069280 x^{4} + 489774176 x^{3} + 113788653 x^{2} - 22139936 x\\
&{}-8705314\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 609069280.

\[
\begin{aligned}
c_{5}(x)={}&\frac{1}{512}\bigl[557056 x^{8} + 1867520 x^{7} + 6005456 x^{6} + 114615712 x^{5}\\
&{}+270162380 x^{4} + 171690976 x^{3} - 42983895 x^{2} - 71767144 x\\
&{}-16624908\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 270162380.

\[
\begin{aligned}
c_{6}(x)={}&\frac{1}{128}\bigl[8704 x^{8} + 34560 x^{7} - 24544 x^{6} - 126096 x^{5}\\
&{}- 289180 x^{4} - 599256 x^{3} - 640115 x^{2} - 440454 x\\
&{}-119736\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 640115.

## 2. Reduce y to the upper line

The small one-variable claims proved in section 5 imply
\[
 c_1<0,\quad c_2<-48000,\quad
 c_3<3500000x^3,\quad c_4<3500000x^3,\quad c_5,c_6<0.
 \tag{I4}
\]
For clarity the elementary fourth-degree bound used with them is also explicit.
Put \(r=123/320\). Since \(3931/8640<41/90\),
\[
 x^3b(x)\le x^3(41/90-8x/9)
 \le\frac8{27}\left(\frac{123}{320}\right)^4<\frac{13}{2000}.
 \tag{I5}
\]
The middle inequality is the square completion
\[
 \frac8{27}r^4-x^3(41/90-8x/9)
 =\frac8{27}(x-r)^2(3x^2+2rx+r^2).
 \tag{I6}
\]
This is a three-monomial univariate identity of degree four after r is
specialized, with largest cleared coefficient below 300000000000.
All factors on its right have the required sign.

On (I2), \(3+4y\le61/16\) and \(x^3y<13/2000\). Consequently
\[
\begin{aligned}
 P_y
 &\le c_1+y\bigl[-96000+3500000x^3y(3+4y)\bigr]\\
 &\le c_1-\frac{74125}{8}y<0.
\end{aligned}
 \tag{I7}
\]
Thus \(P(x,y)\ge P(x,b(x))\). This is the first dimension reduction.

## 3. A separate concavity claim for the upper line

Set
\[
 \mathcal D=\partial_x-\tfrac89\partial_y,
 \qquad \mathcal D^2P=\sum_{i=0}^6d_i(x)y^i.
\]
We prove \(\mathcal D^2P<0\) on the larger rectangle
\[
 17/60\le x\le3/7,\qquad 0\le y\le13/64.
 \tag{I8}
\]
The identities are obtained from
\(d_i=c_i''-\frac{16}{9}(i+1)c_{i+1}'+\frac{64}{81}(i+2)(i+1)c_{i+2}\),
with missing coefficients zero. Every coefficient polynomial is printed:

\[
\begin{aligned}
d_{0}(x)={}&\frac{1}{31104}\bigl[140378112 x^{8} + 832321536 x^{7} - 771036672 x^{6} - 4734018048 x^{5}\\
&{}+18169663872 x^{4} + 28449682464 x^{3} - 11947322104 x^{2} - 2116654376 x\\
&{}-1604645225\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 28449682464.

\[
\begin{aligned}
d_{1}(x)={}&\frac{1}{20736}\bigl[6684672 x^{8} - 1446150144 x^{7} - 4719688704 x^{6} + 81023809152 x^{5}\\
&{}+226438597248 x^{4} + 162529526752 x^{3} + 8271432440 x^{2} + 924774000 x\\
&{}+3041216381\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 226438597248.

\[
\begin{aligned}
d_{2}(x)={}&\frac{1}{1728}\bigl[- 32309248 x^{8} - 200730624 x^{7} + 1209609216 x^{6} + 15721374128 x^{5}\\
&{}+3784482040 x^{4} - 40672589464 x^{3} - 39376065360 x^{2} - 10690403216 x\\
&{}-422695171\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 40672589464.

\[
\begin{aligned}
d_{3}(x)={}&\frac{1}{10368}\bigl[178257920 x^{8} + 1760739328 x^{7} + 8126316544 x^{6} + 8311610624 x^{5}\\
&{}- 277782650720 x^{4} - 492759115600 x^{3} - 210004068732 x^{2} + 8718338920 x\\
&{}+11567779443\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 492759115600.

\[
\begin{aligned}
d_{4}(x)={}&\frac{1}{3456}\bigl[5570560 x^{8} - 245268480 x^{7} - 1181719552 x^{6} - 3976596960 x^{5}\\
&{}- 27674148640 x^{4} + 5456221440 x^{3} + 67355174080 x^{2} + 44547885096 x\\
&{}+7301691231\bigr]
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 67355174080.

\[
\begin{aligned}
d_{5}(x)={}&\frac{1}{768}\bigl[- 4456448 x^{7} + 31309824 x^{6} + 127078656 x^{5} + 310596240 x^{4}\\
&{}+3512501440 x^{3} + 4977979992 x^{2} + 1627153504 x - 100762629\bigr]
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 4977979992.

\[
\begin{aligned}
d_{6}(x)={}&\frac{1}{64}\bigl[243712 x^{6} + 725760 x^{5} - 368160 x^{4} - 1260960 x^{3}\\
&{}- 1735080 x^{2} - 1797768 x - 640115\bigr]
\end{aligned}
\]
This identity has 7 monomials, degree 6, and largest cleared coefficient 1797768.

To make their signs transparent, round each coefficient of d_i upwards to
an integer. This gives \(d_i\le u_i\) for \(x\ge0\). All the u_i are printed
below; each difference \(u_i-d_i\) has nonnegative coefficients, at most nine
monomials and degree at most eight. Its cleared coefficients are smaller
than the printed denominator of d_i, so these comparison identities introduce
no large coefficients.

\[
\begin{aligned}
u_{0}(x)={}&4514 x^{8} + 26760 x^{7} - 24788 x^{6} - 152199 x^{5}\\
&{}+584159 x^{4} + 914664 x^{3} - 384108 x^{2} - 68050 x\\
&{}-51589
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 914664.

\[
\begin{aligned}
u_{1}(x)={}&323 x^{8} - 69741 x^{7} - 227608 x^{6} + 3907399 x^{5}\\
&{}+10920072 x^{4} + 7838037 x^{3} + 398893 x^{2} + 44598 x\\
&{}+146664
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 10920072.

\[
\begin{aligned}
u_{2}(x)={}&- 18697 x^{8} - 116163 x^{7} + 700006 x^{6} + 9098018 x^{5}\\
&{}+2190094 x^{4} - 23537378 x^{3} - 22787074 x^{2} - 6186575 x\\
&{}-244615
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 23537378.

\[
\begin{aligned}
u_{3}(x)={}&17194 x^{8} + 169825 x^{7} + 783789 x^{6} + 801660 x^{5}\\
&{}- 26792308 x^{4} - 47526920 x^{3} - 20255022 x^{2} + 840890 x\\
&{}+1115720
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 47526920.

\[
\begin{aligned}
u_{4}(x)={}&1612 x^{8} - 70968 x^{7} - 341932 x^{6} - 1150635 x^{5}\\
&{}- 8007566 x^{4} + 1578768 x^{3} + 19489345 x^{2} + 12890014 x\\
&{}+2112758
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 19489345.

\[
\begin{aligned}
u_{5}(x)={}&- 5802 x^{7} + 40768 x^{6} + 165467 x^{5} + 404423 x^{4}\\
&{}+4573570 x^{3} + 6481745 x^{2} + 2118690 x - 131201
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 6481745.

\[
\begin{aligned}
u_{6}(x)={}&3808 x^{6} + 11340 x^{5} - 5752 x^{4} - 19702 x^{3}\\
&{}- 27110 x^{2} - 28090 x - 10001
\end{aligned}
\]
This identity has 7 monomials, degree 6, and largest cleared coefficient 28090.

The separate one-variable claims in section 5 are
\[
\begin{gathered}
 u_1,u_4,u_5>0,\qquad u_3,u_6<0,\\
 -u_0-u_1/24>8400,\\
 -u_2-u_4/24-u_5/112-6u_1>0.
\end{gathered}
 \tag{I9}
\]
Since \(y^2\le169/4096<1/24\) and
\(y^3\le2197/262144<1/112\), these claims give
\[
\begin{aligned}
 \mathcal D^2P
 &\le u_0+u_1y+(u_2+u_4/24+u_5/112)y^2\\
 &\le u_0+u_1(y-6y^2)\\
 &\le u_0+u_1/24<-8400.
\end{aligned}
 \tag{I10}
\]
The last step uses only
\(1/24-y+6y^2=6(y-1/12)^2\), a three-monomial quadratic identity.
Thus x maps to \(P(x,b(x))\) is strictly concave, and its minimum is attained
at one of the two endpoints. This is the second dimension reduction.

## 4. The two scalar endpoints

Substitution into the seven printed c_i gives the following explicit
coefficientwise lower polynomials (each has seven monomials and degree six):
\[
\begin{aligned}
 P(17/60,y)&\ge
 1738-966y-48270y^2+56970y^3+37921y^4-67482y^5-2435y^6,\\
 P(3/7,y)&\ge
 652-4655y-62754y^2+255091y^3+256597y^4-60446y^5-3789y^6.
\end{aligned}
 \tag{I11}
\]
These are scalar evaluations of degree-eight polynomials already printed in
section 1, not additional large polynomial identities. They can be checked
by Horner evaluation of each numerator, rounding each multiplication down
to an integer, then dividing by its positive denominator and rounding down.
All intermediate integers have at most twelve digits.

At \(y=13/64\), downward-rounded Horner evaluation of the first polynomial,
starting with its leading coefficient -2435, gives successively
\[
 -67977,\quad24113,\quad61867,\quad-35704,\quad-8219,\quad68.
\]
At \(y=4477/60480\), the same evaluation of the second polynomial, starting
with -3789, gives
\[
 -60727,\quad252101,\quad273752,\quad-42490,\quad-7801,\quad74.
\]
Every rounding is downwards and y is nonnegative, so these are rigorous
lower bounds. Concavity gives \(P(x,b(x))\ge68\), and (I7) proves (I1).

## 5. Complete small sign checks used above

Here is the verification of every one-variable premise in (I4) and (I9).
For each displayed comparison, the coefficients of the left side minus the
stated multiple of the printed polynomial are nonnegative. This is checked
directly from sections 1 and 3. Each such comparison has at most nine
monomials and degree at most eight; its cleared remainder coefficients are
at most 1000000.

Except for the final polynomial, use \(z=x-1/4\), so
\(1/30\le z\le5/28\). The displayed shifted identities then prove the signs
by replacing a positive monomial's z by 1/30 and a negative monomial's z by
5/28. The resulting strict integer lower bound is stated for each polynomial.
This is an elementary monomial bound on a single interval, with every
polynomial and every shift printed.

### A1

\[
-c_1\ge 100A_{1}(x).
\]

\[
\begin{aligned}
A_{1}(x)={}&4 x^{7} + 62 x^{6} + 967 x^{5} + 1610 x^{4}\\
&{}- 346 x^{3} - 184 x^{2} + 128 x - 17
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 1610.

\[
\begin{aligned}
4096A_{1}(1/4+z)={}&16384 z^{7} + 282624 z^{6} + 4363264 z^{5} + 11792640 z^{4}\\
&{}+7734464 z^{3} + 1290480 z^{2} + 372764 z + 21883
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 11792640.

The stated monomial bounds give \(A_{1}>8\).

### A2

\[
-c_2-48000\ge 100A_{2}(x).
\]

\[
\begin{aligned}
A_{2}(x)={}&- 29 x^{8} - 170 x^{7} + 190 x^{6} + 1384 x^{5}\\
&{}+1662 x^{4} - 68 x^{3} - 176 x^{2} + 711 x\\
&{}-197
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 1662.

\[
\begin{aligned}
65536A_{2}(1/4+z)={}&- 1900544 z^{8} - 14942208 z^{7} - 10371072 z^{6} + 93093888 z^{5}\\
&{}+227359232 z^{4} + 163417088 z^{3} + 40628928 z^{2} + 48625408 z\\
&{}-1535717
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 227359232.

The stated monomial bounds give \(A_{2}>2\).

### A3

\[
3500000x^3-c_3\ge 1000A_{3}(x).
\]

\[
\begin{aligned}
A_{3}(x)={}&- x^{8} - 3 x^{7} - 41 x^{6} - 743 x^{5}\\
&{}- 1824 x^{4} + 1937 x^{3} - 507 x^{2} + 8 x\\
&{}+30
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 1937.

\[
\begin{aligned}
65536A_{3}(1/4+z)={}&- 65536 z^{8} - 327680 z^{7} - 3145728 z^{6} - 53039104 z^{5}\\
&{}- 183048704 z^{4} - 23897856 z^{3} + 9383808 z^{2} - 725488 z\\
&{}+1488803
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 183048704.

The stated monomial bounds give \(A_{3}>15\).

### A4

\[
3500000x^3-c_4\ge 1000A_{4}(x).
\]

\[
\begin{aligned}
A_{4}(x)={}&x^{8} + 11 x^{7} - 67 x^{6} - 1023 x^{5}\\
&{}- 2380 x^{4} + 1586 x^{3} - 445 x^{2} + 86 x\\
&{}+34
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 2380.

\[
\begin{aligned}
65536A_{4}(1/4+z)={}&65536 z^{8} + 851968 z^{7} - 3014656 z^{6} - 72626176 z^{5}\\
&{}- 243484160 z^{4} - 95207680 z^{3} - 20416896 z^{2} - 539280 z\\
&{}+2762813
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 243484160.

The stated monomial bounds give \(A_{4}>18\).

### A5

\[
-c_5\ge 1000A_{5}(x).
\]

\[
\begin{aligned}
A_{5}(x)={}&- 2 x^{8} - 4 x^{7} - 12 x^{6} - 224 x^{5}\\
&{}- 528 x^{4} - 336 x^{3} + 83 x^{2} + 140 x\\
&{}+32
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 528.

\[
\begin{aligned}
32768A_{5}(1/4+z)={}&- 65536 z^{8} - 262144 z^{7} - 737280 z^{6} - 8159232 z^{5}\\
&{}- 26934784 z^{4} - 33043456 z^{3} - 13198912 z^{2} + 2655744 z\\
&{}+2118551
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 33043456.

The stated monomial bounds give \(A_{5}>47\).

### A6

\[
-c_6\ge 100A_{6}(x).
\]

\[
\begin{aligned}
A_{6}(x)={}&- x^{8} - 3 x^{7} + x^{6} + 9 x^{5}\\
&{}+22 x^{4} + 46 x^{3} + 50 x^{2} + 34 x\\
&{}+9
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 50.

\[
\begin{aligned}
65536A_{6}(1/4+z)={}&- 65536 z^{8} - 327680 z^{7} - 393216 z^{6} + 372736 z^{5}\\
&{}+2115072 z^{4} + 4815104 z^{3} + 6169984 z^{2} + 4533520 z\\
&{}+1404995
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 6169984.

The stated monomial bounds give \(A_{6}>23\).

### B1

\[
u_1\ge 1000B_{1}(x).
\]

\[
\begin{aligned}
B_{1}(x)={}&- 70 x^{7} - 228 x^{6} + 3907 x^{5} + 10920 x^{4}\\
&{}+7838 x^{3} + 398 x^{2} + 44 x + 146
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 10920.

\[
\begin{aligned}
8192B_{1}(1/4+z)={}&- 573440 z^{7} - 2871296 z^{6} + 28451840 z^{5} + 127399680 z^{4}\\
&{}+173007296 z^{3} + 89843088 z^{2} + 20234060 z + 2873389
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 173007296.

The stated monomial bounds give \(B_{1}>446\).

### B3

\[
-u_3\ge 1000B_{3}(x).
\]

\[
\begin{aligned}
B_{3}(x)={}&- 18 x^{8} - 170 x^{7} - 784 x^{6} - 802 x^{5}\\
&{}+26792 x^{4} + 47526 x^{3} + 20255 x^{2} - 841 x\\
&{}-1116
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 47526.

\[
\begin{aligned}
32768B_{3}(1/4+z)={}&- 589824 z^{8} - 6750208 z^{7} - 36470784 z^{6} - 72642560 z^{5}\\
&{}+817778176 z^{4} + 2410005248 z^{3} + 2155205120 z^{2} + 650496176 z\\
&{}+25754083
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 2410005248.

The stated monomial bounds give \(B_{3}>1523\).

### B4

\[
u_4\ge 1000B_{4}(x).
\]

\[
\begin{aligned}
B_{4}(x)={}&x^{8} - 71 x^{7} - 342 x^{6} - 1151 x^{5}\\
&{}- 8008 x^{4} + 1578 x^{3} + 19489 x^{2} + 12890 x\\
&{}+2112
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 19489.

\[
\begin{aligned}
65536B_{4}(1/4+z)={}&65536 z^{8} - 4521984 z^{7} - 30441472 z^{6} - 115101696 z^{5}\\
&{}- 642641408 z^{4} - 476178176 z^{3} + 1144793856 z^{2} + 1468351760 z\\
&{}+428915141
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 1468351760.

The stated monomial bounds give \(B_{4}>7259\).

### B5

\[
u_5\ge 1000B_{5}(x).
\]

\[
\begin{aligned}
B_{5}(x)={}&- 6 x^{7} + 40 x^{6} + 165 x^{5} + 404 x^{4}\\
&{}+4573 x^{3} + 6481 x^{2} + 2118 x - 132
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 6481.

\[
\begin{aligned}
8192B_{5}(1/4+z)={}&- 49152 z^{7} + 241664 z^{6} + 1778688 z^{5} + 5279488 z^{4}\\
&{}+41712064 z^{3} + 82659344 z^{2} + 51156044 z + 7174261
\end{aligned}
\]
This identity has 8 monomials, degree 7, and largest cleared coefficient 82659344.

The stated monomial bounds give \(B_{5}>1095\).

### B6

\[
-u_6\ge 100B_{6}(x).
\]

\[
\begin{aligned}
B_{6}(x)={}&- 39 x^{6} - 114 x^{5} + 57 x^{4} + 197 x^{3}\\
&{}+271 x^{2} + 280 x + 100
\end{aligned}
\]
This identity has 7 monomials, degree 6, and largest cleared coefficient 280.

\[
\begin{aligned}
4096B_{6}(1/4+z)={}&- 159744 z^{6} - 706560 z^{5} - 499968 z^{4} + 698624 z^{3}\\
&{}+1720432 z^{2} + 1857720 z + 778721
\end{aligned}
\]
This identity has 7 monomials, degree 6, and largest cleared coefficient 1857720.

The stated monomial bounds give \(B_{6}>205\).

### B0

\[
-u_0-u_1/24\ge 100B_{0}(x).
\]

\[
\begin{aligned}
B_{0}(x)={}&- 46 x^{8} - 239 x^{7} + 342 x^{6} - 107 x^{5}\\
&{}- 10392 x^{4} - 12413 x^{3} + 3674 x^{2} + 661 x\\
&{}+454
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 12413.

\[
\begin{aligned}
32768B_{0}(1/4+z)={}&- 1507328 z^{8} - 10846208 z^{7} - 5136384 z^{6} + 1705984 z^{5}\\
&{}- 339096576 z^{4} - 747116672 z^{3} - 312431264 z^{2} - 15710760 z\\
&{}+20129115
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 747116672.

The stated monomial bounds give \(B_{0}>84\).

### B2

\[
-u_2-u_4/24-u_5/112-6u_1\ge 1000B_{2}(x).
\]

\[
\begin{aligned}
B_{2}(x)={}&16 x^{8} + 537 x^{7} + 679 x^{6} - 32496 x^{5}\\
&{}- 67381 x^{4} - 23598 x^{3} + 19523 x^{2} + 5362 x\\
&{}-723
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 67381.

For this last check use \(z=x-1/3\), so \(-1/20\le z\le2/21\). For a positive even power use the lower bound zero; for every other signed power use the appropriate endpoint. No subdivision is used.

\[
\begin{aligned}
6561B_{2}(1/3+z)={}&104976 z^{8} + 3803193 z^{7} + 13002444 z^{6} - 195857757 z^{5}\\
&{}- 785347731 z^{4} - 976324779 z^{3} - 399292353 z^{2} - 9546141 z\\
&{}+9153529
\end{aligned}
\]
This identity has 9 monomials, degree 8, and largest cleared coefficient 976324779.

The stated monomial bounds give \(B_{2}>565\).

## Budget and logical scope

All source and directional coefficient identities in this note are univariate
of degree at most eight and have at most nine monomials. The largest cleared
coefficient among them is 492759115600 (twelve digits). The auxiliary sign
polynomials have degree at most eight and at most nine monomials; their
shifted identities have coefficients below 2500000000. The line enlargement
and square completions have degrees two, four, and two respectively.

The full bivariate polynomial P is kept as a sum of seven products; no
identity expands that sum across both variables. The line restriction is
handled through its separately proved directional second derivative and
scalar endpoints. No coefficient tables, high-order logarithm bounds,
or interval subdivisions are used. This note changes no Lean file and
makes no claim about measured Lean time or memory.
