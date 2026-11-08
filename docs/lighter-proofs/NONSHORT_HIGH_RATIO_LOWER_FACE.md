# High-ratio lower shape: the h=1/4 terminal face

## 1. Exact statement and source

Use the constant multipliers a=4, m=1 and the incoming majorant
\[
 T_L(x)=\frac{912-401x}{24(17x+76)}.
\]
Let \(G_{4,L}\) be the residual of `NONSHORT_HIGH_RATIO_LOWER_REDUCTION.md`,
with this incoming majorant and the same fixed rational logarithm bound
\[
 L(q)=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
At \(t=3/8\), \(k_0=29t^2/4=261/256\), put
\[
 P(x,y)=96q(q+1)(1+x)^3(17x+76)G_{4,L}(3/8,x,q,k_0),\qquad q=1+y.
\]
We prove the quantitative face sign
\[
 \boxed{P(x,y)\ge13/4>0}
 \quad\left(\frac{17}{60}\le x\le\frac37,\quad
 0\le y\le\frac{1-2x}{1+4x}\right).
 \tag{F1}
\]
The positive normalization therefore gives \(G_{4,L}>0\) on exactly the needed face.
This note supplies a terminal dependency of the high-ratio reduction; it does not
by itself assert a sign in the interior high-ratio region.

Write \(P=\sum_{i=0}^6 C_i(x)y^i\). The source affine interface is
\(C/(4qW^2)+Av/(qW)-pqB\ell/(W(q-1))\), with the W cancellation carried
out before the incoming/logarithm substitutions, as in the reduction note.
At t=3/8 its seven coefficient identities are univariate in x of degree at most 8,
with at most nine monomials. The complete coefficients are:

\[
\begin{aligned}
C_0(x)={}&\frac{5}{262144}\bigl[- 100270080 x^{6} - 448627200 x^{5} - 520627200 x^{4} + 127109951 x^{3}\\
&{}+247628099 x^{2} - 59785932 x\bigr]
\end{aligned}
\]
This polynomial has 6 monomials and total degree 6.
\[
\begin{aligned}
C_1(x)={}&\frac{3}{524288}\bigl[- 343408640 x^{7} - 5917941760 x^{6} - 18081487360 x^{5} - 18318174128 x^{4}\\
&{}- 827157663 x^{3} + 5618789099 x^{2} + 394645010 x - 119571864\bigr]
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
C_2(x)={}&\frac{1}{524288}\bigl[- 1283457024 x^{8} - 17584619520 x^{7} - 100823052288 x^{6} - 238799235072 x^{5}\\
&{}- 250663749064 x^{4} - 92438377608 x^{3} + 10322714837 x^{2} + 6313406737 x\\
&{}+581438076\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
C_3(x)={}&\frac{1}{262144}\bigl[- 1711276032 x^{8} - 19198771200 x^{7} - 85299277824 x^{6} - 181561992576 x^{5}\\
&{}- 196041535040 x^{4} - 100902544067 x^{3} - 19730788975 x^{2} - 1056660604 x\\
&{}+344099424\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
C_4(x)={}&\frac{3}{262144}\bigl[- 499122176 x^{8} - 5071011840 x^{7} - 19646820352 x^{6} - 39280794368 x^{5}\\
&{}- 44143409640 x^{4} - 28049313661 x^{3} - 10344557880 x^{2} - 2465497287 x\\
&{}-192537108\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
C_5(x)={}&\frac{3}{524288}\bigl[- 320864256 x^{8} - 3062169600 x^{7} - 10882281472 x^{6} - 21073964288 x^{5}\\
&{}- 25161799440 x^{4} - 18988812231 x^{3} - 9383326785 x^{2} - 2975776002 x\\
&{}-339060168\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
C_6(x)={}&\frac{3}{524288}\bigl[- 8912896 x^{8} - 68812800 x^{7} - 183672832 x^{6} - 340674048 x^{5}\\
&{}- 557281240 x^{4} - 621688296 x^{3} - 494998785 x^{2} - 248859837 x\\
&{}-35169228\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
### Staging the source coefficient with the largest cancellation

Keep the three terms of the affine source separate:
\[
 P^{c}=24WD(q+1)C,\quad P^{v}=4(q+1)AV_n,\quad
 P^{\ell}=-16W^2DpqB(q^2+10q+1).
\]
The symbols on the right are the source polynomials of the reduction note, specialized
to t=3/8 before expansion. For the y² coefficient define
\[
 K_0=\frac{524288}{3}[y^2]P^c,\qquad
 K_1=4096[y^2]P^v,\qquad K_2=512[y^2]P^\ell.
\]
Cancel these scalar normalizations before expanding. The resulting complete polynomials are:

\[
\begin{aligned}
K_0(x)={}&2566914048 x^{8} + 24096276480 x^{7} + 90733572096 x^{6} + 219478938624 x^{5}\\
&{}+378483481960 x^{4} + 428850375208 x^{3} + 274649542855 x^{2} + 77592807131 x\\
&{}+3584886484
\end{aligned}
\]
This polynomial has 9 monomials and degree 8.
\[
\begin{aligned}
K_1(x)={}&- 40108032 x^{8} - 413491200 x^{7} - 1857525504 x^{6} - 4836100776 x^{5}\\
&{}- 7939380732 x^{4} - 8113479694 x^{3} - 4676577619 x^{2} - 1137900879 x\\
&{}+17640588
\end{aligned}
\]
This polynomial has 9 monomials and degree 8.
\[
\begin{aligned}
K_2(x)={}&- 3760128 x^{8} - 36080640 x^{7} - 132090336 x^{6} - 271694484 x^{5}\\
&{}- 361204552 x^{4} - 332484475 x^{3} - 209984354 x^{2} - 78919631 x\\
&{}-12139860
\end{aligned}
\]
This polynomial has 9 monomials and degree 8.
Inside each source term, combine the q coefficients **before multiplying by
the outer x factors**. In particular, write
\[
 K_0=WDJ_0,\qquad K_1=V_*J_1,\qquad
 K_2=W^2D(8x+3)J_2,
\]
where \(V_*=3264x^3+16310x^2+23703x+11172\), and the complete inner polynomials are
\[
\begin{aligned}
 J_0={}&150994944x^6+591396864x^5+1426944000x^4+2460410880x^3\\
      &+2424560360x^2+963237344x+47169559,\\
 J_1={}&-12288x^5-65280x^4-153660x^3-197700x^2-105203x+1579,\\
 J_2={}&-27648x^4-76032x^3-108828x^2-85752x-53245.
\end{aligned}
\]
These have respectively 7, 6, and 5 monomials and degrees 6, 5, and 4;
\(V_*\) has four monomials and degree 3. To obtain them, let
\(\widehat C_m,\widehat A_m,\widehat B_m\) denote the q coefficients of the
three affine source polynomials in the reduction note, specialized to t=3/8.
Then combine
\[
\begin{aligned}
 J_0&=4194304\sum_m m^2\widehat C_m,\\
 J_1&=2048\sum_m m^2\widehat A_m,\\
 J_2&=-1024\sum_m(6m^2+18m+13)\widehat B_m.
\end{aligned}
\]
The first inner sum has coefficients of absolute value at most 7468886016
before collection, and its collected coefficients are at most 2460410880.
Only after this small identity is checked should WD be multiplied in.
Multiplying each separate q-coefficient contribution by WD first would create
an unnecessary 13-digit intermediate and is not the stated proof.

Do not collect \(3K_0+128K_1+1024K_2\) in one step. Use instead
\[
 E_0=K_0+64K_1,\qquad E_1=2E_0+K_0,\qquad
 524288C_2=E_1+1024K_2,
\]
where
\[
\begin{aligned}
E_0(x)={}&- 2367160320 x^{7} - 28148060160 x^{6} - 90031511040 x^{5} - 129636884888 x^{4}\\
&{}- 90412325208 x^{3} - 24651424761 x^{2} + 4767150875 x + 4713884116
\end{aligned}
\]
This polynomial has 8 monomials and degree 7.
\[
\begin{aligned}
E_1(x)={}&2566914048 x^{8} + 19361955840 x^{7} + 34437451776 x^{6} + 39415916544 x^{5}\\
&{}+119209712184 x^{4} + 248025724792 x^{3} + 225346693333 x^{2} + 87127108881 x\\
&{}+13012654716
\end{aligned}
\]
This polynomial has 9 monomials and degree 8.
The three collected outputs have respectively 8, 9, and 9 monomials; each side
before collection uses at most nine monomials and univariate degree at most 8.
Every individual polynomial contribution before collection
has coefficients of absolute value at most 519262700416; every collected coefficient
also stays within 12 digits. The other six y coefficients can be checked directly
from the three separate affine terms: their largest coefficient before collection,
with denominators cleared, is 916895167299. Thus this source interface does not
require even an intermediate 13-digit polynomial coefficient.


## 2. Concavity in y and a low-degree upper face

We first check \(C_2,C_3,C_4,C_5,C_6<0\).
All coefficients printed for C4 and C5 are negative.
For C6, its factored form is
\[
 C_6=-\frac3{524288}(x+1)(17x+76)(8x^2+16x+3)
             (256x^2-128x+591)(256x^2+192x+261),
\]
where \(256x^2-128x+591=256(x-1/4)^2+575>0\).
This square completion has three monomials and degree 2.
For C3, factor out the minus sign: the polynomial \(-262144C_3\) is bounded below by
\(19730788975x^2-344099424>0\) when x≥1/4.

For C2 let \(K=-524288C_2\), the complete polynomial already printed above.
Ignore its positive differentiated terms of degree at least 3 without expanding
those numerical prefactors. For x≥1/4,
\[
 K'\ge277315132824x^2-20645429674x-6313406737
 \ge48683353532x-6313406737\ge5857431646>0.
 \tag{F2}
\]
The two lower polynomials in (F2) have three and two monomials, of degrees 2 and 1.
The downward-rounded Horner chain for K at x=9/32 is
\[
\begin{gathered}
1283457024,\ 17945591808,\ 105870249984,\ 268575242880,\\
326200536124,\ 184182278392,\ 41478550960,\ 5352435720,\ 923934470.
\end{gathered}
\]
Here each next entry is the floor of 9/32 times the previous entry plus the next
printed coefficient of K. Thus K(9/32)≥923934470>0, and
x≥17/60>9/32 proves C2<0. These are scalar Horner steps, not sign premises from a coefficient table.

Consequently \(P_{yy}<0\) for y≥0. Define
\[
 b(x)=467/960-x.
\]
The following three-monomial quadratic identity proves that it is an upper bound
for the original event face:
\[
 b(x)-\frac{1-2x}{1+4x}
 =\frac{(60x-17)(29-64x)}{960(1+4x)}\ge0.
 \tag{F3}
\]
On the stated x interval, \(0<b(x)\le13/64\).
It suffices to prove P(x,0)>20 and P(x,b(x))≥13/4.

## 3. The y=0 face

The constant coefficient is \(C_0=-5xR(x)/262144\), where
\[
\begin{aligned}
R(x)={}&100270080 x^{5} + 448627200 x^{4} + 520627200 x^{3} - 127109951 x^{2}\\
&{}- 247628099 x + 59785932
\end{aligned}
\]
This polynomial has 6 monomials and total degree 5.
\[
\begin{aligned}
R^{\prime\prime}(x)={}&2\bigl[1002700800 x^{3} + 2691763200 x^{2} + 1561881600 x - 127109951
\bigr]
\end{aligned}
\]
This polynomial has 4 monomials and total degree 3.
For x≥1/4, \(R''\ge526720898>0\), so R is convex.
At the two endpoints, upward-rounded Horner chains are
\[
\begin{aligned}
 x=17/60:\;&100270080,\ 477037056,\ 655787700,\ 58696564,\ -230997405,\ -5663332;\\
 x=3/7:\;&100270080,\ 491600092,\ 731312954,\ 186309887,\ -167781004,\ -12120212.
\end{aligned}
\]
Convexity gives R<−5000000 throughout the interval. Hence
\[
 C_0>\frac{25\cdot10^6x}{262144}>20.
 \tag{F4}
\]

## 4. A small ninth derivative controls the line face

Let \(F(x)=P(x,b(x))\) and \(\mathcal D=\partial_x-\partial_y\).
Then \(F^{(k)}(x)=\mathcal D^kP(x,b(x))\).
Differentiate the seven source products \(C_i(x)y^i\) **nine times before expansion**.
Cancel factorials before collecting any coefficient: for a source monomial
\(c x^n y^i\), its normalized contribution is
\[
 \frac{512}{8505}\mathcal D^9(c x^n y^i)
 =\frac{65536c}{3}
   \sum_r(-1)^r\binom{n}{9-r}\binom{i}{r}
                 x^{n-9+r}y^{i-r},
\]
where the sum includes only nonzero binomial terms.
The contributions from \(C_0,C_1\) vanish. The five remaining source
contributions have respectively 3, 6, 10, 15, and 21 monomials, and degrees
1, 2, 3, 4, and 5. There are only 55 monomial contributions before collection.
After this factorial cancellation, every individual contribution has an integer
coefficient of absolute value at most 40808555520; the same bound holds for
each of the five separately expanded source contributions. Thus the budget
holds before cancellation between different source contributions as well.
The result has total degree only 5:
\[
 \frac{512}{8505}\mathcal D^9P=A_0(x)+A_1(x)y+A_2(x)y^2
                                  +A_3(x)y^3+A_4(x)y^4+6684672y^5.
 \tag{F5}
\]
This identity has 21 monomials in the two free variables x,y, total degree 5,
and primitive integer coefficients of at most 11 digits.
Its complete coefficient polynomials are:

\[
\begin{aligned}
A_0(x)={}&- 62390272 x^{5} + 2506506240 x^{4} + 5950099456 x^{3} - 2651399552 x^{2}\\
&{}- 5806179276 x - 377104027
\end{aligned}
\]
This polynomial has 6 monomials and total degree 5.
\[
\begin{aligned}
A_1(x)={}&2\bigl[233963520 x^{4} - 4711956480 x^{3} - 12074617856 x^{2} - 3728248512 x\\
&{}+1100407777\bigr]
\end{aligned}
\]
This polynomial has 5 monomials and total degree 4.
\[
\begin{aligned}
A_2(x)={}&64\bigl[- 14622720 x^{3} + 133136640 x^{2} + 292784352 x + 90396707
\bigr]
\end{aligned}
\]
This polynomial has 4 monomials and total degree 3.
\[
\begin{aligned}
A_3(x)={}&4096\bigl[152320 x^{2} - 489360 x - 700539
\bigr]
\end{aligned}
\]
This polynomial has 3 monomials and total degree 2.
\[
\begin{aligned}
A_4(x)={}&245760\bigl[- 544 x + 291
\bigr]
\end{aligned}
\]
This polynomial has 2 monomials and total degree 1.
On the larger rectangle \(1/4\le x\le1/2\), \(0\le y\le13/64\), the signs are elementary.
For A0, use \(x^4\le x^3/2\) and \(x^3\le x/4\), and discard its other negative terms:
\[
 A_0\le-4005341132x-377104027\le-1378439310<-1300000000.
\]
For A1, use \(x^4\le x/8\), x≥1/4, and x²≥1/16:
\[
 A_1\le-7398006144x-24149235712x^2+2200815554
 \le-1158013214<0.
\]
For A3, use \(x^2\le x/2\), which immediately gives A3<0.
The positive-part bounds for the remaining coefficients are
\[
 A_2\le17284674752<18000000000,\quad A_4\le71516160<72000000,
 \quad6684672<7000000.
\]
All displayed comparison polynomials have at most three monomials and degree at most 2.
Since \(y^2<1/24\), \(y^4<1/576\), \(y^5<1/2304\),
\[
 \frac{512}{8505}\mathcal D^9P
 <-1300000000+\frac{18000000000}{24}
       +\frac{72000000}{576}+\frac{7000000}{2304}
 <-500000000<0.
 \tag{F6}
\]
In particular \(F^{(9)}<0\) along the whole line face.
No expanded fourth- or seventh-derivative polynomial is needed.

## 5. Explicit scalar jets

Here are the scalar checks used to integrate the high-derivative sign.
They are obtained without expanding F, which would have degree 14.
For a fixed x=s, compute the coefficients of \(\mathcal D^kP(s,y)\) by
\[
 [y^i]\mathcal D^kP(s,y)
 =\sum_{r=0}^{\min(k,6-i)}(-1)^r\binom{k}{r}
       \frac{(i+r)!}{i!}\,C_{i+r}^{(k-r)}(s).
 \tag{F7}
\]
After differentiation and evaluation at s, these are scalar comparisons involving
the printed C_i. Round each coefficient in the required direction before collecting
any large common denominator. The resulting degree-6 polynomials are printed below.
For a lower bound use downward rounding; for an upper bound use upward rounding.
Each listed Horner chain applies the same floor or ceiling after each multiplication
by the displayed y value. Thus every endpoint bound is directly checkable from the text.

At \(x=\frac{17}{60}\), \(y=b(x)=\frac{13}{64}\), \(F^{(7)}(x)\ge1000J_{7L}(y)\), where
\[
\begin{aligned}
J_{7L}(y)={}&- 2568 y^{6} - 50421 y^{5} + 1853639 y^{4} - 5589773 y^{3}\\
&{}- 1503506 y^{2} + 1423429 y + 1273770
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-2568,\ -50943,\ 1843291,\ -5215355,\ -2562875,\ 902845,\ 1457160 .
\]
At \(x=\frac{3}{7}\), \(y=b(x)=\frac{389}{6720}\), \(F^{(7)}(x)\ge1000J_{7R}(y)\), where
\[
\begin{aligned}
J_{7R}(y)={}&- 2866 y^{6} - 44603 y^{5} + 2257089 y^{4} - 8652984 y^{3}\\
&{}+391939 y^{2} + 3655820 y + 1675052
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-2866,\ -44769,\ 2254497,\ -8522479,\ -101401,\ 3649950,\ 1886336 .
\]
At \(x=\frac{17}{60}\), \(y=b(x)=\frac{13}{64}\), \(F^{(5)}(x)\le1000J_{5L}(y)\), where
\[
\begin{aligned}
J_{5L}(y)={}&- 535 y^{6} - 25560 y^{5} + 113561 y^{4} + 74002 y^{3}\\
&{}- 10356 y^{2} - 80118 y - 19636
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The upward Horner chain is
\[
-535,\ -25668,\ 108348,\ 96011,\ 9147,\ -78260,\ -35532 .
\]
At \(x=\frac{3}{7}\), \(y=b(x)=\frac{389}{6720}\), \(F^{(5)}(x)\le1000J_{5R}(y)\), where
\[
\begin{aligned}
J_{5R}(y)={}&- 767 y^{6} - 34509 y^{5} + 196144 y^{4} + 59431 y^{3}\\
&{}- 115146 y^{2} - 159634 y - 19975
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The upward Horner chain is
\[
-767,\ -34553,\ 194144,\ 70670,\ -111055,\ -166062,\ -29587 .
\]
At \(x=\frac{17}{60}\), \(y=b(x)=\frac{13}{64}\), \(F^{(4)}(x)\le1000J_{4L}(y)\), where
\[
\begin{aligned}
J_{4L}(y)={}&- 181 y^{6} - 8369 y^{5} + 10192 y^{4} + 21336 y^{3}\\
&{}+19504 y^{2} + 1684 y - 2004
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The upward Horner chain is
\[
-181,\ -8405,\ 8485,\ 23060,\ 24189,\ 6598,\ -663 .
\]
At \(x=\frac{17}{60}\), \(y=b(x)=\frac{13}{64}\), \(F^{(2)}(x)\geJ_{2L}(y)\), where
\[
\begin{aligned}
J_{2L}(y)={}&- 15906 y^{6} - 448066 y^{5} - 636305 y^{4} - 317799 y^{3}\\
&{}+59064 y^{2} + 94853 y - 16291
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-15906,\ -451297,\ -727975,\ -465669,\ -35526,\ 87636,\ 1510 .
\]
At \(x=\frac{2}{5}\), \(y=b(x)=\frac{83}{960}\), \(F^{(2)}(x)\geJ_{2M}(y)\), where
\[
\begin{aligned}
J_{2M}(y)={}&- 23809 y^{6} - 776244 y^{5} - 1110403 y^{4} - 434257 y^{3}\\
&{}+401901 y^{2} + 305746 y - 23122
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-23809,\ -778303,\ -1177694,\ -536079,\ 355552,\ 336486,\ 5970 .
\]
At \(x=\frac{2}{5}\), \(y=b(x)=\frac{83}{960}\), \(F^{(1)}(x)\geJ_{1M}(y)\), where
\[
\begin{aligned}
J_{1M}(y)={}&- 6540 y^{6} - 159432 y^{5} - 331916 y^{4} - 265158 y^{3}\\
&{}- 56329 y^{2} + 23405 y - 1129
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-6540,\ -159998,\ -345750,\ -295051,\ -81839,\ 16329,\ 282 .
\]
At \(x=\frac{3}{7}\), \(y=b(x)=\frac{389}{6720}\), \(F^{(1)}(x)\geJ_{1R}(y)\), where
\[
\begin{aligned}
J_{1R}(y)={}&- 7255 y^{6} - 184265 y^{5} - 390163 y^{4} - 318867 y^{3}\\
&{}- 67793 y^{2} + 29710 y - 1062
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-7255,\ -184685,\ -400854,\ -342072,\ -87595,\ 24639,\ 364 .
\]
At \(x=\frac{11}{30}\), \(y=b(x)=\frac{23}{192}\), \(F^{(0)}(x)\geJ_{0C}(y)\), where
\[
\begin{aligned}
J_{0C}(y)={}&- 1354 y^{6} - 24328 y^{5} - 57000 y^{4} - 48226 y^{3}\\
&{}- 12679 y^{2} + 1568 y + 95
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-1354,\ -24491,\ -59934,\ -55406,\ -19317,\ -747,\ 5 .
\]
At \(x=\frac{11}{30}\), \(y=b(x)=\frac{23}{192}\), \(F^{(1)}(x)\geJ_{1Clo}(y)\), where
\[
\begin{aligned}
J_{1Clo}(y)={}&- 5790 y^{6} - 134184 y^{5} - 273073 y^{4} - 210766 y^{3}\\
&{}- 43631 y^{2} + 17884 y - 1075
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The downward Horner chain is
\[
-5790,\ -134878,\ -289231,\ -245414,\ -73030,\ 9135,\ 19 .
\]
At \(x=\frac{11}{30}\), \(y=b(x)=\frac{23}{192}\), \(F^{(1)}(x)\leJ_{1Chi}(y)\), where
\[
\begin{aligned}
J_{1Chi}(y)={}&- 5789 y^{6} - 134183 y^{5} - 273072 y^{4} - 210765 y^{3}\\
&{}- 43630 y^{2} + 17885 y - 1074
\end{aligned}
\]
This polynomial has 7 monomials and total degree 6.
The upward Horner chain is
\[
-5789,\ -134876,\ -289229,\ -245412,\ -73028,\ 9137,\ 21 .
\]
The chains give the following bounds, with \(L=17/60\), \(R=3/7\), \(M=2/5\), \(c=11/30\):
\[
\begin{aligned}
 &F^{(7)}(L)>0,\quad F^{(7)}(R)>0,\\
 &F^{(5)}(L)<0,\quad F^{(5)}(R)<0,\quad F^{(4)}(L)<0,\\
 &F''(L)\ge1510,\quad F''(M)\ge5970,\\
 &F'(M)\ge282,\quad F'(R)\ge364,\\
 &F(c)\ge5,\qquad 19\le F'(c)\le21.
\end{aligned}
 \tag{F8}
\]

## 6. Integrate the derivative signs and finish

By (F6), \(F^{(7)}\) is concave. Its two positive endpoint values in (F8)
therefore prove \(F^{(7)}>0\) everywhere.
It follows that \(F^{(5)}\) is convex; its two negative endpoint values prove
\(F^{(5)}<0\). Hence \(F^{(4)}\) decreases, and its negative left endpoint
proves \(F^{(4)}<0\). Thus F'' is concave.

On \([L,M]\), the positive endpoint bounds for F'' show F''>0.
Convexity of F gives the tangent lower bound
\[
 F(x)\ge F(c)+F'(c)(x-c)\ge5-21/12=13/4,
 \qquad L\le x\le M.
 \tag{F9}
\]
Here c lies in that interval, \(c-L=1/12\), and \(F'(c)>0\).

On \([M,R]\), concavity of F'' and \(F''(M)>0\) mean F'' can cross from
positive to negative at most once. Therefore F' first increases and then decreases,
if it changes monotonicity at all. Its minimum is at an endpoint, and (F8) shows
both endpoint values are positive. Thus F increases on \([M,R]\), and
\(F(x)\ge F(M)\ge13/4\) there as well.

We have proved P(x,b(x))≥13/4. Combine this with P(x,0)>20, concavity in y,
and (F3) to obtain (F1) on the unchanged original face.

The only interval split in this proof is x=2/5. Every polynomial sign premise is
printed. The largest expanded identity is the 21-monomial degree-5 ninth derivative;
the source coefficient identities have at most nine monomials and degree at most 8.

