# A small proof of the low-t unit face at h = 1/4

## Scope

This proves a terminal face for the **new** residual in
[NONSHORT_LOW_T_SHAPE](NONSHORT_LOW_T_SHAPE.md), with its unchanged
multipliers and incoming bound. It does not prove the full first-priority
three-variable unit-shape sign. The remaining h reduction and its other
boundary faces are still required.

The result is
\[
\boxed{G_n(3/8,x,1+y,1)>0}
\]
whenever
\[
\frac{17}{60}\le x\le\frac37,\qquad
0\le y\le\frac{1-2x}{1+4x}.
\tag{1}
\]
This is exactly the h=1/4 face: j=x-1/4 lies in [1/30,5/28].
All polynomial identities expanded in this proof are univariate and have
degree at most eight and at most nine monomials. Products in the event
variable are assembled by distributivity from these identities.

## 1. The source residual, with its cancellations exposed

Use the product definitions N and P in Section 2 of the shape note, at
\(t=3/8,k=1\). Put
\[
W=x+1,\quad D=17x+76,\quad
V_n=3264x^3+16310x^2+23703x+11172.
\]
The incoming bound is
\[
V_L=\frac{V_n}{192W^2D}.
\]
For free scalar v and ell, let \(G(v,\ell)\) include the floor term
\[
m\left(1+\frac{p^2q}{W^2}-\frac pW\frac{q\ell}{q-1}-v\right),
\qquad p=x+3/8,
\]
as well as the two transported residual terms in that note. This expression
is affine in v and ell. Its full coefficient interface is
\[
G(v,\ell)=\frac{\mathscr C}{49152qW^2}
 +\frac{\mathscr A}{768qW}\,v
 +\frac{q(8x+3)\mathscr H}{6144(q-1)W}\,\ell,
\tag{2}
\]
where
\[
\mathscr A=\sum_{i=0}^4 a_i(x)q^i,\quad
\mathscr C=\sum_{i=0}^5 c_i(x)q^i,\quad
\mathscr H=\sum_{i=0}^3 d_i(x)q^i.
\]
Here are every one of those coefficient polynomials. In (2), first collect
in q; verify each scalar coefficient of v and ell separately. Before
inserting V_L, the factor W cancels in the coefficient of v. Thus the
coefficient checks for (2) have x-degree at most six, not a large common
three-variable expansion.

\[
a_{0}(x)=288 x^{5} + 1260 x^{4} + 2160 x^{3} + 1800 x^{2} + 720 x + 108.
\]

(6 monomials, degree 5.)

\[
a_{1}(x)=- 288 x^{5} - 1440 x^{4} - 2700 x^{3} - 8484 x^{2} + 764 x + 7700.
\]

(6 monomials, degree 5.)

\[
a_{2}(x)=3600 x^{5} + 18360 x^{4} + 34812 x^{3} + 28656 x^{2} + 2172 x - 6432.
\]

(6 monomials, degree 5.)

\[
a_{3}(x)=- 6480 x^{5} - 32400 x^{4} - 66072 x^{3} - 67416 x^{2} - 26976 x + 288.
\]

(6 monomials, degree 5.)

\[
a_{4}(x)=2880 x^{5} + 14220 x^{4} + 30540 x^{3} + 35100 x^{2} + 15675 x.
\]

(5 monomials, degree 5.)

\[
c_{0}(x)=- 13824 x^{6} - 74304 x^{5} - 164160 x^{4} - 190080 x^{3} - 120960 x^{2} - 39744 x - 5184.
\]

(7 monomials, degree 6.)

\[
c_{1}(x)=- 198144 x^{6} - 923904 x^{5} - 1738800 x^{4} - 1285824 x^{3} - 584480 x^{2} - 836032 x - 524336.
\]

(7 monomials, degree 6.)

\[
c_{2}(x)=46080 x^{6} + 570240 x^{5} + 975312 x^{4} + 480444 x^{3} - 521072 x^{2} + 112812 x + 314376.
\]

(7 monomials, degree 6.)

\[
c_{3}(x)=423936 x^{6} + 1380096 x^{5} + 3051408 x^{4} + 5343192 x^{3} + 5416404 x^{2} + 2160480 x + 145620.
\]

(7 monomials, degree 6.)

\[
c_{4}(x)=- 253440 x^{6} - 936000 x^{5} - 2040960 x^{4} - 3273240 x^{3} - 2945220 x^{2} - 1074975 x - 50220.
\]

(7 monomials, degree 6.)

\[
c_{5}(x)=- 4608 x^{6} - 16128 x^{5} - 27360 x^{4} - 33120 x^{3} - 22860 x^{2} - 11808 x - 1728.
\]

(7 monomials, degree 6.)

\[
d_{0}(x)=4176 x^{4} + 11484 x^{3} + 14616 x^{2} + 5340 x + 11984.
\]

(5 monomials, degree 4.)

\[
d_{1}(x)=- 7056 x^{4} - 19404 x^{3} - 24696 x^{2} - 19404 x - 13200.
\]

(5 monomials, degree 4.)

\[
d_{2}(x)=2592 x^{4} + 7128 x^{3} + 9252 x^{2} + 7263 x + 2772.
\]

(5 monomials, degree 4.)

\[
d_{3}(x)=288 x^{4} + 792 x^{3} + 828 x^{2} + 657 x + 108.
\]

(5 monomials, degree 4.)

Insert the single logarithm bound from the shape note,
\[
L(q)=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
The factor q-1 cancels before evaluating q=1. Equation (2) now gives
\[
147456q(q+1)W^3D\,G_n
=3WD(q+1)\mathscr C+(q+1)V_n\mathscr A
 +4W^2Dq(8x+3)\mathscr H(q^2+10q+1).
\tag{3}
\]
Denote this expression by P. All its denominator factors are positive.
With q=1+y, write \(P=\sum_{i=0}^6 C_i(x)y^i\).
All seven coefficient polynomials are printed next.

\[
C_{0}(x)=- 2570400 x^{6} - 11579400 x^{5} + 20231160 x^{4} + 9611930 x^{3} - 15602560 x^{2} + 3793920 x.
\]

(6 monomials, degree 6.)

\[
C_{1}(x)=- 2640960 x^{7} - 38064240 x^{6} - 86017524 x^{5} + 51084660 x^{4} + 95366541 x^{3} - 19510992 x^{2} - 11965152 x + 2276352.
\]

(8 monomials, degree 7.)

\[
C_{2}(x)=- 3290112 x^{8} - 37931040 x^{7} - 125578224 x^{6} - 155046960 x^{5} + 54511676 x^{4} + 206949420 x^{3} + 58530680 x^{2} - 38051816 x - 6400416.
\]

(9 monomials, degree 8.)

\[
C_{3}(x)=- 78336 x^{8} + 15220800 x^{7} + 259700688 x^{6} + 815901492 x^{5} + 1041675896 x^{4} + 673286150 x^{3} + 207692872 x^{2} - 3710852 x - 6671280.
\]

(9 monomials, degree 8.)

\[
C_{4}(x)=2271744 x^{8} + 50047200 x^{7} + 416220768 x^{6} + 1101130752 x^{5} + 1199150640 x^{4} + 516188634 x^{3} + 9044160 x^{2} - 49152972 x - 7778448.
\]

(9 monomials, degree 8.)

\[
C_{5}(x)=- 1253376 x^{8} - 2232000 x^{7} + 62655048 x^{6} + 199922532 x^{5} + 176006160 x^{4} - 40976151 x^{3} - 140397660 x^{2} - 69924132 x - 10104048.
\]

(9 monomials, degree 8.)

\[
C_{6}(x)=- 78336 x^{8} - 604800 x^{7} - 1608192 x^{6} - 2945808 x^{5} - 4773240 x^{4} - 5293836 x^{3} - 4182660 x^{2} - 2093472 x - 295488.
\]

(9 monomials, degree 8.)

For complete small-identity verification of (3), extend a_i,c_i,d_i by
zero outside their displayed index ranges. For each i=0,...,6 the exact
identity to check is
\[
\begin{aligned}
C_i=\sum_{r=i}^6\binom ri\big[&3WD(c_r+c_{r-1})+V_n(a_r+a_{r-1})\\
&+4W^2D(8x+3)(d_{r-1}+10d_{r-2}+d_{r-3})\big].
\end{aligned}
\tag{4}
\]
Each of these seven identities is univariate in x, has degree at most
eight, and at most nine monomials. The three product types have degrees
respectively 2+6, 3+5 and 4+4. Equation (4), followed by distributivity,
is the verification interface; the high-total-degree polynomial P is never
expanded as a two-variable identity. No coefficient in these identities
has more than ten digits.

## 2. Remove the fourth, fifth and sixth event powers

The domain implies
\[
0\le y\le\frac{13}{64},\qquad
y\le b(x):=\frac{15}{16}(1/2-x).
\tag{5}
\]
Indeed (1-2x)/(1+4x) decreases in x, so its maximum is 13/64;
and (1+4x)/2 is at least 16/15.

The univariate estimates proved below are
\[
C_4>0,\quad C_5\ge-144000000x,\quad C_6\ge-6100000x,
\tag{6}
\]
and
\[
B_*:=C_3-6000000x>0,\qquad
E_*:=B_*+\frac{79}{20}C_2>0.
\tag{7}
\]
The scalar inequality
\[
144000000(13/64)^2+6100000(13/64)^3<6000000
\]
then gives, using y>=0 and x>0,
\[
P\ge C_0+C_1y+C_2y^2+B_*y^3.
\tag{8}
\]
When C_2>=0, the last two terms are nonnegative. When C_2<0, put
A=-C_2>0; (7) gives B_*>79A/20. Use the explicit small square completion
\[
\frac{79}{20}y^3-y^2+\frac1{105}
=\frac{79}{20}(y-40/237)^2(y+20/237)
 +\frac{169}{5897745}>0\quad(y\ge0).
\tag{9}
\]
This has degree three and three monomials after cancellation; the cleared
identity has coefficients of at most ten digits. Thus
\[
C_2y^2+B_*y^3\ge\min(0,C_2/105).
\tag{10}
\]
The linear function C_0+C_1y on [0,b(x)] has minimum at an endpoint.
It consequently suffices to prove all four one-variable inequalities
\[
C_0>0,\quad R_0:=C_0+C_2/105>0,\quad
R_b:=C_0+bC_1>0,\quad R:=C_0+bC_1+C_2/105>0.
\tag{11}
\]
This conclusion uses neither a discriminant nor a coefficient table.

## 3. Small one-variable bounds

For the following seven polynomial expressions, put w=3x-1, so
\(-3/20\le w\le2/7\). Every polynomial is printed in full. To check
each displayed integer lower bound, treat its powers separately: an even
positive power of w lies in [0,(2/7)^i], and an odd power lies in
[(-3/20)^i,(2/7)^i]. Multiply by its printed coefficient and round the
resulting rational lower bound downward to an integer. The integer sums
are given in increasing-power order; they are inequalities for the printed
polynomials, not unexplained coefficient signs.

\[
C_5+144000000x= - \frac{139264 w^{8} + 1858112 w^{7} - 53547656 w^{6} - 952275100 w^{5} - 5486930660 w^{4} - 12446803819 w^{3} - 1731032237 w^{2} - 1641614689 w - 401613215}{729}.
\]

Its termwise lower bound is
\[
C_5+144000000x\ge 550909-337781+0-57625+0-100+0-1-1=155401>0.
\]

\[
C_6+6100000x= - \frac{4 \left(2176 w^{8} + 67808 w^{7} + 815776 w^{6} + 5801900 w^{5} + 29733610 w^{4} + 110712929 w^{3} + 285581392 w^{2} + 89989769 w - 55707860\right)}{729}.
\]

Its termwise lower bound is
\[
C_6+6100000x\ge 305667-141078-127917-14169-1088-61-3-1-1=21349>0.
\]

\[
B_*= - \frac{2 \left(4352 w^{8} - 2501984 w^{7} - 147486088 w^{6} - 2055983390 w^{5} - 12843041242 w^{4} - 42763602701 w^{3} - 78044328067 w^{2} - 68577595355 w - 19933150825\right)}{729}.
\]

Its termwise lower bound is
\[
B_*\ge 54686284-28221233+0-395960+0-429+0-1-1=26068660>0.
\]

\[
R_b= \frac{5 \left(586880 w^{8} + 29190880 w^{7} + 316390808 w^{6} + 679532956 w^{5} - 1235995666 w^{4} - 2218174241 w^{3} + 1069336457 w^{2} + 103181041 w + 102872765\right)}{7776}.
\]

Its termwise lower bound is
\[
R_b\ge 66147-9952+0-33267-5297-34+0-1+0=17596>0.
\]

\[
R_0''= - \frac{4 \left(1705984 w^{6} + 54488784 w^{5} + 1235529720 w^{4} + 11285770520 w^{3} + 7354380036 w^{2} - 30887368569 w - 6812260385\right)}{2835}.
\]

Its termwise lower bound is
\[
R_0''\ge 9611654-6537010-847066-371394-11617-147-2=1844418>0.
\]

\[
C_2'= - \frac{4 \left(243712 w^{7} + 9081464 w^{6} + 112159944 w^{5} + 626916380 w^{4} + 1395630412 w^{3} + 18979803 w^{2} - 2939447210 w - 1315841515\right)}{81}.
\]

Its termwise lower bound is
\[
C_2'\ge 64979827-21773684-76513-1607465-206307-10546-244-2=41305066>0.
\]

\[
C_3'= - \frac{2 \left(34816 w^{7} - 17513888 w^{6} - 884916528 w^{5} - 10279916950 w^{4} - 51372164968 w^{3} - 128290808103 w^{2} - 156088656134 w - 69306595355\right)}{243}.
\]

Its termwise lower bound is
\[
C_3'\ge 570424653-192702045+0-1427005+0-554+0-1=376295048>0.
\]

These are seven separate univariate identities, of degrees respectively
8, 8, 8, 8, 6, 7 and 7, with 9, 9, 9, 9, 7, 8 and 8 monomials.
Every cleared coefficient has at most twelve digits. In particular,
\[
R_b>17596,\quad R_0''>1800000,\quad
C_2'>41305066,\quad C_3'>376295048.
\tag{12}
\]
They prove the bounds for C_5,C_6,B_* in (6)--(7). Also
\(E_*'=C_3'-6000000+(79/20)C_2'>0\).
The fully printed polynomial for E_* is

\[
20E_*=- 261485568 x^{8} - 2692136160 x^{7} - 4726665936 x^{6} + 4069320000 x^{5} + 25139940324 x^{4} + 29814727180 x^{3} + 8777781160 x^{2} - 3200310504 x - 639058464.
\]

(9 monomials, degree 8.)

At the left endpoint, direct rational evaluation gives
\(E_*(17/60)>179000\). Hence E_*>0 throughout (1).

For C_4, its derivative is

\[
C_4'=18173952 x^{7} + 350330400 x^{6} + 2497324608 x^{5} + 5505653760 x^{4} + 4796602560 x^{3} + 1548565902 x^{2} + 18088320 x - 49152972.
\]

(8 monomials, degree 7.)

All its nonconstant coefficients are positive. Already the x^2 term
is greater than the absolute constant term when x>=1/4. Thus C_4'>0,
and C_4(17/60)>723000 proves the remaining assertion in (6).

The two endpoint inequalities just used can be verified from the printed
polynomials by rational Horner evaluation. Integer rounding at each Horner
step gives the same strict integer bounds, so no large integer coefficient
expansion at 17/60 is needed.

For C_0, the needed derivatives are

\[
C_0'=- 15422400 x^{5} - 57897000 x^{4} + 80924640 x^{3} + 28835790 x^{2} - 31205120 x + 3793920.
\]

(6 monomials, degree 5.)

\[
C_0'''=- 308448000 x^{3} - 694764000 x^{2} + 485547840 x + 57671580.
\]

(4 monomials, degree 3.)

Using x<=3/7, the last polynomial is at least
\[
57671580+x\left(485547840-694764000\frac37
                         -308448000\frac9{49}\right)>0.
\]
Thus C_0' is convex. Its endpoint values satisfy
\(C_0'(17/60)<-1000000\) and \(C_0'(3/7)<-80000\),
so C_0'<0 on the whole interval. Finally C_0(3/7)>15000; hence C_0>0.

For R_0, its full polynomial is

\[
105R_0=- 3290112 x^{8} - 37931040 x^{7} - 395470224 x^{6} - 1370883960 x^{5} + 2178783476 x^{4} + 1216202070 x^{3} - 1579738120 x^{2} + 360309784 x - 6400416.
\]

(9 monomials, degree 8.)

Its second derivative was printed and bounded in (12). Direct endpoint
arithmetic at x_0=3/8 gives
\[
R_0(x_0)>23600,\qquad |R_0'(x_0)|<55000.
\]
Taylor's inequality using R_0''>1800000, followed by completing a square,
gives for every x in (1)
\[
\begin{aligned}
R_0(x)&>23600+R_0'(x_0)(x-x_0)+900000(x-x_0)^2\\
&\ge23600-\frac{55000^2}{3600000}>0.
\end{aligned}
\tag{13}
\]
The first three inequalities in (11) are proved.

## 4. The tight remaining univariate sign

The remaining polynomial is

\[
3360R=8213740416 x^{8} + 114529050720 x^{7} + 198348975432 x^{6} - 340262566020 x^{5} - 150225193418 x^{4} + 250580393115 x^{3} - 43591203440 x^{2} - 14485710112 x + 3380441088.
\]

(9 monomials, degree 8.)

Use the following smaller integer polynomial:

\[
Q(x)=24445 x^{8} + 340860 x^{7} + 590324 x^{6} - 1012687 x^{5} - 447099 x^{4} + 745774 x^{3} - 129736 x^{2} - 43113 x + 10060.
\]

(9 monomials, degree 8.)

There is the explicit positive-error identity

\[
3360(R-100Q)=220416 x^{8} + 90720 x^{7} + 111432 x^{6} + 265980 x^{5} + 70582 x^{4} + 329115 x^{3} + 92560 x^{2} + 257888 x + 281088.
\]

(9 monomials, degree 8.)

It has nine monomials and degree eight, and all coefficients are
nonnegative. Thus R>=100Q for x>=0. It remains to prove Q>0 on
[17/60,3/7]; we prove it on the slightly larger [1/4,3/7].
The three derivative polynomials used are

\[
Q'=195560 x^{7} + 2386020 x^{6} + 3541944 x^{5} - 5063435 x^{4} - 1788396 x^{3} + 2237322 x^{2} - 259472 x - 43113.
\]

(8 monomials, degree 7.)

\[
Q''=1368920 x^{6} + 14316120 x^{5} + 17709720 x^{4} - 20253740 x^{3} - 5365188 x^{2} + 4474644 x - 259472.
\]

(7 monomials, degree 6.)

\[
Q'''=8213520 x^{5} + 71580600 x^{4} + 70838880 x^{3} - 60761220 x^{2} - 10730376 x + 4474644.
\]

(6 monomials, degree 5.)

First Q'''<0. Dividing its printed expression by 12, replace each
positive term of degree at least three by its upper bound as a multiple
of x^2. On [1/4,1/3] this yields
\[
Q'''/12\le-A_1x^2-894198x+372887<0,
\]
where
\[
A_1=5063435-684460/27-5965050/9-5903240/3>2400000.
\]
Indeed the right side is decreasing for x>0, and at x=1/4 it is
less than \(-2400000/16-894198/4+372887<0\).
On [1/3,3/7] the same argument gives
\[
Q'''/12\le-A_2x^2-894198x+372887<0,
\]
where
\[
A_2=5063435-684460(3/7)^3-5965050(3/7)^2-5903240(3/7)
>1380000.
\]
At x=1/3 this upper bound is less than
\(-1380000/9-894198/3+372887<0\), and it decreases thereafter.
These are scalar comparisons and quadratic inequalities; the only
interval split is x=1/3.

On [1/4,1/3], Q'''<0 and Q''(1/3)>160000 imply Q''>160000.
Also
\[
Q(3/10)>9,\qquad 0<Q'(3/10)<1500.
\]
Taylor's inequality and a square completion therefore give
\[
Q(x)>9+Q'(3/10)(x-3/10)+80000(x-3/10)^2
\ge9-\frac{1500^2}{320000}=\frac{63}{32}>0.
\tag{14}
\]
On [1/3,3/7], Q' is concave because Q'''<0, and its endpoint values
satisfy Q'(1/3)>8000 and Q'(3/7)>11000. Thus Q'>0 there.
Since Q(1/3)>0 by (14), Q>0 throughout this second interval too.
This proves R>0, completing (11).

Equations (8)--(11) now prove P>0. The positive normalization (3)
proves the terminal-face claim.

## Budget and remaining work

The proof reduces y to a cubic square completion and four univariate signs.
Every polynomial entering a sign check is printed. The polynomial coefficient
identities in (2)--(4), the shifted identities of Section 3, and the rounded
error identity all have at most nine monomials and degree at most eight in
one variable. Their cleared coefficients have at most twelve digits.
The derivative and square-completion arguments keep their positive factors.
All scalar endpoint estimates can be checked by Horner evaluation with
integer rounding; none is a sampled claim or a generated coefficient table.

Exact symbolic arithmetic checked the displayed identities, coefficient
counts and rational comparisons. The proof is the displayed algebra and
inequalities. No Lean compilation, Lake, typechecking or CI was run.
The other lower-h faces and a valid reduction to them remain open;
this note alone does not close the original first-priority sign.
