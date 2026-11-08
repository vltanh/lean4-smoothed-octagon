# Central S1: reduce the second test to two fixed shapes

Use the exact central source of [the reduction note](SHORT_CENTRAL_REDUCTION.md), and fix
\[
 u=19/25,\qquad b=x+(10/13)(a-1),\qquad8/5\le x\le2,\quad1\le a\le7/6.
\]
Norm and beta monotonicity allow precisely this comparison for the original second test. We prove
\[
 \boxed{F_1(x,a,b,19/25)\ge
 \min\{F_1(x,1,x,19/25),F_1(x,7/6,x+5/39,19/25)\}.}\tag{1}
\]
This comparison holds on the full rectangle, so it also holds on the actual central cap domain.
Its [two terminal signs](SHORT_CENTRAL_F1_TERMINALS.md) close the remaining step.

## 1. Keep the rational source separate until differentiation

Set d=23/13, B=da+x−10/13, K=X+a², and V=aBK. Then R1=N/V, where the complete small source polynomials are
\[
\begin{aligned}
16900N={}&- 41075 a^{4} - 70440 a^{3} x + 30800 a^{3}\\
&{}+ 3120 a^{2} x^{3} - 34582 a^{2} x^{2} + 94428 a^{2} x\\
&{}- 5520 a^{2} - 2184 a x^{4} + 20540 a x^{3}\\
&{}+ 5100 a x^{2} - 42016 a x + 3120 a\\
&{}- 8112 x^{5} + 41561 x^{4} - 59488 x^{3}\\
&{}+ 71732 x^{2} - 6984 x
\end{aligned}
\]
\[
\begin{aligned}
13V={}&23 a^{4} + 13 a^{3} x - 10 a^{3}\\
&{}+ 23 a^{2} x^{2} + 46 a^{2} x + 13 a x^{3}\\
&{}+ 16 a x^{2} - 20 a x
\end{aligned}
\]

The source N has seventeen monomials and degree five; V has eight and degree four. Their interpretation is independently checked by the small-factor formula
\[
 N=(u-1)B^2K+a^2K+aBK-a^3B-aB(2Du-E)+M+uD^2-DE-3K^2/4.
\]
Let r=R1+log(2aB/K). Define the unexpanded curvature source
\[
\begin{aligned}
 P=1428050\{&N_{aa}V^2-NV_{aa}V-2N_aV_aV+2NV_a^2\\
 &-aB^3K^3-d^2a^3BK^3-2a^3B^3K^2+4a^5B^3K\}.
\end{aligned}\tag{2}
\]
Quotient differentiation, one fraction at a time, gives
\[
 r_{aa}=P/(1428050V^3).\tag{3}
\]
The source circuit (2) has degree eleven. We do not expand it. Differentiate its displayed products three times first; all expanded derivative identities below have degree at most eight.
We prove P_a<0, so the sign of r_aa changes at most once, from positive to negative, as a increases.

## 2. A third shape derivative controls the whole rectangle

Put A=a−1 and z=x−3/2, with 0≤A≤1/6 and 0≤z≤1/2. The coefficient identities obtained from (2) are
\[
 -P_{aaa}/12=p_0(x)+4p_1(x)A+30p_2(x)A^2+40p_3(x)A^3
                 +35p_4(x)A^4+1932p_5(x)A^5+4830p_6(x)A^6.
 \tag{4}
\]
Here are all seven complete univariate coefficient polynomials:
\[
\begin{aligned}
p_0={}&12987000 x^{8} + 62977317 x^{7} + 34809662 x^{6}\\
&{}+ 121451300 x^{5} + 804614864 x^{4} + 1240478045 x^{3}\\
&{}- 972038842 x^{2} + 42321282 x - 49320580
\end{aligned}
\]
\[
\begin{aligned}
p_1={}&24214320 x^{7} + 57537415 x^{6} - 37760307 x^{5}\\
&{}- 416286636 x^{4} + 704903748 x^{3} - 1495319181 x^{2}\\
&{}- 467256285 x - 32133850
\end{aligned}
\]
\[
\begin{aligned}
p_2={}&7758816 x^{6} + 12352366 x^{5} - 199205248 x^{4}\\
&{}- 77950069 x^{3} - 394998062 x^{2} - 288034157 x\\
&{}+ 975210
\end{aligned}
\]
\[
\begin{aligned}
p_3={}&12314952 x^{5} - 80027447 x^{4} - 188417877 x^{3}\\
&{}- 227732436 x^{2} - 341910135 x + 9293990
\end{aligned}
\]
\[
\begin{aligned}
p_4={}&2066688 x^{4} - 102448453 x^{3} - 42144342 x^{2}\\
&{}+ 11129020 - 241154142 x
\end{aligned}
\]
\[
\begin{aligned}
p_5={}&- 71760 x^{3} + 428511 x^{2} - 424559 x\\
&{}+ 66010
\end{aligned}
\]
\[
\begin{aligned}
p_6={}&139489 x + 270
\end{aligned}
\]

Each coefficient identity in (4) has degree at most eight. Their combined expression in A,x has at most 41 monomials; coefficients are checked separately before any common numerical denominator is introduced.
The first polynomial increases for x≥3/2: its derivative's negative linear contribution is absorbed by the positive x² term, and every other derivative term is positive. Direct scalar evaluation gives
\[
 p_0(x)\ge p_0(3/2)>8800000000.
\]
The last polynomial is positive. For the remaining five, the following individual shifts make every adverse term explicit:
\[
\begin{aligned}
64p_1(3/2+z)={}&1549716480 z^{7} + 19954417600 z^{6} + 103948995072 z^{5}\\
&{}+ 262573783536 z^{4} + 354036951168 z^{3} + 192841122036 z^{2}\\
&{}- 141985839600 z - 194785167067
\end{aligned}
\]
\[
\begin{aligned}
16p_2(3/2+z)={}&124141056 z^{6} + 1314907360 z^{5} + 2484760592 z^{4}\\
&{}- 7544531872 z^{3} - 38863468448 z^{2} - 64356509414 z\\
&{}-38547218769
\end{aligned}
\]
\[
\begin{aligned}
16p_3(3/2+z)={}&197039232 z^{5} + 197355088 z^{4} - 6263938224 z^{3}\\
&{}- 27845660592 z^{2} - 49049222796 z - 31416028993
\end{aligned}
\]
\[
\begin{aligned}
8p_4(3/2+z)={}&16533504 z^{4} - 720386600 z^{3} - 3802096740 z^{2}\\
&{}- 8249711502 z - 6245823067
\end{aligned}
\]
\[
\begin{aligned}
4p_5(3/2+z)={}&- 287040 z^{3} + 422364 z^{2} + 1506376 z\\
&{}+ 604525
\end{aligned}
\]

Discard positive terms in these five shifts, bound z≤1/2 only in the negative terms, and use A≤1/6. The resulting elementary lower bounds, with the scalar multipliers in (4) included, are
\[
\begin{aligned}
4Ap_1&>-2770000000,&30A^2p_2&>-4240000000,\\
40A^3p_3&>-740000000,&35A^4p_4&>-39000000,\\
1932A^5p_5&>-3000.
\end{aligned}
\]
Their total loss is less than 7789003000, whereas p0>8800000000. Hence
\[
 \boxed{P_{aaa}<0.}\tag{5}
\]
The largest coefficient in these five shift identities is 354036951168, twelve digits.

## 3. Two mixed third derivatives supply the starting jets

Write \(J_2(x)=P_{aa}(x,1)\), \(J_1(x)=P_a(x,1)\).
Differentiate (2) before substituting a=1. With z=x−3/2, the complete identities are
\[
\begin{aligned}
\frac8{39}J_2\prime={}&- 62719488 z^{8} - 922861056 z^{7} - 5777184448 z^{6}\\
&{}- 20352161856 z^{5} - 46400627280 z^{4} - 77590421696 z^{3}\\
&{}- 99909801012 z^{2} - 85025510676 z - 32758562637
\end{aligned}
\]
\[
\begin{aligned}
\frac{16}{39}J_1\prime\prime={}&- 268669440 z^{8} - 3862934400 z^{7} - 22961871296 z^{6}\\
&{}- 73081680672 z^{5} - 134935446160 z^{4} - 149869910920 z^{3}\\
&{}- 110669538084 z^{2} - 67876571678 z - 28075188629
\end{aligned}
\]

Both right sides are strictly negative for z≥0. The source jets at x=3/2, evaluated separately in the products (2), satisfy
\[
 J_2(3/2)<-50000000000,\quad
 J_1(3/2)<-10000000000,\quad J_1'(3/2)<-28000000000.
\]
These are rational inequalities, obtained directly by substituting a=1 and x=3/2 into the printed products after differentiation; no decimal estimate or large common numerator is needed.
It follows that J2<0 and J1<0 for x≥3/2. Together with (5), first integrate in a to obtain Paa<0, then integrate once more to obtain
\[
 \boxed{P_a<0}\tag{6}
\]
on the entire rectangle.

## 4. The derivative at the upper shape is positive

At a=7/6, direct first differentiation of N/V and of the logarithm gives
\[
 r_a=\frac{H(z)}{1281290400V^2},\qquad z=x-3/2,
\]
where the full degree-eight polynomial is
\[
\begin{aligned}
H={}&615019392 z^{8} + 7525117080 z^{7} + 36750125412 z^{6}\\
&{}+ 88441331004 z^{5} + 104149881378 z^{4} + 51729964866 z^{3}\\
&{}+ 9548287488 z^{2} + 7502774245 z + 2143618365
\end{aligned}
\]

Every coefficient is positive, so r_a(7/6)>0.
The largest coefficient here is 104149881378, twelve digits.

Fix x. By (3) and (6), r_aa is positive and then negative, with either part possibly empty. Therefore r_a first increases and then decreases. On its decreasing part it is at least its strictly positive final value. On its increasing part it can cross zero only from negative to positive. Consequently r can have only an interior minimum, and its maximum on [1,7/6] lies at an endpoint. Since Gamma is independent of a and F1=Gamma−cr−g, this is exactly (1).

All differentiated sources used to establish (6) are third derivatives of (2); no degree-eleven numerator is expanded. The proof uses elementary differentiation and integration, the explicitly printed polynomials, and one rectangle bound on each adverse monomial. It uses no original coefficient table.
