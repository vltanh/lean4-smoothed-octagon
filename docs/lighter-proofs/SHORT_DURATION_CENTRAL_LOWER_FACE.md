# Central duration tests at the lower beta face

This closes the `beta=x` face, for all three rational tests in
[central duration faces](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES.md)
and [central duration two](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN.md).
The upper beta face is a separate obligation: this lemma alone does not
close either source theorem. It uses their exact rational incoming norm.

## 1. Domain and source quantities

Let
\[
12/5\le x\le9,\qquad 1\le a\le(5x+4)/12,\qquad b=x,
\]
and set
\[
S=x+1,\quad M=35x+13,\quad K=x^2+2x+a^2,
\quad u=3/4+2(x-1)^2/(SM),
\]
\[
D=a^2+2ax+1+2x-2x^2,\quad E=S^3(u-1)+3S-1,
\]
\[
w=\{S^2(S^2-S+1)+D^2u-DE\}/K^2,
\quad E_L=(2Du-E)/K,\quad q=a^2/K,\quad T=K/[a(a+x)].
\]
The exact three expressions are
\[
G_1=(w-1)T+T^{-1}+(u-1)(a+x)/a+a/(a+x)
+1-q-E_L+(w-3/4)/2,
\]
\[
G_8=(w-1)8T/9+9/(8T)+(u-1)(a+x)/a+a/(a+x)
+1-q-E_L-1/9+(w-3/4)/2,
\]
\[
G_2=5w/2+(u-1)(a+x)/a+a/(a+x)-q-E_L
+5q(a+x)/(2a)-151/72.
\]
We prove all three are strictly negative. Define
\[
\Delta=8a(a+x)SMK^2>0,\qquad
N_1=-\Delta G_1,\quad N_8=-9\Delta G_8,\quad N_2=-9\Delta G_2.
\]
The proof differentiates in `a` before expanding. The three source
expressions `N_i` are never expanded as polynomials of degree nine.
Instead their first derivatives have degree eight, and their values at
`a=1` have a positive factor times a polynomial of degree at most eight.

## 2. Increase the numerator in a

For `1<=a<=4/3`, put `A=a-1` and `H=x-2`. Thus
`0<=A<=1/3` and `H>=2/5`. The following are exact polynomial identities
for `partial_a N_i`, with the derivative taken before substitution.

\[
\begin{aligned}
\partial_a N_1={}&\bigl(- 48 A^{5} - 30520 A^{4} - 155204 A^{3} - 153354 A^{2} + 35860 A + 72374\bigr)\\
&+H\bigl(- 96 A^{5} - 38980 A^{4} - 232460 A^{3} - 184269 A^{2} + 182836 A + 230121\bigr)\\
&+H^{2}\bigl(- 48 A^{5} - 16520 A^{4} - 129032 A^{3} - 54801 A^{2} + 249208 A + 301250\bigr)\\
&+H^{3}\bigl(- 2300 A^{4} - 31944 A^{3} + 6762 A^{2} + 151680 A + 214729\bigr)\\
&+H^{4}\bigl(- 3316 A^{3} + 1584 A^{2} + 48708 A + 92298\bigr)\\
&+H^{5}\bigl(- 108 A^{3} - 1821 A^{2} + 10100 A + 24739\bigr)\\
&+H^{6}\bigl(- 405 A^{2} + 1840 A + 3966\bigr)\\
&+H^{7}\bigl(216 A + 299\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\partial_a N_8={}&\bigl(- 4818 A^{5} - 261110 A^{4} - 1372976 A^{3} - 1311654 A^{2} + 301610 A + 439160\bigr)\\
&+H\bigl(- 4056 A^{5} - 321430 A^{4} - 2048356 A^{3} - 1519461 A^{2} + 1588472 A + 1444311\bigr)\\
&+H^{2}\bigl(- 966 A^{5} - 132010 A^{4} - 1140980 A^{3} - 389289 A^{2} + 2178802 A + 1926988\bigr)\\
&+H^{3}\bigl(- 17930 A^{4} - 284824 A^{3} + 105480 A^{2} + 1336476 A + 1406177\bigr)\\
&+H^{4}\bigl(- 29260 A^{3} + 28992 A^{2} + 435262 A + 633688\bigr)\\
&+H^{5}\bigl(- 756 A^{3} - 13035 A^{2} + 91072 A + 186317\bigr)\\
&+H^{6}\bigl(- 3321 A^{2} + 16166 A + 35064\bigr)\\
&+H^{7}\bigl(1836 A + 3579\bigr)\\
&+H^{8}\bigl(108\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\partial_a N_2={}&\bigl(- 58068 A^{5} - 1428060 A^{4} - 7065492 A^{3} - 7350570 A^{2} + 1247184 A + 446706\bigr)\\
&+H\bigl(- 45456 A^{5} - 1670380 A^{4} - 10069364 A^{3} - 8769477 A^{2} + 8386800 A + 1320093\bigr)\\
&+H^{2}\bigl(- 9276 A^{5} - 653940 A^{4} - 5345992 A^{3} - 2875473 A^{2} + 12037348 A + 1035594\bigr)\\
&+H^{3}\bigl(- 85220 A^{4} - 1266472 A^{3} + 128370 A^{2} + 7431932 A + 257253\bigr)\\
&+H^{4}\bigl(- 122276 A^{3} + 117984 A^{2} + 2255032 A + 162074\bigr)\\
&+H^{5}\bigl(- 2916 A^{3} - 31821 A^{2} + 327496 A + 246751\bigr)\\
&+H^{6}\bigl(- 9477 A^{2} + 20884 A + 139462\bigr)\\
&+H^{7}\bigl(972 A + 33311\bigr)\\
&+H^{8}\bigl(2916\bigr)
\end{aligned}
\]

Here is a direct bound for those identities. For each coefficient of
`H^j`, replace each negative term `-c A^k`, `k>=2`, by the lower term
`-c A/3^{k-1}`, and discard its positive terms of degree at least two.
This leaves a linear polynomial in `A`. In all three identities every
coefficient of `H^j`, `j>=1`, is bounded below by its printed constant
term. The three constant coefficients, after this operation, have the
respective lower bounds
\[
4954180/81,\qquad9176300/27,\qquad-2104652/9.
\]
The first two are positive. For the third retain its linear `H` term:
\[
\partial_aN_2\ge-2104652/9+1320093H
\ge13238414/45>0.
\]
This proves all three derivative signs on the first shape interval.

For `a>=4/3`, use `A=a-4/3` and `H=x-2a+1/3`. The source domain gives
\[
0\le A\le11/4,\qquad
H\ge(12a-4)/5-2a+1/3=(6a-7)/15>0.
\]
The next identities are for the same partial derivatives, again taken
before the indicated substitution; they are not derivatives along the
slanted boundary.

\[
\begin{aligned}
729\partial_a N_1={}&\bigl(- 1259712 A^{8} + 13156992 A^{7} + 191861136 A^{6} + 848769840 A^{5} + 1928026368 A^{4} + 2532521376 A^{3} + 1951022160 A^{2} + 821778736 A + 146581344\bigr)\\
&+H\bigl(7558272 A^{7} + 149905728 A^{6} + 952120656 A^{5} + 2891491992 A^{4} + 4798596384 A^{3} + 4477054032 A^{2} + 2209659408 A + 449452696\bigr)\\
&+H^{2}\bigl(28658448 A^{6} + 313615800 A^{5} + 1388293020 A^{4} + 3091572360 A^{3} + 3658457664 A^{2} + 2196636624 A + 526099140\bigr)\\
&+H^{3}\bigl(37791360 A^{5} + 291433788 A^{4} + 932560128 A^{3} + 1466982252 A^{2} + 1112571288 A + 323770824\bigr)\\
&+H^{4}\bigl(25587900 A^{4} + 143929386 A^{3} + 323178822 A^{2} + 324144018 A + 118917558\bigr)\\
&+H^{5}\bigl(9605304 A^{3} + 38865177 A^{2} + 56347326 A + 27580743\bigr)\\
&+H^{6}\bigl(1909251 A^{2} + 5298372 A + 3936600\bigr)\\
&+H^{7}\bigl(157464 A + 270459\bigr)
\end{aligned}
\]

\[
\begin{aligned}
2187\partial_a N_8={}&\bigl(56687040 A^{8} + 986197032 A^{7} + 6574145328 A^{6} + 22689751752 A^{5} + 45568033272 A^{4} + 55510515216 A^{3} + 40524135192 A^{2} + 16334226336 A + 2797667168\bigr)\\
&+H\bigl(513962496 A^{7} + 5855911200 A^{6} + 28580722020 A^{5} + 75105811116 A^{4} + 113957301384 A^{3} + 99900479412 A^{2} + 46960964028 A + 9149109720\bigr)\\
&+H^{2}\bigl(1246170096 A^{6} + 10740055194 A^{5} + 39932769798 A^{4} + 78956680716 A^{3} + 85945071546 A^{2} + 48431296278 A + 10993673268\bigr)\\
&+H^{3}\bigl(1443629952 A^{5} + 9505992330 A^{4} + 26300028024 A^{3} + 36881834814 A^{2} + 25587825156 A + 6920700696\bigr)\\
&+H^{4}\bigl(936517140 A^{4} + 4622071410 A^{3} + 9024244344 A^{2} + 8006687190 A + 2650443930\bigr)\\
&+H^{5}\bigl(354294000 A^{3} + 1256726745 A^{2} + 1567427274 A + 667840545\bigr)\\
&+H^{6}\bigl(75405573 A^{2} + 177020154 A + 109784484\bigr)\\
&+H^{7}\bigl(7794468 A + 9795573\bigr)\\
&+H^{8}\bigl(236196\bigr)
\end{aligned}
\]

\[
\begin{aligned}
2187\partial_a N_2={}&\bigl(374134464 A^{8} + 4170241584 A^{7} + 19554835968 A^{6} + 50888993904 A^{5} + 81042633216 A^{4} + 81462800304 A^{3} + 50818523040 A^{2} + 18105891504 A + 2837805728\bigr)\\
&+H\bigl(2993075712 A^{7} + 27033244560 A^{6} + 103961634408 A^{5} + 220314058488 A^{4} + 277630554672 A^{3} + 207912312432 A^{2} + 85603397832 A + 14926525416\bigr)\\
&+H^{2}\bigl(7372149552 A^{6} + 52490650644 A^{5} + 155132946684 A^{4} + 242517701376 A^{3} + 210428328600 A^{2} + 95435867628 A + 17492942844\bigr)\\
&+H^{3}\bigl(9047251584 A^{5} + 49499796924 A^{4} + 106213865328 A^{3} + 110386623420 A^{2} + 54397851048 A + 9721096632\bigr)\\
&+H^{4}\bigl(6430436100 A^{4} + 26115128838 A^{3} + 37757588346 A^{2} + 22094705502 A + 3931915122\bigr)\\
&+H^{5}\bigl(2780499312 A^{3} + 7931901267 A^{2} + 6849242226 A + 1591136541\bigr)\\
&+H^{6}\bigl(723291201 A^{2} + 1304737956 A + 509404788\bigr)\\
&+H^{7}\bigl(104162436 A + 90565857\bigr)\\
&+H^{8}\bigl(6377292\bigr)
\end{aligned}
\]

Every coefficient in the last two identities is positive. The first
has just one negative monomial. Its neighboring term absorbs it:
\[
13156992A^7-1259712A^8
\ge(13156992-1259712\cdot11/4)A^7=9692784A^7\ge0.
\]
The constant terms are strictly positive. Thus `partial_a N_i>0`
throughout the original shape domain. For every fixed `x`, the interval
from `1` to the original `a` stays in that domain, so `N_i(x,a)>=N_i(x,1)`.

## 3. Three scalar lower endpoints

Direct substitution in the source gives
\[
N_1(x,1)=(x-1)^2(x+1)P_1(x),\qquad
N_8(x,1)=(x+1)P_8(x),\qquad N_2(x,1)=(x+1)P_2(x).
\]
Writing `H=x-2>=2/5`, the complete endpoint polynomials are

\[
P_1(2+H)=108 H^{6} + 1242 H^{5} + 5527 H^{4} + 11786 H^{3} + 11624 H^{2} + 3324 H - 1163.
\]

\[
P_8(2+H)=864 H^{8} + 11826 H^{7} + 66807 H^{6} + 201279 H^{5} + 346164 H^{4} + 330992 H^{3} + 145743 H^{2} - 353 H - 16602.
\]

\[
P_2(2+H)=3402 H^{7} + 33491 H^{6} + 129806 H^{5} + 246171 H^{4} + 225702 H^{3} + 75537 H^{2} - 9342 H - 8703.
\]

For the first, the positive linear term alone absorbs its negative
constant: `3324H-1163>=833/5>0`.
For the second, its quadratic lower part
`145743H^2-353H-16602` increases for `H>=2/5` and equals
`164392/25>0` at `2/5`.
For the third, `75537H^2-9342H-8703` increases for `H>=2/5`, but its
value there is negative. Retain the positive cubic term as well:
\[
225702H^3+75537H^2-9342H-8703
\ge1761381/125>0.
\]
The retained cubic increases on this interval since its derivative is
at least `2(75537)(2/5)-9342>0`. All omitted terms are positive.
Consequently `N_i>0` and `G_i<0` for all three tests on the stated face.

## 4. Audit and size boundary

The derivative identities have respectively 36, 37, 37 monomials in
Section 2's first coordinates and 44, 45, 45 monomials in its second
coordinates. Each has total degree eight in two variables. The largest
coefficient is 277630554672 (twelve digits). The endpoint identities have
at most nine monomials and degree at most eight. The single split is at
`a=4/3`; it serves only to choose nonnegative coordinates. Every polynomial
used for a sign is printed above. Coefficient extraction is not a proof
premise: the displayed identities and the explicit linear absorption
rule give all signs.

For a contribution-by-contribution check of the source differentiation,
keep the positive scalar `151` outside the contribution
`151 a(a+x)SMK^2` to `N_2`. Differentiate its remaining product before
using the second coordinates. Clearing that product's denominator gives
36 monomials, degree seven and largest coefficient 9194966424; multiplying
that already checked identity by `151` requires no further expansion.
All other individual differentiated source contributions have at most
45 monomials, degree eight and coefficients of at most twelve digits.

Exact rational symbolic arithmetic checked the source differentiation,
source endpoints and monomial counts. The proof does not depend on that
computation. No Lean compilation, Lake, typechecking or CI was run.
