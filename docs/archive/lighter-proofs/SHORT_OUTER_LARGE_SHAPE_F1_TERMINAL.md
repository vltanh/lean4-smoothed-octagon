# The four terminal F1 curves at a=x in the S1 outer A branch

This supplies the last terminal face in
[the large-shape reduction](SHORT_OUTER_LARGE_SHAPE_REDUCTION.md).
Use the original \(F_1\) and the same cubic logarithm majorant.
For
\[
 3/2\le x\le2,\qquad a=x,\qquad
 C\in\{24/43,10/13\},\qquad \beta=x+C(x-1),
\]
and either
\[
 u_-(x)=(8x+1303)/1750,\qquad u_+(x)=(6x+443)/600,
\tag{T1}
\]
we prove
\[
 \boxed{F_1(x,x,x+C(x-1),u_\pm(x))>1/15000.}
\tag{T2}
\]
The proof makes each of the four curves strictly concave in x and checks
its two scalar endpoints. It never clears the denominator of the full
curve, which would produce a degree-fourteen numerator.

## 1. A Laurent source with small separate identities

Write \(c=7/96\), \(g=9193/50000\), \(S=x+1\),
\(A=2+C\), \(H_C=Ax-C\), \(Z=H_C/x\), and \(Y=2Z/7\).
At \(a=x\), the original transport polynomial D equals \(S^2\), so w
and \(E_L\) are independent of beta. Before substituting a norm, the
complete Laurent source is
\[
\begin{aligned}
 \Gamma_*={}&-\frac{(u-1)^2x^2}{16}-\frac{(u-1)^2x}{8}
       -\frac{u^2}{12}+\frac u4+\frac1{12}\\
 &-\frac{12u^2+6u-13}{288x}
  -\frac{13u^2-14u+2}{576x^2}
  -\frac{u(u-1)}{288x^3}-\frac{(u-1)^2}{576x^4}\\
 &-\frac7{288S}-\frac{49}{576S^2},\\
 49w={}&54-17u+6(1-u)x-\frac{5(3u-1)}x
                         -\frac{3u-5}{x^2}+\frac{u-1}{x^3},\\
 7E_L={}&6-4u+6(1-u)x+\frac{3u}x-\frac7S+\frac{u-1}{x^2}.
\end{aligned}
\tag{T3}
\]
Check the three coefficients of u in the first identity separately,
and the two coefficients in each of the other identities separately.
Each is univariate in x; the largest degree is eight and the largest
collected count is nine. Substituting either affine norm into the
individual Laurent summands now involves only polynomials of degree at
most four. In particular it does not form the degree-ten numerator of
\(\Gamma_*\) with the substituted norm.

The residual itself is
\[
 F=\Gamma_*+cE_L+c(1-u)Z-1/16-g-cJ-c\ell(Y),
 \qquad J=\frac{7w-17/4}{Z}.
\tag{T4}
\]
After the affine norm substitution, the two small source polynomials are
\[
 (7w_--17/4)x^3
 =-\frac{96x^5-5092x^4-40333x^3+21638x^2-9698x+894}{24500},
\]
\[
 (7w_+-17/4)x^3
 =-\frac{36x^5-840x^4-6929x^3+3663x^2-1677x+157}{4200}.
\tag{T5}
\]
Each identity has six monomials and degree five. Divide each by the
linear factor \(H_C\) before differentiating. The four complete divisions
are as follows; the linear denominators retain their normalized form.

For \(C=24/43\),
\[
\begin{aligned}
 J_-={}&-516x^2/336875+61189x/756250+5390231503/8152375000\\
       &-481643/(1176000x)+6407/(98000x^2)
           +\frac{52197632273}{97828500000H_C},\\
 J_+={}&-129x^2/38500+82001x/1058750+924905963/1397550000\\
       &-494027/(1209600x)+6751/(100800x^2)
           +\frac{54541690673}{100623600000H_C}.
\end{aligned}
\tag{T6}
\]
For \(C=10/13\),
\[
\begin{aligned}
 J_-={}&-26x^2/18375+49387x/661500+14650753/23814000\\
       &-210587/(612500x)+5811/(122500x^2)
           +\frac{161388629}{297675000H_C},\\
 J_+={}&-13x^2/4200+1079x/15120+209417/340200\\
       &-24089/(70000x)+2041/(42000x^2)
           +\frac{4714697}{8505000H_C}.
\end{aligned}
\tag{T7}
\]
After multiplying by \(24500x^2H_C\) or \(4200x^2H_C\), these are
six-monomial degree-five identities. Even before collecting the terms,
the largest cleared coefficient is \(170354772720\), twelve digits.
The polynomial and reciprocal pieces can therefore be differentiated
separately within the requested budget.

## 2. The complete second-derivative data

For a fixed choice of C and norm, differentiating (T3)--(T7) gives
\[
 F''=-Q/d_Q-\frac{P}{d_Px^6S^4}-\frac{K}{H_C^3}
                                  -c\frac{d^2}{dx^2}\ell(Y(x)).
\tag{T8}
\]
All numerator polynomials and constants in this identity are printed
below. Each Q has three monomials and degree two; each P has eight
monomials and degree seven. The source check for P combines the
second derivatives of the four powers \(1/x,\ldots,1/x^4\) and the
two powers \(1/S,1/S^2\) only. It has 23 summands before collection;
the largest cleared coefficient is \(179382734898\).

### C=24/43, norm \(u_-\)

\[ Q=12672 x^{2} - 695376 x + 6405881,\qquad d_Q=808500000. \]
\[ P=29098877517 x^{7} + 103961937432 x^{6} - 143042103618 x^{5} - 70437895492 x^{4} - 2902510243 x^{3} + 4137672420 x^{2} + 330293664 x + 687342960. \]
\[ d_P=303408000000,\qquad K=\frac{52197632273}{102508560000}. \]

### C=24/43, norm \(u_+\)

\[ Q=2376 x^{2} - 59796 x + 254339,\qquad d_Q=31680000. \]
\[ P=855290791 x^{7} + 3062892754 x^{6} - 4176005670 x^{5} - 2032336260 x^{4} - 62610945 x^{3} + 128083326 x^{2} + 12043784 x + 21198140. \]
\[ d_P=8916480000,\qquad K=\frac{1268411411}{2452032000}. \]

### C=10/13, norm \(u_-\)

\[ Q=3456 x^{2} - 189648 x + 1750813,\qquad d_Q=220500000. \]
\[ P=1299759374 x^{7} + 4639166249 x^{6} - 4565097396 x^{5} - 2401514424 x^{4} - 269586846 x^{3} + 66367665 x^{2} + 12482028 x + 25975170. \]
\[ d_P=11466000000,\qquad K=\frac{161388629}{266175000}. \]

### C=10/13, norm \(u_+\)

\[ Q=24 x^{2} - 604 x + 2581,\qquad d_Q=320000. \]
\[ P=152782716 x^{7} + 546135999 x^{6} - 533640072 x^{5} - 278261588 x^{4} - 29320712 x^{3} + 8523723 x^{2} + 1820572 x + 3204370. \]
\[ d_P=1347840000,\qquad K=\frac{362669}{585000}. \]

## 3. Elementary signs of the polynomial parts

For each Q, discard its positive quadratic term and use \(x\le2\)
on its negative linear term. This gives respectively
\[
 Q\ge5015129,\quad Q\ge134747,\quad
 Q\ge1371517,\quad Q\ge1373.
\]
Dividing by the corresponding positive \(d_Q\) in Section 2 shows
\[
 Q/d_Q>1/250
\tag{T9}
\]
in all four cases. No derivative sign is used for this estimate.

For P, the following complete quartic comparisons avoid a large shift
of its twelve-digit coefficients. In the same order as Section 2,
write \(P=\sigma x^3q+R\). Every coefficient of R is nonnegative.
Put \(z=2x-3\in[0,1]\); each displayed shift has positive coefficients.

\[
 \sigma=1000000000,\qquad q=29 x^{4} + 103 x^{3} - 144 x^{2} - 71 x - 3.
\]
\[ R=98877517 x^{7} + 961937432 x^{6} + 957896382 x^{5} + 562104508 x^{4} + 97489757 x^{3} + 4137672420 x^{2} + 330293664 x + 687342960. \]
\[ 16q((3+z)/2)=29 z^{4} + 554 z^{3} + 2844 z^{2} + 4670 z + 975. \]

\[
 \sigma=10000000,\qquad q=85 x^{4} + 306 x^{3} - 418 x^{2} - 204 x - 7.
\]
\[ R=5290791 x^{7} + 2892754 x^{6} + 3994330 x^{5} + 7663740 x^{4} + 7389055 x^{3} + 128083326 x^{2} + 12043784 x + 21198140. \]
\[ 16q((3+z)/2)=85 z^{4} + 1632 z^{3} + 8426 z^{2} + 14040 z + 3353. \]

\[
 \sigma=10000000,\qquad q=129 x^{4} + 463 x^{3} - 457 x^{2} - 241 x - 27.
\]
\[ R=9759374 x^{7} + 9166249 x^{6} + 4902604 x^{5} + 8485576 x^{4} + 413154 x^{3} + 66367665 x^{2} + 12482028 x + 25975170. \]
\[ 16q((3+z)/2)=129 z^{4} + 2474 z^{3} + 13472 z^{2} + 26038 z + 12783. \]

\[
 \sigma=1000000,\qquad q=152 x^{4} + 546 x^{3} - 534 x^{2} - 279 x - 30.
\]
\[ R=782716 x^{7} + 135999 x^{6} + 359928 x^{5} + 738412 x^{4} + 679288 x^{3} + 8523723 x^{2} + 1820572 x + 3204370. \]
\[ 16q((3+z)/2)=152 z^{4} + 2916 z^{3} + 15900 z^{2} + 30852 z + 15396. \]

Thus \(P>0\). The quartics and shifts each have five monomials and degree
four; the remainders each have eight monomials and degree seven. Every
identity uses only x (or only z), and every coefficient is at most twelve
digits. Combining with (T9) gives
\[
 -Q/d_Q-P/(d_Px^6S^4)<-1/250.
\tag{T10}
\]

## 4. Pairing the linear pole with the same logarithm bound

The derivative inequalities for the single cubic majorant, printed in
the large-shape reduction, are \(\ell'(Y)\le1/Y\) and
\(\ell''(Y)\ge-1/Y^2\). Here
\[
 Y=\frac27(A-C/x),\quad Y'=\frac{2C}{7x^2}>0,
 \quad Y''=-\frac{4C}{7x^3}<0.
\]
Therefore
\[
 -c\frac{d^2}{dx^2}\ell(Y(x))
 \le c\left[(Y'/Y)^2-Y''/Y\right]
 =\frac{cC(2Ax-C)}{x^2H_C^2}.
\tag{T11}
\]
The inequality direction on the \(Y''\) term uses \(Y''<0\); it does
not require concavity of a composition as an unstated rule.

For \(C=24/43\), both K values are greater than \(1/2\). The logarithm
term multiplied by \(H_C^3\) is at most
\[
 cC\left(2A^2-\frac{3AC}{x}+\frac{C^2}{x^2}\right)
 \le cC(2A^2-3AC/2+4C^2/9)
 =35868/79507<1/2.
\tag{T12}
\]
Thus the last two terms of (T8) together are negative.

For \(C=10/13\), both K values are greater than \(3/5\). The complete
cleared comparison needed for a \(1/500\) bound is
\[
 \frac{x^2H_C^3}{500}-cC(2Ax-C)H_C+\frac35x^2
 =\frac{V(x)}{3295500},
\]
\[
 V=139968x^5-116640x^4+32400x^3-860700x^2+1181250x-109375.
\tag{T13}
\]
This has six monomials and degree five. Its complete shift is
\[
 V((3+z)/2)=4374z^5+58320z^4+310230z^3
                 +608595z^2+393075z+307667>0.
\tag{T14}
\]
Consequently the last two terms in (T8) together are less than \(1/500\).
Together with (T10), this proves
\[
 \boxed{F''<-1/500<0}
\tag{T15}
\]
for all four curves. The left C endpoint even gives \(F''<-1/250\).

## 5. Eight scalar endpoint checks

All endpoint data below come from the factored source (T3)--(T5).
At \(x=3/2\), the respective norm, Casimir, transported norm, and pairing
are
\[
 (u_-,\Gamma_*,w,E_L)
 =\left(263/350,\ 4714079/25401600,\ 283/343,\ 803/1470\right),
\]
\[
 (u_+,\Gamma_*,w,E_L)
 =\left(113/150,\ 7810799/41990400,\ 467/567,\ 1027/1890\right).
\tag{T16}
\]
At \(x=2\), they are
\[
 (u_-,\Gamma_*,w,E_L)
 =\left(1319/1750,\ 365788579/2032128000,\ 583007/686000,\ 98201/147000\right),
\]
\[
 (u_+,\Gamma_*,w,E_L)
 =\left(91/120,\ 4817299/26542080,\ 13271/15680,\ 2213/3360\right).
\tag{T17}
\]
The two C values give, respectively,
\[
 (Z,\ell(2Z/7))_{x=3/2}
 =\left(94/43,-165009832/350790507\right),\quad
   \left(88/39,-119157128/271556547\right),
\]
\[
 (Z,\ell(2Z/7))_{x=2}
 =\left(98/43,-153480/357911\right),\quad
   \left(31/13,-4121944/10744731\right).
\tag{T18}
\]
These are evaluations of the one bound \(\ell\), not new logarithm
approximations. All fractions have at most ten-digit numerators and
denominators.

Here are explicit rounded scalar certificates, with denominators at most
10000. In each expression use the lower bounds for \(\Gamma_*\), \(E_L\),
and \((1-u)Z\), and upper bounds for \(J\) and \(\ell\). Equation (T4)
then gives the following strict inequalities.

At \(x=3/2,C=24/43\):
\[
 F_-\ge\frac{1855}{10000}
 +\frac7{96000}(546+543-698+470)-\frac1{16}-\frac{9193}{50000}
 =1537/800000,
\]
\[
 F_+\ge\frac{1860}{10000}
 +\frac7{96000}(543+539-694+470)-\frac1{16}-\frac{9193}{50000}
 =881/400000.
\]
At \(x=3/2,C=10/13\):
\[
 F_-\ge\frac{1855}{10000}
 +\frac7{96000}(546+560-677+438)-\frac1{16}-\frac{9193}{50000}
 =1887/800000,
\]
\[
 F_+\ge\frac{1860}{10000}
 +\frac7{96000}(543+556-672+438)-\frac1{16}-\frac{9193}{50000}
 =6511/2400000.
\]
At \(x=2,C=24/43\):
\[
 F_-\ge\frac{1800}{10000}
 +\frac7{96000}(668+561-746+428)-\frac1{16}-\frac{9193}{50000}
 =161/2400000,
\]
\[
 F_+\ge\frac{1814}{10000}
 +\frac7{96000}(658+550-735+428)-\frac1{16}-\frac{9193}{50000}
 =1771/2400000.
\]
At \(x=2,C=10/13\):
\[
 F_-\ge\frac{1800}{10000}
 +\frac7{96000}(668+587-713+383)-\frac1{16}-\frac{9193}{50000}
 =2611/2400000,
\]
\[
 F_+\ge\frac{1814}{10000}
 +\frac7{96000}(658+576-703+383)-\frac1{16}-\frac{9193}{50000}
 =2023/1200000.
\tag{T19}
\]
Every displayed lower bound is strictly greater than \(1/15000\).
All rounded comparisons can be checked against (T16)--(T18) after
reducing their small rational fractions; the largest resulting cross
product is below \(10^{12}\). Concavity (T15) now proves (T2) throughout
the full x interval.

## 6. Expansion boundary

The order of verification matters. In (T3), compare coefficients of u
before substituting an affine norm. Substitute into individual Laurent
summands, then use the degree-five divisions (T5)--(T7). Differentiate
those pieces before combining the proper fractions. This produces the
four degree-seven P identities (23 raw summands each) and the four
quadratic Q identities. Their largest cleared coefficient, before
collection, is \(179382734898\). The only other polynomial sign checks
are the four quartics, their shifts and positive remainders, and the
six-term quintic (T13)--(T14). Every identity is univariate and has total
degree at most eight. The numerator of the complete residual is never
expanded. This proof requires no coefficient table and no subdivision.
