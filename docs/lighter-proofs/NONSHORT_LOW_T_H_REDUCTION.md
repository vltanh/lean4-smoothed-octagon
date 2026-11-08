# Low-t unit residual: monotonicity in h

## Statement and dependencies

Use \(G_n\), \(S=96q(q+1)(1+x)^3(17x+76)G_n\), and
\(\mathcal H=\partial_x-\tfrac12\partial_t\) from
`NONSHORT_LOW_T_CURVATURE.md`. This note proves
\[
 \boxed{\mathcal HS>0}
 \tag{H1}
\]
on the original unit-shape low-t domain
\[
 1/4\le h\le1/3,\quad 1/30\le j\le5h/7,\quad
 0\le y\le\frac{h-j}{1+2j},\quad
 t=(1-h)/2,\quad x=h+j,\quad q=1+y.
 \tag{H2}
\]
It uses two previously proved inputs:

* `NONSHORT_LOW_T_CURVATURE.md`: \(\mathcal H^2S>0\), \(\mathcal H^3S>0\),
  and \(\mathcal H^4S>500000\) on the rectangles specified there.
* `NONSHORT_LOW_T_INITIAL_DERIVATIVE.md`: the lower jet
  \(P_0(u,y)=\mathcal HS(3/8,u,1+y)\) is positive for
  \(17/60\le u\le3/7\), \(0\le y\le b(u)\), where
  \(b(u)=3931/8640-8u/9\). This includes the original initial face and
  \(u=3/7,\ y\le2/31\).

Every displayed polynomial is univariate of degree at most 8.
The source identities are checked coefficient by coefficient in y after differentiation,
never by expanding a polynomial in u and y of high total degree.

## 1. A cubic Taylor lower bound

Put
\[
 u=j+1/4,\quad r=h-1/4,\quad
 A=(2u+1/2)y+u-1/2,\quad B=(7u-3)/5.
\]
The domain gives
\[
 17/60\le u\le41/84,\quad 0\le r\le1/12,\quad
 0\le y\le9/32,\qquad r\ge\max(0,A,B).
 \tag{H3}
\]
Let \(P_i(u,y)=\mathcal H^{i+1}S(3/8,u,1+y)\) for \(i=0,1,2\), and set
\[
 T(u,y,r)=P_0+rP_1+\frac{r^2}{2}P_2+\frac{250000}{3}r^3.
 \tag{H4}
\]
The complete coefficients of \(P_0\) are printed in the initial-derivative note;
those of \(P_1\) are the \(E_i\) in the curvature note, and those of \(P_2\)
are its printed \(R_i(3/8,u)\). The source circuit (C3) there supplies the identities.
By the quantitative fourth-derivative bound and Taylor's theorem,
\(\mathcal HS\ge T(u,y,r)\). Since \(P_1,P_2>0\),
\[
 T_r=P_1+rP_2+250000r^2>0\quad(r\ge0).
 \tag{H5}
\]
It remains to prove \(T>0\) at the three possible lower values \(r=0,A,B\).

## 2. The q-limited Taylor polynomial: its u derivative

Write \(T_A(u,y)=T(u,y,A)\) and
\[
 f(u,y)=\partial_uT_A(u,y)=\sum_{i=0}^8 f_i(u)y^i.
 \tag{H6}
\]
Differentiate (H4) before expansion. Its \(P_2A^2\) term has coefficient degree
at most 9 in u, so the differentiation reduces every identity in (H6) to degree
at most 8. Each identity has at most nine monomials.
The complete coefficients are:

\[
\begin{aligned}
f_0(u)={}&\frac{1}{384}\bigl[13160448 u^{7} + 174706560 u^{6} + 337591872 u^{5} + 369000 u^{4}\\
&{}+48212424 u^{3} + 101004660 u^{2} - 110032610 u + 15657747\bigr]
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
f_1(u)={}&\frac{1}{768}\bigl[29611008 u^{8} + 584896512 u^{7} + 4144137984 u^{6} + 7999401024 u^{5}\\
&{}+1455106440 u^{4} - 193898232 u^{3} + 2011502844 u^{2} - 460165234 u\\
&{}-100281901\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_2(u)={}&\frac{1}{384}\bigl[45474048 u^{8} + 1681809408 u^{7} + 8871880416 u^{6} + 14837678784 u^{5}\\
&{}+5905808640 u^{4} - 792504120 u^{3} + 2107690002 u^{2} + 818427832 u\\
&{}-69445731\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_3(u)={}&\frac{1}{768}\bigl[- 160745472 u^{8} + 3427688448 u^{7} + 10108215936 u^{6} + 8666640576 u^{5}\\
&{}+22657543320 u^{4} + 8521943448 u^{3} - 1202782488 u^{2} + 2389155252 u\\
&{}+713876065\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_4(u)={}&\frac{1}{384}\bigl[- 472718592 u^{8} - 6732985344 u^{7} - 49445462304 u^{6} - 106020120384 u^{5}\\
&{}- 46987782360 u^{4} + 3046474056 u^{3} - 4836152862 u^{2} - 2550915442 u\\
&{}+34618473\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_5(u)={}&\frac{1}{256}\bigl[- 451215360 u^{8} - 10795785216 u^{7} - 73307389568 u^{6} - 160599613152 u^{5}\\
&{}- 112327496160 u^{4} - 26343399360 u^{3} - 7780909020 u^{2} - 3629182584 u\\
&{}-400733545\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_6(u)={}&\frac{1}{128}\bigl[- 133954560 u^{8} - 3628365824 u^{7} - 25234996864 u^{6} - 58127118144 u^{5}\\
&{}- 47220910400 u^{4} - 14335713536 u^{3} - 2513101812 u^{2} - 847763326 u\\
&{}-128275663\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_7(u)={}&\frac{1}{256}\bigl[- 56401920 u^{8} - 1133228032 u^{7} - 8771535360 u^{6} - 21671708544 u^{5}\\
&{}- 17412454720 u^{4} - 3468933720 u^{3} + 842411208 u^{2} + 195531454 u\\
&{}-10383035\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
f_8(u)={}&\frac{3}{32}\bigl[626688 u^{7} + 2489088 u^{6} + 4612608 u^{5} + 7816400 u^{4}\\
&{}+7820504 u^{3} + 4571526 u^{2} + 1296747 u + 134064\bigr]
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
### 2.1 The derivative of f increases its value in u

We prove \(f_u>0\) for \(u\ge17/60\) and \(1/19\le y\le2/7\).
This step uses finite Taylor transport in u, **not an expanded shift identity**.
Let \(g=f_u\), \(z=u-1/4\). The u-degree of g is at most 7, so
\[
 g(u,y)=\sum_{k=0}^7 z^k\frac{\partial_u^k g(1/4,y)}{k!}.
 \tag{H7}
\]
The eight divided-derivative jets are
\[
 \frac{p_0}{6144},\quad\frac{p_1}{512},\quad\frac{3p_2}{32},\quad
 \frac{5p_3}{8},\quad\frac{15p_4}{8},\quad\frac{21p_5}{2},\quad
 28p_6,\quad22032p_7.
 \tag{H8}
\]
Each jet identity is checked after differentiation and evaluation at u=1/4.
Only y is free: degree at most 8, at most nine monomials, with the positive
scalar factor in (H8) kept outside. The vanishing eighth u derivative is immediate
from the u-degree. Thus no high total-degree polynomial in (z,y), and no large
common numerator for such a shift, is expanded.
Here are the complete jet polynomials:

\[
\begin{aligned}
p_0(y)={}&3250440000 y^{8} - 38366445984 y^{7} - 433583531232 y^{6} - 553545835497 y^{5}\\
&{}- 155306828053 y^{4} + 40288019124 y^{3} + 38999517259 y^{2} + 6253670554 y\\
&{}-685242152
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_1(y)={}&1367757216 y^{8} - 48850987200 y^{7} - 332872233780 y^{6} - 397099185726 y^{5}\\
&{}- 106068972927 y^{4} + 20934520342 y^{3} + 17602707453 y^{2} + 5222224596 y\\
&{}+534820500
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_2(y)={}&58149912 y^{8} - 4665666135 y^{7} - 26568850144 y^{6} - 32931859385 y^{5}\\
&{}- 10550163971 y^{4} + 1675616380 y^{3} + 1449311511 y^{2} + 318227610 y\\
&{}+26330952
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_3(y)={}&9755040 y^{8} - 1334014032 y^{7} - 7277925420 y^{6} - 9695750364 y^{5}\\
&{}- 3827990235 y^{4} + 373315498 y^{3} + 561707814 y^{2} + 130562076 y\\
&{}+9889056
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_4(y)={}&2292192 y^{8} - 378809636 y^{7} - 2101230288 y^{6} - 2970051865 y^{5}\\
&{}- 1315548513 y^{4} + 97872060 y^{3} + 211060167 y^{2} + 52115258 y\\
&{}+4284200
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_5(y)={}&192096 y^{8} - 24226312 y^{7} - 142049364 y^{6} - 207566162 y^{5}\\
&{}- 92344411 y^{4} + 11774826 y^{3} + 17700337 y^{2} + 3883576 y\\
&{}+294252
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_6(y)={}&14688 y^{8} - 1216828 y^{7} - 7609912 y^{6} - 11424039 y^{5}\\
&{}- 4998973 y^{4} + 1011132 y^{3} + 1154139 y^{2} + 209674 y\\
&{}+8568
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
p_7(y)={}&- 80 y^{7} - 380 y^{6} - 640 y^{5} - 447 y^{4}\\
&{}- 76 y^{3} + 43 y^{2} + 14 y
\end{aligned}
\]
This polynomial has 7 monomials and total degree 7.
On \(0\le y\le2/7\), absorb every negative term of degree greater than 2
in a quadratic term by \(y^n\le(2/7)^{n-2}y^2\), and discard the unused positive terms.
This gives the following explicit lower polynomials:
\[
\begin{aligned}
 p_7&\ge14y-33y^2,\\
 p_6&\ge8568+209674y+400000y^2,\\
 p_5&\ge294252+3883576y+4300000y^2,\\
 p_4&\ge4284200+52115258y+19000000y^2,\\
 p_3&\ge9889056+130562076y-28000000y^2,\\
 p_2&\ge26330952+318227610y-367000000y^2,\\
 p_1&\ge534820500+5222224596y-2630000000y^2.
\end{aligned}
 \tag{H9}
\]
Each lower polynomial has two or three monomials and degree 2.
The last three negative quadratic terms are absorbed in their positive linear terms
using \(y\le2/7\); likewise \(14-33y>0\). Hence \(p_1,\dots,p_6>0\) and \(p_7\ge0\).

Retain the positive cubic terms in the separate comparisons for \(p_0\) and
\(p_1\), and absorb their negative high powers before combining the bounds.
Keep the scalar multipliers 5 and 2 outside throughout; do not expand
\(5p_0+2p_1\) as a degree-8 polynomial. The resulting cubic comparison is
\[
 5p_0+2p_1\ge
 243000000000y^3+46900000000y^2+41700000000y-2357000000=:M(y).
 \tag{H10}
\]
This polynomial has four monomials and degree 3. It is strictly increasing for y≥0,
and \(M(1/19)>3000000\). Since \(z\ge1/30\), (H7)–(H10) give
\[
 g\ge p_0/6144+zp_1/512
 \ge(5p_0+2p_1)/30720>0.
 \tag{H11}
\]
Thus f is strictly increasing in u on this rectangle.

### 2.2 Four small terminal intervals for f

We will use f only where \(A\ge0\) and \(y\ge1/19\).
The relation \(A\ge0\) gives \(y\ge(1-2u)/(1+4u)\).
Consequently the following four pieces cover that domain:
\[
\begin{array}{c|c}
\text{u interval}&\text{lower y bound}\\\hline
[17/60,1/3]&1/7\\
[1/3,3/8]&1/10\\
[3/8,2/5]&1/13\\
[2/5,41/84]&1/19.
\end{array}
 \tag{H12}
\]
These are the only subdivision pieces used in this note.
By (H11), each piece reduces to its left endpoint in u.
Round each coefficient of that univariate endpoint polynomial down to the integer
printed below. The comparisons are scalar evaluations of the explicit f_i in (H6);
no polynomial with a large common denominator is expanded.

For \(u=\frac{17}{60}\), \(f(u,y)\ge Q_a(y)\), where
\[
\begin{aligned}
Q_a(y)={}&103736 y^{8} - 479495 y^{7} - 10315146 y^{6} - 14490222 y^{5}\\
&{}- 3984562 y^{4} + 2155792 y^{3} + 998979 y^{2} - 61691 y\\
&{}-14589
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
On \([\frac{1}{7},2/7]\), the exact scalar checks are
\[
 Q_a(\frac{1}{7})>660,\quad Q_a(2/7)>39792,\quad
 Q_a^\prime(\frac{1}{7})>275366,\quad Q_a^{\prime\prime}(\frac{1}{7})>1895023.
\]
\[
\begin{aligned}
Q_a^{(4)}(y)={}&24\bigl[7261520 y^{4} - 16782325 y^{3} - 154727190 y^{2} - 72451110 y\\
&{}-3984562\bigr]
\end{aligned}
\]
This polynomial has 5 monomials and total degree 4.
For \(u=\frac{1}{3}\), \(f(u,y)\ge Q_b(y)\), where
\[
\begin{aligned}
Q_b(y)={}&139039 y^{8} - 1159357 y^{7} - 16246291 y^{6} - 21890293 y^{5}\\
&{}- 6061393 y^{4} + 2634170 y^{3} + 1445616 y^{2} + 25376 y\\
&{}-16594
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
On \([\frac{1}{10},2/7]\), the exact scalar checks are
\[
 Q_b(\frac{1}{10})>2192,\quad Q_b(2/7)>79021,\quad
 Q_b^\prime(\frac{1}{10})>357350,\quad Q_b^{\prime\prime}(\frac{1}{10})>3257342.
\]
\[
\begin{aligned}
Q_b^{(4)}(y)={}&24\bigl[9732730 y^{4} - 40577495 y^{3} - 243694365 y^{2} - 109451465 y\\
&{}-6061393\bigr]
\end{aligned}
\]
This polynomial has 5 monomials and total degree 4.
For \(u=\frac{3}{8}\), \(f(u,y)\ge Q_c(y)\), where
\[
\begin{aligned}
Q_c(y)={}&175497 y^{8} - 2078805 y^{7} - 23394209 y^{6} - 30752565 y^{5}\\
&{}- 8597755 y^{4} + 3169297 y^{3} + 1940970 y^{2} + 130262 y\\
&{}-15229
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
On \([\frac{1}{13},2/7]\), the exact scalar checks are
\[
 Q_c(\frac{1}{13})>7330,\quad Q_c(2/7)>125466,\quad
 Q_c^\prime(\frac{1}{13})>463714,\quad Q_c^{\prime\prime}(\frac{1}{13})>4429444.
\]
\[
\begin{aligned}
Q_c^{(4)}(y)={}&120\bigl[2456958 y^{4} - 14551635 y^{3} - 70182627 y^{2} - 30752565 y\\
&{}-1719551\bigr]
\end{aligned}
\]
This polynomial has 5 monomials and total degree 4.
For \(u=\frac{2}{5}\), \(f(u,y)\ge Q_d(y)\), where
\[
\begin{aligned}
Q_d(y)={}&200931 y^{8} - 2831623 y^{7} - 28909649 y^{6} - 37584782 y^{5}\\
&{}- 10591044 y^{4} + 3565352 y^{3} + 2309079 y^{2} + 211197 y\\
&{}-12775
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
On \([\frac{1}{19},2/7]\), the exact scalar checks are
\[
 Q_d(\frac{1}{19})>5159,\quad Q_d(2/7)>160924,\quad
 Q_d^\prime(\frac{1}{19})>476197,\quad Q_d^{\prime\prime}(\frac{1}{19})>5275706.
\]
\[
\begin{aligned}
Q_d^{(4)}(y)={}&24\bigl[14065170 y^{4} - 99106805 y^{3} - 433644735 y^{2} - 187923910 y\\
&{}-10591044\bigr]
\end{aligned}
\]
This polynomial has 5 monomials and total degree 4.
Each fourth derivative is negative on \([0,2/7]\): its positive leading term
is absorbed in the next negative term using \(y<1\), and all remaining terms are negative.
Thus each \(Q_i''\) is concave, starts positive at the listed lower endpoint,
and can cross to negative at most once. Each \(Q_i'\) therefore first increases
and then decreases; its listed initial value is positive. Hence \(Q_i\) first
increases and then decreases, if it changes monotonicity at all, and its minimum
is at an endpoint. The endpoint checks prove
\[
 f(u,y)>0\quad\text{if }A\ge0,\quad y\in[1/19,9/32].
 \tag{H13}
\]

### 2.3 The terminal u=17/60 Taylor polynomial

Coefficientwise downward rounding gives \(T_A(17/60,y)\ge Q_*(y)\), where
\[
\begin{aligned}
Q_*(y)={}&14168 y^{8} - 24363 y^{7} - 1147729 y^{6} - 1712338 y^{5}\\
&{}- 304743 y^{4} + 460447 y^{3} - 19522 y^{2} - 17846 y\\
&{}+1832
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
Q_*^{\prime\prime\prime}(y)={}&6\bigl[793408 y^{5} - 852705 y^{4} - 22954580 y^{3} - 17123380 y^{2}\\
&{}- 1218972 y + 460447\bigr]
\end{aligned}
\]
This polynomial has 6 monomials and total degree 5.
On \([13/64,9/32]\), this third derivative is negative.
Indeed \(y<1\) absorbs its positive leading term in the negative \(y^4\) term,
and \(y>1/5\) makes
\(-17123380y^2-1218972y+460447<0\); the remaining cubic term is negative.
Thus \(Q_*''\) decreases, and \(Q_*'\) first increases and then decreases.
The exact checks
\[
 Q_*'(13/64)>4000,\qquad Q_*(13/64)>68,\qquad Q_*(9/32)>21
 \tag{H14}
\]
therefore imply \(Q_*>0\) throughout that interval.

## 3. The outer-gap Taylor polynomial

Write \(T_B(u,y)=T(u,y,B)\), and
\[
 \partial_uT_B=\sum_{i=0}^6 U_i(u)y^i.
 \tag{H15}
\]
As for (H6), differentiate before expansion; the seven source identities are
univariate in u of degree at most 8. Their complete polynomials are:

\[
\begin{aligned}
U_0(u)={}&\frac{1}{800}\bigl[53738496 u^{7} + 704428704 u^{6} + 1427265840 u^{5} + 301735630 u^{4}\\
&{}+357052454 u^{3} + 577910678 u^{2} - 488273562 u + 61451961\bigr]
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
U_1(u)={}&\frac{1}{1600}\bigl[120911616 u^{8} + 1937245184 u^{7} + 11070177216 u^{6} + 19133806512 u^{5}\\
&{}+34318170 u^{4} - 4972020098 u^{3} + 862624890 u^{2} - 50582202 u\\
&{}-110194151\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
U_2(u)={}&\frac{1}{2400}\bigl[- 168412608 u^{8} + 7552731648 u^{7} + 27000216600 u^{6} + 10157769648 u^{5}\\
&{}- 27642793785 u^{4} - 33995288448 u^{3} - 2890522413 u^{2} + 4254345822 u\\
&{}+163933196\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
U_3(u)={}&\frac{1}{2400}\bigl[- 1036385280 u^{8} - 18960480768 u^{7} - 127222937520 u^{6} - 230098098024 u^{5}\\
&{}- 17996752845 u^{4} + 78860767947 u^{3} + 14169413046 u^{2} + 2511917859 u\\
&{}+72725168\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
U_4(u)={}&\frac{1}{800}\bigl[- 323870400 u^{8} - 9677290752 u^{7} - 58857082200 u^{6} - 92441315664 u^{5}\\
&{}+9962087240 u^{4} + 49749186608 u^{3} + 5784375060 u^{2} - 2274300396 u\\
&{}-69676949\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
U_5(u)={}&\frac{1}{1600}\bigl[- 172730880 u^{8} - 3329682176 u^{7} - 24361148896 u^{6} - 41125435416 u^{5}\\
&{}+14039031370 u^{4} + 29933126546 u^{3} - 653220204 u^{2} - 3417016578 u\\
&{}-53679249\bigr]
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
U_6(u)={}&\frac{1}{400}\bigl[14779392 u^{7} + 44674784 u^{6} + 51218688 u^{5} + 90577470 u^{4}\\
&{}+35599414 u^{3} - 10268763 u^{2} - 16543968 u - 2226165\bigr]
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
For \(3/7\le u\le41/84\), put \(v=1/2-u\), so \(0\le v\le1/14\).
The following bounds suffice:
\[
 U_0>20000,\quad U_1>-20000,\quad U_2>-1600000,\quad
 U_3,U_4,U_5>0,\quad U_6>-20000.
 \tag{H16}
\]
Here are small explicit lower polynomials for them. Apply finite Taylor expansion
to each printed univariate U_i at u=1/2, evaluating its scalar divided-derivative jets
before rounding down. It gives
\[
 U_0-20000\ge J_0(v),\quad U_1+20000\ge J_1(v),\quad
 U_2+1600000\ge J_2(v),\quad U_i\ge J_i(v)\ (i=3,4,5),\quad
 U_6+20000\ge J_6(v).
 \tag{H17}
\]
This comparison uses scalar jets, not an expanded shift identity with a large numerator.
The complete lower polynomials are:

\[
\begin{aligned}
J_0(v)={}&- 67174 v^{7} + 1115641 v^{6} - 4778349 v^{5} + 8433267 v^{4}\\
&{}- 8009142 v^{3} + 5057303 v^{2} - 1365342 v + 81639
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
\[
\begin{aligned}
J_1(v)={}&75569 v^{8} - 1513058 v^{7} + 11685572 v^{6} - 39600786 v^{5}\\
&{}+61491521 v^{4} - 46909935 v^{3} + 18172398 v^{2} - 3359127 v\\
&{}+174577
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
J_2(v)={}&- 70172 v^{8} - 2866284 v^{7} + 21773287 v^{6} - 54013072 v^{5}\\
&{}+54712015 v^{4} - 8267071 v^{3} - 21856222 v^{2} + 12042350 v\\
&{}+95435
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
J_3(v)={}&- 431828 v^{8} + 9627509 v^{7} - 83683049 v^{6} + 299401721 v^{5}\\
&{}- 482422627 v^{4} + 372385438 v^{3} - 130968719 v^{2} + 12945834 v\\
&{}+1780514
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
J_4(v)={}&- 404838 v^{8} + 13715965 v^{7} - 118743366 v^{6} + 402606789 v^{5}\\
&{}- 607012926 v^{4} + 412885600 v^{3} - 102339111 v^{2} - 6000874 v\\
&{}+3994054
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
J_5(v)={}&- 107957 v^{8} + 2512878 v^{7} - 23265096 v^{6} + 83061768 v^{5}\\
&{}- 122157452 v^{4} + 70807018 v^{3} - 7000643 v^{2} - 4752957 v\\
&{}+625679
\end{aligned}
\]
This polynomial has 9 monomials and total degree 8.
\[
\begin{aligned}
J_6(v)={}&- 36949 v^{7} + 241006 v^{6} - 657088 v^{5} + 1127036 v^{4}\\
&{}- 1222045 v^{3} + 736503 v^{2} - 177937 v + 18649
\end{aligned}
\]
This polynomial has 8 monomials and total degree 7.
Using \(v\le1/14\) to absorb the negative terms of degree at least 3 into the quadratic terms gives
\[
\begin{aligned}
 J_0&\ge81639-1365342v+4480000v^2,\\
 J_1&\ge174577-3359127v+14800000v^2.
\end{aligned}
 \tag{H18}
\]
Each lower polynomial has three monomials and degree 2. Both are decreasing on
\([0,1/14]\); their values at \(1/14\) exceed 6900 and 10000 respectively.
For J_2, absorb all negative terms in its positive linear term by
\(v^n\le v/14^{n-1}\). Their total coefficient is less than 1700000,
so \(J_2\ge95435+(12042350-1700000)v>0\).
For each of \(J_3,J_4,J_5,J_6\), discard its positive nonconstant terms and bound
its negative powers at \(v=1/14\). The resulting scalar lower bounds exceed,
respectively, 1000000, 3000000, 200000, and 5000.
These explicit comparisons prove (H16).

On \(0\le y\le2/31<1/15\), use \(y^6\le y^2\) to obtain
\[
 \partial_uT_B
 >20000-20000y-1620000y^2
 \ge20000-20000/15-1620000/225
 =34400/3>11000.
 \tag{H19}
\]
Thus T_B strictly increases in u on its needed rectangle.

## 4. Close all three lower faces for the first derivative

Because of (H5), it is enough to evaluate T at
\(r_0=\max(0,A,B)\).

If \(r_0=0\), then \(B\le0\) gives \(u\le3/7\), and \(A\le0\) gives
\(y\le(1-2u)/(1+4u)\). The initial-derivative theorem gives \(T=P_0>0\).

If \(r_0=B\ge0\), then \(u\ge3/7\). The inequality \(A\le B\) gives
\[
 y\le\frac{4u-1}{5(4u+1)}\le2/31.
\]
By (H19), \(T_B(u,y)\ge T_B(3/7,y)=P_0(3/7,y)>0\), using
\(b(3/7)>2/31\) from the enlarged initial theorem.

Finally suppose \(r_0=A\ge\max(0,B)\).
If \(u\le3/7\), the condition \(A\ge0\) gives \(y\ge1/19\).
If \(u\ge3/7\), the condition \(A\ge B\) gives the same bound.
Put \(u_0=(1-y)/(2+4y)\). The condition \(A\ge0\) is precisely \(u\ge u_0\).
Decrease u at fixed y to \(\max(17/60,u_0)\); (H13) applies throughout this segment.
When \(y\le13/64\), the terminal point is \(u_0\in[17/60,3/7]\), where A=0
and \(T_A=P_0>0\). When \(y\ge13/64\), the terminal point is u=17/60,
and (H14) gives \(T_A>0\). Thus this last case also closes.

We have proved \(T(u,y,r_0)>0\), hence \(\mathcal HS\ge T(u,y,r)>0\).
This proves (H1) on the unchanged domain (H2).

## 5. Consequence for the unit-sign reduction

Fix j,y and lower h while remaining in (H2). The stopping value is
\[
 h_0=\max\bigl(1/4,\ 7j/5,\ j+(1+2j)y\bigr).
\]
By (H1), S strictly increases in h, so the unit sign reduces exactly to the three faces
\(h=1/4\), \(j=5h/7\), and \(y=(h-j)/(1+2j)\).
The first two signs are proved in [the initial unit face](NONSHORT_LOW_T_UNIT_FACE.md)
and [the outer-gap face](NONSHORT_LOW_T_OUTER_FACE.md). The third is proved in
[the maximum-duration face](NONSHORT_LOW_T_QMAX.md). Together with this
monotonicity theorem they establish the full unit sign, since the positive
normalization of S preserves the sign of G_n. The
[caller argument](NONSHORT_LOW_T_CALLER.md) gives the complete substitution
and shape reduction and names the actual Lean integration point.

