# Central S1: the first test decreases along the original shape curve

Use the source notation of [the central reduction](SHORT_CENTRAL_REDUCTION.md).
This note proves
\[
 \boxed{\frac d{da}F_0\bigl(x,a,b_+(x,a),u_\ell(x,b_+(x,a))\bigr)
 <-4553/2589600<0}\tag{1}
\]
on the unchanged actual central strip
\[
 8/5\le x\le2,\qquad1\le a,\qquad6a^2\le X=x(x+2),
 \qquad b_+=x+(10/13)(a-1).
\]
We use its containing bound a≤7/6. The derivative estimate below is only needed where the cap inequality holds.

## 1. A fixed-norm derivative, followed by one cap division

Put \(C=10/13\), \(d=23/13\), \(e=x-10/13\), so \(B=da+e\), and write
\[
 D=\frac{33a^2+6ax-20a-26x^2+46x+13}{13},\quad
 D_a=\frac{66a+6x-20}{13},\quad W=M+uD^2-DE.
\]
All the source polynomials have been printed: D has six monomials and degree two, E degree three, and M degree four. W is retained as its three products before differentiation.
For \(r_0=R_0+\log(2aB/K)\), direct quotient differentiation gives
\[
\begin{aligned}
 (r_0)_a={}&-\frac{(u-1)e}{a^2}+\frac e{B^2}
 -\frac{(2a+2uD_a)K-2a(a^2+2Du-E)}{K^2}\\
 &+\frac{2\{D_a(2uD-E)K-4aW\}}{K^3}
 +\frac1a+\frac dB-\frac{2a}K.
\end{aligned}\tag{2}
\]
It is affine in u. We prove \((r_0)_a>1/25\) at u=3/4 and u=19/25, so the same inequality holds throughout their interval.

For these two values, respectively, define the unexpanded source numerators
\[
 P_f=16900a^2(23a+13x-10)^2K^3\{(r_0)_a|_{u=3/4}-1/25\},
\]
\[
 P_v=4225a^2(23a+13x-10)^2K^3\{(r_0)_a|_{u=19/25}-1/25\}.
\]
Perform division in a by the actual cap polynomial before making a two-variable expansion:
\[
 \boxed{P_j=(X-6a^2)Q_j+x^2(x+2)\{R_j+(a-1)U_j\}.}\tag{3}
\]
The symbols Rj here denote remainders, not the original rational cost tests. They are specified completely below.

Identity (3) is checked coefficient by coefficient in a, using the rational source (2); it is not an expanded degree-ten certificate. To make the verification explicit, let qi be the coefficient of ai in Qj after A=a−1 is substituted. For every i≥2, the coefficient identity is
\([a^i]P_j=Xq_i-6q_{i-2}\), with missing qi zero. Each is a polynomial identity in x of degree at most eight. For the last two coefficients divide out X first:
\[
 [a^0]P_j/X=q_0+x(R_j-U_j),\qquad
 [a^1]P_j/X=q_1+xU_j.
\]
The two remaining identities have degrees at most eight. These elementary division recurrences provide a direct check of (3) from the printed source and factors without expanding any higher-degree identity.

Here are all quotient polynomials. Set A=a−1, and define
\(Q_j=\sum_{i=0}^8q_{j,i}(x)A^i\).

### The floor norm quotient

\[
\begin{aligned}
3888q_{f,0}={}&- 7457516638 x^{8} + 8799561421 x^{7} + 101156425548 x^{6}\\
&{}+ 53415298594 x^{5} + 19368474584 x^{4} + 38533999668 x^{3}\\
&{}- 19479407112 x^{2} - 21841255800 x - 3342744288
\end{aligned}
\]
\[
\begin{aligned}
324q_{f,1}={}&- 1600429259 x^{7} + 3612954076 x^{6} + 35853688416 x^{5}\\
&{}+ 12544802543 x^{4} - 28723264510 x^{3} - 27045926358 x^{2}\\
&{}- 17685926388 x - 3671408052
\end{aligned}
\]
\[
\begin{aligned}
648q_{f,2}={}&- 7104449950 x^{6} + 35253810801 x^{5} + 43912231206 x^{4}\\
&{}- 165876143924 x^{3} - 194769515364 x^{2} - 119419628796 x\\
&{}-32492555784
\end{aligned}
\]
\[
\begin{aligned}
54q_{f,3}={}&- 410782151 x^{5} + 1689808540 x^{4} - 14543496845 x^{3}\\
&{}- 24270479133 x^{2} - 15556269570 x - 5686238484
\end{aligned}
\]
\[
\begin{aligned}
108q_{f,4}={}&511446962 x^{4} - 10170093283 x^{3} - 30604983064 x^{2}\\
&{}- 22773420870 x - 12373304760
\end{aligned}
\]
\[
\begin{aligned}
9q_{f,5}={}&29256253 x^{3} - 596939894 x^{2} - 476447420 x\\
&{}-557997429
\end{aligned}
\]
\[
\begin{aligned}
18q_{f,6}={}&3739970 x^{2} + 90342229 x - 228533874
\end{aligned}
\]
\[
\begin{aligned}
q_{f,7}/\frac{15548}{3}={}&13 x + 82
\end{aligned}
\]
\[
\begin{aligned}
q_{f,8}/\frac{178802}{3}={}&1
\end{aligned}
\]

### The upper norm quotient

\[
\begin{aligned}
7776q_{v,0}={}&- 3576030263 x^{8} + 5893198736 x^{7} + 54350893002 x^{6}\\
&{}+ 28554152972 x^{5} + 7542647668 x^{4} + 16222704960 x^{3}\\
&{}- 11188228392 x^{2} - 11295286704 x - 1716929136
\end{aligned}
\]
\[
\begin{aligned}
648q_{v,1}={}&- 767512759 x^{7} + 2130287234 x^{6} + 18698433078 x^{5}\\
&{}+ 6225201034 x^{4} - 15346257764 x^{3} - 14173353600 x^{2}\\
&{}- 9030834072 x - 1863675216
\end{aligned}
\]
\[
\begin{aligned}
1296q_{v,2}={}&- 3408038855 x^{6} + 18644000982 x^{5} + 22486180500 x^{4}\\
&{}- 85740718504 x^{3} - 100004290068 x^{2} - 60644096136 x\\
&{}-16428832992
\end{aligned}
\]
\[
\begin{aligned}
108q_{v,3}={}&- 196918735 x^{5} + 867268373 x^{4} - 7451933344 x^{3}\\
&{}- 12373161564 x^{2} - 7880348124 x - 2871768312
\end{aligned}
\]
\[
\begin{aligned}
216q_{v,4}={}&246078937 x^{4} - 5216142260 x^{3} - 15582183710 x^{2}\\
&{}- 11527890276 x - 6251650920
\end{aligned}
\]
\[
\begin{aligned}
18q_{v,5}={}&14081405 x^{3} - 304654486 x^{2} - 241297522 x\\
&{}-282397068
\end{aligned}
\]
\[
\begin{aligned}
36q_{v,6}={}&1869985 x^{2} + 45809882 x - 116052312
\end{aligned}
\]
\[
\begin{aligned}
q_{v,7}/\frac{3887}{3}={}&13 x + 82
\end{aligned}
\]
\[
\begin{aligned}
q_{v,8}/\frac{89401}{6}={}&1
\end{aligned}
\]

## 2. Quotient signs use elementary bounds on powers

Every coefficient identity above has degree at most eight and at most nine terms. The largest coefficient is 194769515364.
On the slightly larger x interval [3/2,2], the displayed q0 terms give
\[
 q_{f,0}>170000000,\qquad q_{v,0}>49000000.
\]
For verification, pair each negative x8 term with the positive x6 term, using x²≤4; evaluate the remaining positive x6 at x=3/2, discard other positive terms, and bound the three negative low powers by x≤2.
Both q1 terms are positive: pair their adverse x7 term with the positive x5 term, then divide by x3. The four remaining adverse terms are bounded using x≥3/2. The resulting lower constants before their positive scalar denominators exceed 10000000000 and 5000000000, respectively.

For i≥2 discard positive terms and use x≤2, A≤1/6. The complete rounded lower bounds needed are
\[
\begin{aligned}
 A^2q_{f,2}&>-122000000,&A^3q_{f,3}&>-23000000,&A^4q_{f,4}&>-1900000,\\
 A^5q_{f,5}&>-56000,&A^6q_{f,6}&>-300,
\end{aligned}
\]
\[
\begin{aligned}
 A^2q_{v,2}&>-31000000,&A^3q_{v,3}&>-5800000,&A^4q_{v,4}&>-480000,\\
 A^5q_{v,5}&>-15000,&A^6q_{v,6}&>-100.
\end{aligned}
\]
The last two coefficient terms are positive. Adding these inequalities gives
\[
 Q_f>23043700>0,\qquad Q_v>11704900>0.\tag{4}
\]
These bounds are direct consequences of the displayed polynomials; no coefficient table or numerical probe is a premise.

## 3. The two remainder signs are univariate

Put t=2−x. It is enough to use 0≤t≤1/2. The four complete remainder polynomials are:
\[
\begin{aligned}
3888R_f={}&- 7457516638 t^{7} + 98381800711 t^{6} - 435992893692 t^{5}\\
&{}+ 804306942456 t^{4} - 575758236036 t^{3} + 277385873448 t^{2}\\
&{}+ 698060219264 - 727676770880 t
\end{aligned}
\]
\[
\begin{aligned}
324U_f={}&1600429259 t^{6} - 10231725682 t^{5} + 17378572783 t^{4}\\
&{}+ 9807846689 t^{3} - 50779391666 t^{2} + 26698617872 t\\
&{}+ 18550932128
\end{aligned}
\]
\[
\begin{aligned}
7776R_v={}&- 3576030263 t^{7} + 45503766962 t^{6} - 183382013496 t^{5}\\
&{}+ 237217598472 t^{4} + 149933776080 t^{3} - 517187084160 t^{2}\\
&{}+ 154119362048 t + 182112670720
\end{aligned}
\]
\[
\begin{aligned}
648U_v={}&767512759 t^{6} - 4527444275 t^{5} + 4819917128 t^{4}\\
&{}+ 17469882076 t^{3} - 47133051616 t^{2} + 32524703104 t\\
&{}+ 2565409024
\end{aligned}
\]

Both U numerators are positive. Bound their negative t² terms by half their t coefficient and their negative t5 terms by t/16. The remaining t coefficient is positive in each case, and their constants are positive. For the R numerators, discard the positive nonconstant terms and set t=1/2 in the negative terms. This leaves respectively more than 240000000000 and 40000000000. Thus
\[
 R_f,R_v,U_f,U_v>0.\tag{5}
\]
The largest displayed remainder coefficient is 804306942456; their degrees are six and seven.
Because X−6a²≥0 and A≥0, (3)--(5) prove both endpoint signs and hence
\[
 \boxed{(r_0)_a>1/25\qquad(3/4\le u\le19/25).}\tag{6}
\]

## 4. Restore the norm dependence and reach the true cap

Along b=b+, the only norm motion is
\(du_\ell/da=(10/13)(u_\ell)_b<0\).
The reduction note gives \(-1/5<(F_0)_u<0\) and \(|(u_\ell)_b|\le5/664\).
Consequently
\[
 \frac d{da}F_0(x,a,b_+,u_\ell)
 <-\frac7{2400}+\frac{10}{8632}
 =-\frac{4553}{2589600}<0,
\]
which is (1).

Increase a to the exact cap \(a_c=\sqrt{X/6}\), following b+ and u_l throughout.
At this cap K=7a_c², so the central transport quantities are exactly the outer q=1/7 quantities. No rational approximation to the cap is used.
The proof after the constant-beta step in Section 1 of
[the completed outer first-test sign](SHORT_OUTER_LOW_SHAPE_TERMINAL.md)
already proves positivity at b=b+ on this cap. Its shape comparison works for every fixed C∈[1/2,4/5], expressly including C=10/13, and follows the same u_l curve.

The needed floor condition there also holds: \(u_\ell\ge u_f=3/4+(x-1)^2/(28S^2)\).
After positive factors are cleared, this follows from
\[
 7S(b+15x-16)-2Z(b-1)
 =105x^2+63x-86-(63x+19)b>0.
\]
Use b≤ax≤7x/6 and x≥3/2; the resulting increasing quadratic is
\(63x^2/2+245x/6-86>0\).
Thus the exact cap endpoint has the already certified outer margin 167/144000000.
Combining norm reduction, beta reduction, and (1) proves the central first-test sign on its original actual domain.
