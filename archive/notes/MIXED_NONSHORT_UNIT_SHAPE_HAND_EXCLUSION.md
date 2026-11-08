# A hand exclusion on the unit shape face

Date: 2026-11-07 UTC. Complete hand proof, accepted in the
[independent unit-shape audit](MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md).

This note gives an elementary, explicit sign proof on the lower face
\(k=1\). It does not use an interval cover, a numerical minimum, or a
runtime certificate. It applies both to the reverse-next reduction and
to the part of the common low-\(a\) problem where \(d\le c\).
The reverse scale face \(k=29t^2/4\) is now closed separately in the
[complete reverse hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md).

The normalized residual and its shape monotonicity are defined in
[MIXED_NONSHORT_SHAPE_MONOTONICITY.md](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
The [reverse order bound](MIXED_NONSHORT_REVERSE_ORDER_BOUND.md) supplies
the extra lower face \(k\ge2t+x\). The present argument keeps the actual
incoming missing-control floor throughout.

## 1. Scalar theorem and its applications

Let
\[
0<t\le\frac{13}{35},\qquad
0<x\le1-2t,\qquad
1<2t+2x+x^2,\qquad q>1.
\tag{1}
\]
Put
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad X=x+2,\quad
Y=x(x+2),\quad B=1+2tx+x^2,\quad Z=qB/W,
\]
and retain the exact incoming secant and its floor:
\[
v=1+\frac{c^2}{W}-\frac c x\log W,\qquad
v\ge F_{p/W}(q),\qquad
F_\eta(q)=1+\eta^2q-\eta\frac{q\log q}{q-1}.
\tag{2}
\]
Define
\[
H_0=\frac{v-1+t^2}{t}+t(2-t),\qquad
w_U=\frac{1-t+t^2+H_0Y+vY^2}{B^2},
\]
\[
R=c+Z-\frac{p^2}{W}-\frac{p^2}{Z}+\frac{p^3}{B}
-p\log q-Wv-Zw_U+\frac{p(H_0+2vY)}B,\qquad
N=tBqW R.
\tag{3}
\]

**Theorem.** Under (1)--(2), \(N>0\).

For the reverse-next problem, the possible smallest shape is
\[
k_{\min}=\max\{1,\,2t+x,\,29t^2/4\}.
\]
If \(k_{\min}=1\), then \(x\le1-2t\) and
\(t\le2/\sqrt{29}<13/35\); the last strict comparison is the integer
inequality \(4900<4901\). The actual centre gap
\(k<2t+2x+x^2\) implies the third inequality in (1).
The incoming floor is independent of \(k\), and the strict increase
of \(N\) in \(k\) moves actual negativity to \(k=1\). The theorem
therefore excludes the entire unit lower face, including its ties.

More generally, any common low-\(a\) argument that has \(k\ge1\),
\(t\le13/35\), \(d\le c\), the same centre gap and the actual incoming
floor may use exactly the same comparison. No reverse-next hypothesis
occurs in the scalar theorem.

## 2. Removing the logarithms with their correct signs

For positive \(x\), and \(q>1\),
\[
\log(1+x)>
\frac{2x}{x+2}+\frac{2x^3}{3(x+2)^3},
\qquad
\log q<L_+(q):=
\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\tag{4}
\]
The first follows by integrating
\(1/(1-z^2)>1+z^2\) from zero to \(x/(x+2)\).
For the second, \(L_+(1)=0\), and
\[
(L_+(q)-\log q)'=\frac{(q-1)^4}{6q^2(q+1)^2}>0.
\]

Set
\[
\bar v=1+\frac{c^2}{W}
-\frac{2c}{X}\left(1+\frac{x^2}{3X^2}\right),
\qquad
F_\ell=1+\frac{p^2}{W^2}q
-\frac pW\,\frac{q^2+10q+1}{6(q+1)}.
\]
Then \(v<\bar v\) and \(F_\ell<F_{p/W}(q)\le v\).
Let \(\bar N\) be (3) after replacing \(v\) by \(\bar v\) and
\(\log q\) by \(L_+(q)\). Both replacements decrease \(N\). Indeed
the coefficient of \(\log q\) in \(N\) is \(-tpqWB<0\), while
\[
N_v=-xq I,\quad
I=1+tx+tW(1-2t)+(q-1)[X+txX^2]>0.
\]
Consequently \(N>\bar N\).

Put \(y=q-1\) and define the polynomial
\[
P=6(q+1)W^2X^3
\{\bar N-y(\bar v-F_\ell)\}.
\tag{5}
\]
Since \(\bar v-F_\ell>0\), proving \(P>0\) proves \(N>0\).
The displayed denominator cancels exactly, and \(P\) is cubic in \(y\):
\[
P=C_0+C_1y+C_2y^2+C_3y^3.
\tag{6}
\]
Thus (3)--(6) give direct, unambiguous definitions of its four
polynomial coefficients; no numerical quantities enter them.

We prove the following six signs:
\[
\begin{aligned}
C_0&>0,\\
J_1:=20xC_1+3C_0&>0,\\
J_2:=53C_0+20x^2C_2&>0,\\
J_3:=24x^3C_3+12x^2C_2-C_0&>0,\\
J_4:=40x^3C_3+30x^2C_2+7C_0&>0,\\
J_*:=24x^3C_3-C_0&>0.
\end{aligned}
\tag{7}
\]
The proof of these explicit polynomial inequalities is given in
Sections 4--8. The appendices display all coefficients used to check
the elementary expansions and endpoint signs.

## 3. Why the six signs suffice

Define
\[
A=\frac{xC_1}{C_0},\qquad
B_1=-\frac{x^2C_2}{C_0},\qquad
G=\frac{x^3C_3}{C_0},\qquad z=\frac yx\ge0.
\]
(The symbol \(B_1\) here is a scalar coefficient ratio, not the
geometric \(B\) in Section 1.)
The signs (7) imply
\[
A\ge-\frac3{20},\quad B_1\le\frac{53}{20},\quad
G\ge\frac1{24},\quad
G\ge\frac{B_1}{2}+\frac1{24},\quad
G\ge\frac{3B_1}{4}-\frac7{40}.
\]
If \(B_1\le0\), then
\[
P/C_0\ge f_0(z):=1-\frac3{20}z+\frac1{24}z^3>0.
\]
For \(0\le z\le2\), the constant and linear terms are at least \(7/10\).
For \(z\ge2\), \(z^3/24\ge z/6>3z/20\).

If \(0\le B_1\le53/20\), use the larger of the last two affine
lower bounds on \(G\). They meet at \(B_1=13/15\). For fixed \(z\),
the resulting lower bound on \(P/C_0\) is affine in \(B_1\) on
each of the two intervals. Its minimum is therefore attained at
one of \(0,13/15,53/20\), giving \(f_0\) or
\[
f_1(z)=1-\frac3{20}z-\frac{13}{15}z^2+\frac{19}{40}z^3,
\qquad
f_2(z)=1-\frac3{20}z-\frac{53}{20}z^2+\frac{29}{16}z^3.
\]
Both have short positive-square comparisons:
\[
\begin{aligned}
f_1(z)
&=\frac{52}{135}+\frac{13}{180}(z-\tfrac43)
+\frac25(z-\tfrac43)^2+\frac{19}{40}z(z-\tfrac43)^2\\
&\ge\frac{52}{135}-\frac{169}{51840}>0,\\
f_2(z)
&=\frac1{80}-\frac1{80}(z-1)
+\frac{39}{40}(z-1)^2+\frac{29}{16}z(z-1)^2\\
&\ge\frac1{80}-\frac1{24960}>0.
\end{aligned}
\]
Thus (7) proves \(P>0\) for every \(y\ge0\).

## 4. The common shape coordinates and \(C_0\)

Put
\[
s=1-2t-x,\qquad \gamma=\frac9{35}.
\]
The assumptions imply
\[
0<x<1,\qquad
\max\{0,\gamma-x\}\le s\le\min\{1-x,x+x^2\},\qquad x>\frac3{25}.
\tag{8}
\]
For the last inequality, \(x\le3/25\) would give
\(2x+x^2\le159/625<9/35\), contradicting the centre gap.
Using weak bounds in (8) only enlarges the domain.

First, the rational secant bound still lies below the turn ceiling.
Direct subtraction gives
\[
U(t)-\bar v=\frac{(1-t)x}{3WX^3}
\{12-24t+(14-36t)x+(5-18t)x^2-3tx^3\}.
\]
The brace decreases in \(t\). Substituting \(t\le(1-x)/2\) bounds it
below by \(8x+14x^2+(15/2)x^3+(3/2)x^4>0\).
Thus \(\bar v<U(t)\).

At \(q=1\), the general normalized residual is affine in \(k\), and
direct collection gives
\[
\partial_k\bar N(1;k)
=x\{(1-\bar v)(1+tW)-t(1-t^2)\}
>t^2(1-t)x^2>0.
\]
This comparison does not move the incoming floor or any Casimir.
Since \(1-(2t+x)=s\ge0\), the exact order-face identity yields
\[
\bar N(1;1)\ge\bar N(1;2t+x)
=\frac{(1-t)x^3}{3WX^3}P_0(t,x),
\]
where
\[
\begin{aligned}
P_0={}&t(3t-1)x^3+(18t^2-15t+5)x^2\\
&+(36t^2-40t+14)x+(24t^2-32t+12).
\end{aligned}
\]
The exact square bounds
\[
t(3t-1)\ge-\frac1{12},\quad
18t^2-15t+5\ge\frac{15}{8},\quad
36t^2-40t+14\ge\frac{26}{9},\quad
24t^2-32t+12\ge\frac43
\]
and \(x<1\) give
\(P_0>(43/24)x^2+(26/9)x+4/3>0\).
As \(C_0=12W^2X^3\bar N(1;1)\), this proves \(C_0>0\).

For \(i=1,2,3,4\), write
\[
J_i/x^2=A_{i0}(x)+A_{i1}(x)s+
 A_{i2}(x)s^2+A_{i3}(x)s^3.
\tag{9}
\]
Appendix A gives each coefficient explicitly. Appendix C proves
\[
J_i(13/35,x)>0\qquad(3/25\le x\le\gamma)
\tag{10}
\]
by four univariate endpoint arguments.

## 5. The first two bounds are increasing in \(s\)

For \(J_1\), Appendix A gives
\[
A_{12}\ge-408,\qquad
A_{13}\ge-444-1218x-1143x^2-18x^3.
\]
Using \(s\le S:=x+x^2\), its derivative in \(s\) is bounded below by
\[
\begin{aligned}
A_{11}-816S
 -3(444+1218x+1143x^2+18x^3)S^2
={}&36+1022x+5177x^2+7164x^3\\
&+\tfrac{6861}{2}x^4+\tfrac{4543}{2}x^5
 +\tfrac{8807}{2}x^6+\tfrac{6729}{2}x^7
 +865x^8+90x^9>0.
\end{aligned}
\]
Therefore \(J_1/x^2\) is increasing in \(s\).
For \(x\le\gamma\), its minimum in (8) is the positive cap value (10).
For \(x\ge\gamma\), its minimum is \(A_{10}\).
After removing the factor \(xW^2\), every nonconstant coefficient of
\(A_{10}\) is positive. The remaining polynomial is strictly increasing,
and its value at \(\gamma\) is positive by (10). Hence \(J_1>0\).

For \(J_2\), the polynomials \(A_{21},A_{22}\) have positive coefficients.
In \(A_{23}/W\), the only negative monomial is \(-279x^3\), and
\(361x^2-279x^3>82x^2\). Thus all three derivative coefficients are
positive, and \(J_2/x^2\) increases in \(s\).
The cap range again follows from (10). At \(s=0\), write
\(A_{20}=xW^2 f(x)\). Its derivative has the lower bound
\[
f'(x)\ge720x-178>0\qquad(x\ge\gamma),
\]
all its omitted terms being positive as displayed in Appendix A.
The starting value \(f(\gamma)>0\) follows from (10).
This proves \(J_2>0\).

## 6. The third bound is concave in \(s\)

We show \(A_{32}+3A_{33}s<0\) throughout (8), so that (9) for \(i=3\)
is strictly concave in \(s\).

First, collecting the positive tail with \(x\le1\) gives
\[
A_{32}\le-24-1152x-2992x^2<0.
\]
For \(x\ge1/4\), the same elementary collection gives
\[
A_{32}+3A_{33}(1-x)
\le372-570x-3970x^2<0.
\]
The last quadratic is decreasing and is already negative at \(1/4\).

For \(x\le1/4\), use the positive-coefficient part of the expanded
polynomial,
\[
A_{33}\le132+326x+339x^6+396x^7+141x^8+18x^9,
\]
and \(s\le S=x+x^2\). The resulting upper bound on
\(A_{32}+3A_{33}S\) is
\[
\begin{aligned}
-24-756x-2098x^2-3632x^3-\tfrac{6161}{2}x^4
+123x^5+\tfrac{5529}{2}x^6+4092x^7+3888x^8\\
+2082x^9+531x^{10}+54x^{11}.
\end{aligned}
\]
Its positive tail is at most
\[
\left(\frac{123}{4}+\frac{26823}{32}\right)x^4
=\frac{27807}{32}x^4<\frac{6161}{2}x^4.
\]
It is therefore negative. Since \(A_{32}+3A_{33}s\) is affine in \(s\),
these endpoint comparisons prove the asserted concavity.

It remains to check the two endpoints of (8).

At the lower endpoint, \(s=\gamma-x\) is covered by (10).
When the lower endpoint is \(s=0\), Appendix A gives
\[
\frac{A_{30}}{xW^2}
\ge54-440x^2+1703x^4>0.
\]
The first inequality uses \(140-86x\ge54\) and drops only the
displayed positive terms. The quadratic in \(x^2\) is positive because
\(440^2<4\cdot1703\cdot54\).

At the upper endpoint \(s=x+x^2\), exact substitution gives
\[
\begin{aligned}
\frac{J_3}{x^3W^2}
={}&-16-44x+1211x^2+\tfrac{8243}{2}x^3\\
&+x^4\left(\tfrac{13509}{2}+7244x+6458x^2+
 \tfrac{11857}{2}x^3+\tfrac{9873}{2}x^4+
 2913x^5+1062x^6+213x^7+18x^8\right).
\end{aligned}
\]
The first four terms are increasing for \(x\ge3/25\) and exceed \(3\)
at \(x=3/25\); the remainder is positive.

If the upper endpoint is \(s=1-x\), then
\(1-x\le x+x^2\), so \(x\ge\sqrt2-1>2/5\). Here
\[
J_3/x^2=-48-968x+1220x^2+7492x^3+
9840x^4+6048x^5+1872x^6+240x^7>0.
\]
Its first four terms are increasing for \(x\ge2/5\) and exceed \(200\)
at \(2/5\). Concavity now proves \(J_3>0\).

## 7. The fourth bound

First suppose \(3/25<x<1/8\). Direct lower bounds from Appendix A are
\[
A_{40}\ge\frac{7059}{800},\qquad A_{41}>0,\qquad
A_{42}>-217,\qquad A_{43}>0.
\]
For transparency, the first follows by keeping
\(xW^2(148-482x-910x^2)\), using \(x\ge3/25\), \(W^2\ge1\),
and \(x\le1/8\).
For \(A_{41}/W\), keeping its first four terms gives
\(-276+1118x+8137x^2+17546x^3>5\) at \(x\ge3/25\).
For \(A_{42}\), its negative terms at \(1/8\), together with its
constant \(168\), exceed \(-217\).
For \(A_{43}/W\), the lower bound
\(444-491/64-1546/512-1739/8192>433\) suffices.
Since \(s\le9/64\),
\[
J_4/x^2>\frac{7059}{800}-217(9/64)^2>4.
\tag{11}
\]

For \(x\ge1/8\), \(J_4/x^2\) is increasing in \(s\).
Here is an explicit proof that does not assume concavity.
Put \(S=x+x^2\). The derivative in \(s\), at \(s=S z\), equals
\[
A_{41}(1-z)^2+
2(A_{41}+A_{42}S)z(1-z)+
(A_{41}+2A_{42}S+3A_{43}S^2)z^2.
\]
All three coefficients are positive. Appendix A shows this for
\(A_{41}\); its first four terms are already positive at \(1/8\).
For the other two, direct collection gives
\[
\begin{aligned}
A_{41}+A_{42}S={}&-276+1010x+7375x^2+16715x^3+
\tfrac{45665}{2}x^4\\
&+x^5(25598+\tfrac{58089}{2}x+\tfrac{61959}{2}x^2+
\tfrac{51103}{2}x^3+14410x^4+\tfrac{10255}{2}x^5+
\tfrac{2065}{2}x^6+90x^7),\\
\frac{A_{41}+2A_{42}S+3A_{43}S^2}{W}
={}&-276+1454x+5373x^2+8092x^3+
\tfrac{12183}{2}x^4\\
&+1373x^5+\tfrac{6569}{2}x^6+
\tfrac{26381}{2}x^7+\tfrac{36673}{2}x^8+
12930x^9+\tfrac{10085}{2}x^{10}+
\tfrac{2085}{2}x^{11}+90x^{12}.
\end{aligned}
\]
Every nonconstant coefficient is positive. At \(x=1/8\), the
first five terms in the first polynomial exceed \(3\), and the
first four terms in the second exceed \(5\). Both increase thereafter.

For \(1/8\le x\le\gamma\), the lower endpoint is the cap (10).
For \(x\ge\gamma\), it remains to show \(A_{40}>0\).
Write \(A_{40}=xW^2 f(x)\), with \(f\) displayed in Appendix A.
For all \(x\ge\gamma>1/4\),
\[
f''(x)>
-1820+\frac{6531}{4}+\frac{51108}{16}
+\frac{102360}{64}+\frac{101175}{256}
=\frac{1280407}{256}>5000.
\]
All omitted terms of \(f''\) are positive. At \(c_0=3/10\),
\[
f(c_0)=\frac{118625243}{200000000}>\frac{59}{100},
\qquad
f'(c_0)=-\frac{12963121}{1250000},\qquad |f'(c_0)|<11.
\]
Integrating the second-derivative bound in either direction from
\(c_0\) gives
\[
f(x)\ge f(c_0)+f'(c_0)(x-c_0)+2500(x-c_0)^2
>\frac{59}{100}-\frac{121}{10000}
=\frac{5779}{10000}>0.
\]
This proves \(J_4>0\).

## 8. The positive lower bound on the cubic coefficient

For \(J_*\), use the explicit cubic Bernstein identity and coefficients
in Appendix B.

If \(0<x\le2/5\), choose \(S=x+x^2\).
After removing the positive common factor \(xW^2\), the four
coefficients have the following elementary lower bounds:
\[
\begin{aligned}
b_0/(xW^2)&\ge284-\tfrac{51}{2}x>258,\\
b_1/(xW^2)&\ge840-761(2/5)^2-\tfrac{1331}{2}(2/5)^3>675,\\
b_2/(xW^2)&\ge828-1462(2/5)^2-\tfrac{729}{2}(2/5)^3>570,\\
b_3/(xW^2)&\ge272-140(2/5)-733(2/5)^2-\tfrac{145}{2}(2/5)^3>94.
\end{aligned}
\]
These follow by dropping only positive terms in the displayed
polynomials. For \(b_0\), use \(x^2,x^3\le x\).

If \(2/5\le x<1\), choose \(S=1-x\).
The same \(b_0\) bound applies. For the other three coefficients,
Appendix B gives
\[
\begin{aligned}
b_1/W&\ge-12+282x+575x^4-208x^5>100,\\
b_2&\ge-48-264x+1252x^2>46,\\
b_3&\ge h(x):=-48-104x-268x^2+1804x^3+4368x^4>94.
\end{aligned}
\]
For the first, \(575x^4-208x^5\ge0\).
The second quadratic increases for \(x\ge2/5\) and equals
\(1168/25>46\) at \(2/5\).
Finally
\(h'(x)\ge-104+(8144/5)x>0\) on this range and
\(h(2/5)=59248/625>94\).
Thus all four Bernstein coefficients are positive in both ranges.
Since (8) gives \(0\le s\le S\) for the selected \(S\), it follows
that \(J_*>0\).

Sections 4--8 prove every sign in (7); Section 3 proves \(P>0\);
and Section 2 proves the stated theorem \(N>0\).


## Appendix A. The four cubic expansions

The following identities specify every coefficient used above. They are
ordinary polynomial expansions of (7), with no sign or sampling oracle.
Put \(W=1+x\). In each row,
\[
J_i/x^2=A_{i0}+A_{i1}s+A_{i2}s^2+A_{i3}s^3,
\qquad t=(1-x-s)/2.
\]

### The coefficients for \(J_1\)

\[
A_{10}=xW^{2}\bigl(-148+162x+1060x^{2}+\frac{3453}{2}x^{3}+1506x^{4}+\frac{1609}{2}x^{5}+245x^{6}+30x^{7}\bigr).
\]
\[
A_{11}=W^{2}\bigl(36+1766x+3757x^{2}+4202x^{3}+\frac{6677}{2}x^{4}+\frac{3917}{2}x^{5}+685x^{6}+90x^{7}\bigr).
\]
\[
A_{12}=\bigl(-408+288x+3000x^{2}+5738x^{3}+\frac{13323}{2}x^{4}+5396x^{5}+\frac{5667}{2}x^{6}+815x^{7}+90x^{8}\bigr).
\]
\[
A_{13}=W\bigl(-444-774x-369x^{2}+351x^{3}+\frac{1029}{2}x^{4}+225x^{5}+30x^{6}\bigr).
\]

### The coefficients for \(J_2\)

\[
A_{20}=xW^{2}\bigl(-28-178x+360x^{2}+\frac{3963}{2}x^{3}+3091x^{4}+\frac{4969}{2}x^{5}+1195x^{6}+345x^{7}+45x^{8}\bigr).
\]
\[
A_{21}=W\bigl(396+3942x+10973x^{2}+15729x^{3}+\frac{28611}{2}x^{4}+9952x^{5}+\frac{12307}{2}x^{6}+3135x^{7}+1005x^{8}+135x^{9}\bigr).
\]
\[
A_{22}=\bigl(1272+3168x+3440x^{2}+1738x^{3}+\frac{1653}{2}x^{4}+2531x^{5}+\frac{8147}{2}x^{6}+2985x^{7}+1035x^{8}+135x^{9}\bigr).
\]
\[
A_{23}=W\bigl(876+1286x+361x^{2}-279x^{3}+\frac{439}{2}x^{4}+550x^{5}+285x^{6}+45x^{7}\bigr).
\]

### The coefficients for \(J_3\)

\[
A_{30}=xW^{2}\bigl(140-86x-440x^{2}+\frac{449}{2}x^{3}+1703x^{4}+\frac{4683}{2}x^{5}+1665x^{6}+693x^{7}+165x^{8}+18x^{9}\bigr).
\]
\[
A_{31}=W\bigl(-156+66x+2671x^{2}+6911x^{3}+\frac{18725}{2}x^{4}+9000x^{5}+\frac{14001}{2}x^{6}+4317x^{7}+1863x^{8}+477x^{9}+54x^{10}\bigr).
\]
\[
A_{32}=\bigl(-24-1152x-3472x^{2}-4610x^{3}-\frac{6161}{2}x^{4}+123x^{5}+\frac{5529}{2}x^{6}+3075x^{7}+1683x^{8}+471x^{9}+54x^{10}\bigr).
\]
\[
A_{33}=W\bigl(132+194x-221x^{2}-769x^{3}-\frac{1143}{2}x^{4}+66x^{5}+273x^{6}+123x^{7}+18x^{8}\bigr).
\]

### The coefficients for \(J_4\)

\[
A_{40}=xW^{2}\bigl(148-482x-910x^{2}+\frac{2177}{2}x^{3}+4259x^{4}+5118x^{5}+\frac{6745}{2}x^{6}+\frac{2655}{2}x^{7}+\frac{595}{2}x^{8}+30x^{9}\bigr).
\]
\[
A_{41}=W\bigl(-276+1118x+8137x^{2}+17546x^{3}+\frac{43249}{2}x^{4}+19548x^{5}+14664x^{6}+\frac{17525}{2}x^{7}+\frac{7215}{2}x^{8}+\frac{1725}{2}x^{9}+90x^{10}\bigr).
\]
\[
A_{42}=\bigl(168-2048x-6920x^{2}-9418x^{3}-\frac{12313}{2}x^{4}+989x^{5}+6564x^{6}+\frac{13235}{2}x^{7}+\frac{6645}{2}x^{8}+\frac{1705}{2}x^{9}+90x^{10}\bigr).
\]
\[
A_{43}=W\bigl(444+574x-491x^{2}-1546x^{3}-\frac{1739}{2}x^{4}+385x^{5}+\frac{1195}{2}x^{6}+\frac{455}{2}x^{7}+30x^{8}\bigr).
\]


## Appendix B. Four Bernstein coefficients for \(J_*\)

Write \(J_*/x^2=a_0+a_1s+a_2s^2+a_3s^3\), and set
\[
b_0=a_0,\quad b_1=3a_0+a_1S,\quad
b_2=3a_0+2a_1S+a_2S^2,\quad
b_3=a_0+a_1S+a_2S^2+a_3S^3.
\]
For \(s=S z\), the exact identity is
\[
J_*/x^2=b_0(1-z)^3+b_1z(1-z)^2+b_2z^2(1-z)+b_3z^3.
\]
Thus positivity of the four displayed coefficients proves positivity
throughout \(0\le s\le S\).

### The choice \(S=x+x^2\)

\[
b_0=xW^{2}\bigl(284+466x-20x^{2}-\frac{943}{2}x^{3}+71x^{4}+\frac{1797}{2}x^{5}+948x^{6}+486x^{7}+138x^{8}+18x^{9}\bigr).
\]
\[
b_1=xW^{2}\bigl(840+816x-761x^{2}-\frac{1331}{2}x^{3}+\frac{6023}{2}x^{4}+\frac{12975}{2}x^{5}+\frac{12591}{2}x^{6}+3894x^{7}+1674x^{8}+450x^{9}+54x^{10}\bigr).
\]
\[
b_2=xW^{2}\bigl(828+210x-1462x^{2}-\frac{729}{2}x^{3}+4800x^{4}+9263x^{5}+9210x^{6}+\frac{13587}{2}x^{7}+4218x^{8}+1908x^{9}+498x^{10}+54x^{11}\bigr).
\]
\[
b_3=xW^{2}\bigl(272-140x-733x^{2}-\frac{145}{2}x^{3}+\frac{4389}{2}x^{4}+3623x^{5}+2552x^{6}+\frac{2863}{2}x^{7}+\frac{3201}{2}x^{8}+1512x^{9}+756x^{10}+186x^{11}+18x^{12}\bigr).
\]

### The choice \(S=1-x\)

\[
b_0=xW^{2}\bigl(284+466x-20x^{2}-\frac{943}{2}x^{3}+71x^{4}+\frac{1797}{2}x^{5}+948x^{6}+486x^{7}+138x^{8}+18x^{9}\bigr).
\]
\[
b_1=W\bigl(-12+282x+2131x^{2}+2788x^{3}+575x^{4}-208x^{5}+2568x^{6}+4524x^{7}+3126x^{8}+1008x^{9}+126x^{10}\bigr).
\]
\[
b_2=\bigl(-48-264x+1252x^{2}+6136x^{3}+7418x^{4}+3896x^{5}+3534x^{6}+5556x^{7}+4416x^{8}+1644x^{9}+264x^{10}+12x^{11}\bigr).
\]
\[
b_3=\bigl(-48-104x-268x^{2}+1804x^{3}+4368x^{4}+3768x^{5}+1512x^{6}+240x^{7}\bigr).
\]


## Appendix C. The common cap endpoints

At \(t=13/35\),
\[
\frac{J_i(13/35,x)}{x^2}=\frac{g_i}{42875}Q_i(x),
\qquad (g_1,g_2,g_3,g_4)=(176,8,8,4).
\]
The four polynomials are

\[
Q_1=-6156+142478x-138007x^{2}-917627x^{3}-1131283x^{4}-618897x^{5}-154830x^{6}-13130x^{7}.
\]

\[
Q_2=1076328+588356x-3170634x^{2}-32651894x^{3}-79121826x^{4}-88222894x^{5}-53273470x^{6}-17876235x^{7}-3149640x^{8}-238875x^{9}.
\]

\[
Q_3=-211464+1009628x+7306874x^{2}-1652150x^{3}-40822124x^{4}-71476494x^{5}-59891598x^{6}-28108167x^{7}-7388667x^{8}-980031x^{9}-47775x^{10}.
\]

\[
Q_4=-560736+3729368x+24197948x^{2}-34283592x^{3}-213288048x^{4}-326141252x^{5}-252912130x^{6}-111570125x^{7}-27778530x^{8}-3505645x^{9}-159250x^{10}.
\]


All coefficients of degree at least two in \(Q_1,Q_2\) are negative.
Hence both are concave on the positive axis. For \(Q_3,Q_4\), the
linear and quadratic coefficients are positive and every coefficient
of higher degree is negative. Consequently
\[
\frac{d}{dx}\!\left(\frac{Q_i'(x)}x\right)<0,\qquad i=3,4.
\]
Each therefore has at most one interior critical point on a positive
interval, and such a point is a maximum. Every \(Q_i\) takes its
minimum on \([3/25,9/35]\) at an endpoint.

Here are convenient rational lower bounds at those endpoints.
They are obtained by substituting the two stated fractions into the
displayed polynomials and multiplying by the positive denominator;
no logarithmic approximation remains.

| Polynomial | At \(x=3/25\) | At \(x=9/35\) |
|---|---:|---:|
| \(Q_1\) | \(>7000\) | \(>65\) |
| \(Q_2\) | \(>1000000\) | \(>800\) |
| \(Q_3\) | \(>1600\) | \(>200000\) |
| \(Q_4\) | \(>120000\) | \(>34000\) |

For example, the smallest cap endpoint used by the first bound is
\[
Q_1(9/35)=\frac{846532582236}{12867859375}>65,
\]
and the small-\(x\) endpoint of the third bound is
\[
Q_3(3/25)=
\frac{6190342211084388}{3814697265625}>1600.
\]
This proves the four cap endpoint claims used in the body of the note.
