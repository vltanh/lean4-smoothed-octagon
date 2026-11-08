# The central displacement face is strictly negative

**Replacement status, 2026-11-08:** the [new shape derivative proof](../../docs/lighter-proofs/SHORT_DISPLACEMENT_CENTRAL_SHAPE.md)
replaces Section 2, equations (4)--(10), on the actual comparison path.
Both exact-log derivative signs reach the same endpoint used below.
The beta reduction in Section 1 and the separate endpoint signs in
Section 3 remain dependencies; the latter are outside the requested S3.2 row.

Date: 2026-11-08 UTC. Conditional scalar hand theorem. Together with
[the displacement reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md),
this excludes the central scale face for an actual candidate with
\(2\le x\le13/6\) and \(\delta\ge1/19\). It does not prove the
upper or lower ratio hypotheses, or the outer scale face.

Use the definitions \(u,p,q,T,D,K,\lambda,d,w,E_L,J,n_i,F_i\) in
[the central beta monotonicity lemma](MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_BETA.md).
The functions \(F_i=J+n_i(w-3/4)\) retain the exact logarithm
until the final endpoint estimate.

## 1. The exact shape gives a convenient straight order bound

The [rational quadratic order](MIXED_SMALLER_SHORT_RATIONAL_QUADRATIC_ORDER.md)
shows, when \(\delta\ge1/19\), that
\[
\alpha>1+\left(c(x)+\frac1{23}\right)\delta,
\qquad c(x)=\frac{4x^2+11x+1}{7x+1}.
\]
Put
\[
C(x)=\frac{15x+36}{25},\qquad B(x)=\frac{x}{C(x)}.
\tag{1}
\]
The simpler lower order is valid because
\[
c(x)+\frac1{23}-C(x)
=\frac{-115x^2+359x-228}{575(7x+1)}>0.
\tag{2}
\]
The numerator is concave; its endpoint values on \([2,13/6]\)
are \(30\) and \(359/36\). Consequently
\[
a_{\min}(x):=1+C(x)/19<\alpha,
\qquad \beta< b(x,\alpha):=x+B(x)(\alpha-1).
\tag{3}
\]
At a central scale face, \(q_c\le1/7\) gives
\(\alpha^2\le x(x+2)/6\), hence \(\alpha\le(5x+4)/12\).
The whole beta comparison segment from the original beta to \(b\)
satisfies the hypotheses of the central beta lemma. Indeed
\(C>13/5\), and
\[
\frac{b}{\alpha}\le
\frac{20x}{19+C}<2,
\qquad 19+C-10x=\frac{511-235x}{25}\ge\frac{11}{150}>0.
\]
Also \(\beta\ge20x/19\) and \(\alpha>108/95\).
Therefore both tests increase when beta is raised to \(b\).

## 2. Both tests decrease along the straight order boundary

We prove the following rational derivative signs on the larger rectangle
\[
2\le x\le13/6,\qquad 108/95\le a\le89/72,
\qquad \beta=b(x,a):
\qquad \frac{d}{da}F_i(x,a,b(x,a))<0\quad(i=0,1).
\tag{4}
\]
The enclosing rectangle is used only for these scalar derivative
signs. All physical and equal-secant hypotheses enter through (3).

Here are complete rational specifications for the two signs. Set
\[
L=2a/K,\qquad e=\frac{2[a+b+(a-x)B]}K,
\qquad u_b=-\frac{(x-1)(g(x)-1/5808)}{(b-1)^2},
\]
\[
Y=y\left(\frac2a-L-\frac{x-B}{a(a+b)}\right),
\quad N_0=-\frac{12Y}{k}-\frac{20(4-3y)}{k^2},
\quad N_1=-\frac{TY}{y}-\frac{20}{k^2},
\]
where \(g,y,k\) have the definitions in the beta lemma. Direct
chain differentiation gives the exact identity
\[
\begin{aligned}
H_i:=\frac{dF_i}{da}
={}&\frac{x-B}{a^2}\{U(p)-u\}
 +\frac{2(1-q)^2}{a}
 +e(n_iE_L-2u)+L(E_L-2n_iw)\\
&+B u_b\{p^{-1}+\lambda S-2d+n_i d(d-\lambda S)\}
 +N_i(w-3/4).
\end{aligned}
\tag{5}
\]
In particular the logarithmic derivative has been included exactly;
there is no derivative estimate of a logarithm majorant.

Define the positive polynomials
\[
A=25ax+15x^2-4x-36=3(5x+12)(b-1),
\]
\[
Z=40ax+36a+15x^2+11x=3(5x+12)(a+b),
\]
\[
\mathcal D_i=104544a^2xk^2S(5x+12)^{3-i}
 K^{4-i}(13x^2+14x+3)A^2Z^2.
\tag{6}
\]
Every factor is positive. Let \(P_i=-\mathcal D_iH_i\); (5)--(6)
specify ordinary polynomials, of degrees at most \((24,14)\) and
\((22,12)\) in \((x,a)\). Put \(h=x-2\), \(z=a-108/95\),
and \(\widehat P_i=P_i/P_i(2,108/95)\). The two positive
normalizing constants are
\[
P_0(2,108/95)=\frac{190839883929369973027165057485314832196893295509504}{39013998329242388720703125},
\qquad P_1(2,108/95)=\frac{102398593081439047216086099622599101869326336}{4322880701301095703125}.
\]

The following single product majorant proves both signs. Define
\[
\begin{aligned}
V(z)={}&3z^2+20z^3+34z^4+25z^5+17z^6+8z^7+2z^8\\
&+9z^9+8z^{10}+3z^{11}+z^{12}+z^{13}+z^{14},
\end{aligned}
\]
\[
M(h,z)=V(z)(1+h)^{12}+20h^6z
             +1000h^7(1+h)^{17}(1+z)^{14}.
\tag{7}
\]
For both completely specified polynomials in (6), multiplication and
collection in \(h,z\) gives the coefficientwise inequality
\[
\boxed{\widehat P_i(h,z)\succeq1-M(h,z).}
\tag{8}
\]
Here \(P\succeq Q\) means every coefficient of \(P-Q\) is
nonnegative. To make the finite comparison explicit, write \(v_j\)
for the fourteen displayed coefficients of \(V\), taking omitted
coefficients to be zero. For powers \(h^rz^j\) with \(r\le6\),
the entire adverse coefficient is bounded by
\(\binom{12}{r}v_j+20\mathbf1_{(r,j)=(6,1)}\).
For \(r\ge7\), it is bounded by
\(\binom{12}{r}v_j+1000\binom{17}{r-7}\binom{14}{j}\).
As usual a binomial coefficient outside its range is zero. These
are ordinary coefficient comparisons of the factored polynomials
(5)--(6); no subdivision, coefficient minimum or executable table
is a premise of (8). The full adverse majorant is the printed
polynomial (7).

On the rectangle (4), \(0\le h\le1/6\) and
\(0\le z\le679/6840<1/10\). Every coefficient of \(M\) is
nonnegative, and
\[
V(1/10)=\frac{5366782983111}{10^{14}}<\frac{27}{500},
\]
\[
(7/6)^{12}<13/2,\quad (7/6)^{17}<14,
\quad(11/10)^{14}<4.
\]
It follows by direct rational bounds that
\[
M(h,z)<\frac{351}{1000}+\frac1{20000}
            +\frac{56000}{279936}
<\frac{351}{1000}+\frac1{20000}+\frac{201}{1000}
<\frac35.
\tag{9}
\]
Equations (6)--(9) prove \(\widehat P_i>2/5\), and hence (4).
Decreasing alpha from its value in (3) to \(a_{\min}\) therefore
raises both scalar tests. All beta-lemma hypotheses also hold along
this path. The endpoint has
\[
\boxed{a=a_{\min}=(15x+511)/475,\qquad b=20x/19.}
\tag{10}
\]

## 3. One rational logarithm estimate at the endpoint

The beta lemma gives \(0<y\le6/7\). For this interval,
\[
\log y\le-\frac{40153}{180000}
             +\frac{2(5y-4)}{5y+4}=:L_*(y).
\tag{11}
\]
For completeness, \(\log(4/5)<-2231/10000\) follows from the
first three positive terms of the atanh expansion of \(\log(5/4)\).
Put \(s=(5y-4)/(5y+4)\). If \(s\le0\), the remainder after
\(2s\) in \(2\operatorname{atanh}s\) is nonpositive. If
\(0\le s\le1/29\), it is at most
\[
\frac{2s^3}{3(1-s^2)}\le\frac1{36540}<\frac1{36000}.
\]
Adding this to \(-2231/10000\) gives (11). The series estimates
can equivalently be obtained by integrating the finite geometric
identity for \((1-s^2)^{-1}\), with its displayed signed remainder.

Replace the exact logarithm in \(F_i\), only at (10), by (11),
and call the resulting upper expressions \(\overline F_i\).
Here are the complete remaining univariate identities. Set
\[
Q=225850x^2+466580x+261121,
\quad W=490325x^2+2287310x+1827847,
\]
\[
D_*=21780000x(x+1)(15x+416)(15x+511)(20x-19)
 (515x+511)(13x^2+14x+3)W.
\]
All factors are positive, and
\[
-\overline F_i=\frac{N_i(x-2)}{D_*Q^{3-i}}.
\tag{12}
\]
The following two lists give every coefficient of \(N_i(h)\) in
ascending powers of \(h\).

### Polynomial \(N_0\)

```text
2413534919007629868137070688732034410098588,
-26254301047758970029152099025587912698031754,
70210600598363805662951295893340160342087806,
1231260666018762280352657134177895028581204721,
4498601593628546463194691113956045245845235813,
8821418563599351427456297390873555558331292630,
11155720247429732414771122665383587490751693525,
9824378285326805045976584313731635978432494375,
6260501806502667667485414232430338901594628125,
2940300218027638502485142956836091990035603125,
1022727874541701156868178804828673324875796875,
261642089606588828515012621238014687723906250,
48258209590394165569656174095510203980468750,
6179636018751166406735015238165612880859375,
513881158757646744686699205111204707031250,
24541332826675464716798510630404980468750,
526347440193952489082215283692382812500,
3679624501492989173967224121093750000
```

### Polynomial \(N_1\)

```text
1066695320050756620827029638308435448,
-11554078212748962290130793009859116224,
43895838980852054366148716751111284496,
530856372984235900631901782361718380936,
1660483178009696646905224092812029954443,
2808623110857556111554791547311208452940,
3038756659112858923251352168551179093150,
2258207973164675397156836896798409091500,
1192602713354221799935768401537330971250,
453660106978019845283139933325845987500,
124044858401168171760883592299032562500,
23953632656597836417010188357685000000,
3143798989151344183582072553027734375,
260593616101531121669269257914062500,
11745215959060390878951090878906250,
194414857058510946990966796875000
```

Write \(v=6h\in[0,1]\), and normalize either polynomial by
its displayed positive constant \(c_0=N_i(0)\). From the first
four entries of each list,
\[
\frac{c_1}{6c_0}>-2,\qquad
\frac{c_2}{36c_0}>\frac45,\qquad
\frac{c_3}{216c_0}>2.
\]
All later coefficients are positive. Thus both normalized
polynomials exceed
\[
1-2v+\frac45v^2+2v^3.
\]
The identity \(2v(v-1/2)^2\ge0\) gives
\[
1-2v+\frac45v^2+2v^3
\ge1-\frac52v+\frac{14}{5}v^2
=\frac{14}{5}\left(v-\frac{25}{56}\right)^2
 +\frac{99}{224}>0.
\tag{13}
\]
This proves both strict endpoint signs without a root search.

## 4. Central-face conclusion

The original incoming norm is raised to the stated ceiling only
after the scale comparison, using the positive incoming coefficient
from the displacement-weight reduction. Beta monotonicity then
raises each test to (3), the alpha derivative raises it to (10),
and (11)--(13) prove that even the endpoint upper bound is negative.
Hence both tests are strictly negative on the entire central face
of an actual candidate with \(2\le x\le13/6\), \(\delta\ge1/19\).
No physical root, cost, outgoing floor or Casimir cap has been moved
to an artificial shape. The outer scale face remains a separate
obligation before this can exclude the full displacement range.
