# A hand sign for the outer face of the short upper-ratio reduction

**Replacement status, 2026-11-08:** the [new outer-ratio assembly](../../docs/lighter-proofs/SHORT_RATIO_OUTER_COMPLETE.md)
replaces the large signs (11)--(18) with reciprocal-shape convexity,
a lower-shape beta comparison, and three terminal families. It retains
the actual condition `a<=x`, both original incoming ceilings and both
duration tests. Every expanded identity has degree at most eight and
at most 35 monomials. The exact original caller closes.

Date: 2026-11-08 UTC. **Result:** the outer scale face cannot carry
the positive variable-floor test when \(13/6\le x\le12/5\).
This complete proof is accepted in the
[reconstruction audit](MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_AUDIT.md).
Together with the [central sign](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md)
and the accepted variable-floor reduction it supplies the two terminal
signs needed for the independently reviewed S2 actual-period assembly.

The proof splits at \(\alpha=3/2\). For the smaller shapes, elementary
monotonicities reduce to two one-variable signs. For the larger shapes,
two low-degree polynomials have explicitly positive Bernstein lower
bounds. The complete coefficient-norm lower polynomials are printed;
there is no hidden coefficient minimum or executable sign premise.

## 1. Outer face and exact transport

Write \(a=\alpha\), \(b=\beta\), and assume

\[
13/6\le x\le12/5,\qquad
1\le a\le x,\qquad a^2\ge\frac{x(x+2)}6,
\tag{1}
\]
\[
x+\frac{8x(a-1)}{9x+8}\le b
\le x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
\tag{2}
\]

The original equal-secant shape is used to supply its incoming norm u.
The outer scale is \(q=1/7\). For any scalar u put

\[
S=1+x,\quad B=a+b,\quad M=6a^2+1,
\quad D=a^2+2ab+1+2x-2bx,
\]
\[
N=M\{S(u-1)+S^{-1}\}+2S-1,
\]
\[
w=\frac{M^2-MS+S^2+D^2u-DN}{49a^4},
\quad E_L=\frac{2Du-N}{7a^2},
\quad k=\frac{B}{7a}=\frac1T,
\quad h=w-\frac34.
\tag{3}
\]

These are the original upper-envelope covector formulas at outer
scale. Define

\[
\begin{aligned}
G_\tau={}&(w-1)\tau+\tau^{-1}+(u-1)B/a+a/B+6/7-E_L
          +\log(\tau k)\\
 &+\left(2-\frac{7\tau k}{4}\right)h,
\qquad 2\le\tau\le T.
\end{aligned}
\tag{4}
\]

At a central or outer comparison endpoint, the
[variable-floor reduction](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
permits raising the original incoming norm to a proved upper bound:
the coefficient of u is strictly positive. We will use different
proved bounds on the two sides of \(a=3/2\), and prove (4) strictly
negative after either replacement. No outgoing floor, upper Casimir
cap or physical cost is assigned to a scalar endpoint.

## 2. Duration and elementary shape simplifications

The exact derivative is

\[
G_\tau'=\left(1-\frac{7k}{4}\right)h
          -\frac{(\tau-2)^2}{4\tau^2}
\le\left(1-\frac{7k}{4}\right)h.
\]

Integrating, and retaining both signs of h, gives

\[
G_\tau\le\max\{H_0,H_1\},
\tag{5}
\]
\[
\begin{aligned}
H_0={}&6/7+(u-1)B/a+a/B-E_L
       +\left(4-\frac{B}{2a}\right)h+\log(2k),\\
H_1={}&6/7+(u-1)B/a+a/B-E_L
       +\left(\frac{7a}{B}+\frac14\right)h+\log(2k).
\end{aligned}
\tag{6}
\]

The first is exactly \(G_2\), and the second is
\(G_2+(T-2)(1-7k/4)h\). Thus (5) does not assume that the
comparison norm satisfies its original strict floor.

The following shape bounds will be used:

\[
a\ge a_f(x):=\frac{36x+25}{84},
\quad b=x+c(a-1),\quad
\frac58\le c\le c_+(x):=\frac{24x+51}{128}<\frac78.
\tag{7}
\]

For the alpha lower bound, the difference of the squared bounds has
positive numerator

\[
84^2x(x+2)-6(36x+25)^2=-720x^2+3312x-3750.
\]

This is a concave quadratic, with positive endpoint values 46 and
258/5. The two c bounds follow from (2); their elementary proofs are
printed in Section 2 of the
[central-face theorem](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md).
When \(a=1\), the beta endpoints coincide, but the outer face (1)
in fact has \(a\ge103/84>1\).

On every enlarged scalar domain used below, \(a\ge1\),
\(5/8\le c\le7/8<x\), and therefore \(b\le ax\). In particular

\[
0<2k=\frac{2(a+b)}{7a}\le\frac{2(1+x)}7\le\frac{34}{35}<1.
\tag{8}
\]

All duration intervals remain nonempty and every logarithm is valid.

## 3. Two incoming-norm bounds

### 3.1. Smaller shapes: \(a\le3/2\)

The strong upper beta endpoint in (2) gives

\[
\frac{b-x}{x}\le\frac{7x+1}{2(4x^2+11x+1)}<\frac15.
\]

The last sign is \(8x^2-13x-3>0\); it is positive at \(13/6\)
and increasing thereafter. The
[Gauss secant estimate](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md)
at \(b=x\) gives
\(V(x)-3/4<17(x-1)^2/(240S^2)\). Splitting the positive incoming
integral at x and bounding its tail therefore yields

\[
u_{\rm actual}\le u_s:=\frac34+
 \frac{17(x-1)^3/(240S^2)+(b-x)/1200}{b-1}.
\tag{9}
\]

Indeed the tail is at most
\((b-x)^3/(48x^2)\le(b-x)/1200\). The exact secant relation is
used only to identify the original incoming norm and the shape order;
the later scalar motions do not assert another equal-secants shape.

### 3.2. Larger shapes: \(a\ge3/2\)

The exact equal-secant comparison in
[the short-bridge continuation](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md)
gives u_actual<=V(x); its full-domain proof is also recalled in
Section 1 of the displacement-weight reduction. Applying the
[rational incoming estimate](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
to V(x) then gives the uniform bound

\[
u_{\rm actual}\le u_v:=\frac34+
 \frac{2(x-1)^2}{S(35x+13)}.
\tag{10}
\]

Both replacements are used first at the original shape and the outer
scale endpoint, where incoming-norm monotonicity has already been
proved. Subsequent steps compare explicit scalar expressions only.

## 4. Smaller shapes reduce to one variable

In this section put \(u=u_s\) in (3),(6), and write

\[
\mathcal H_j(x,a,c)=H_j(x,a,x+c(a-1);u_s),\qquad j=0,1.
\]

The following derivative signs hold:

\[
\boxed{\partial_a\mathcal H_j<0}
\quad\left(13/6\le x\le12/5,\ 6/5\le a\le3/2,
\ 5/8\le c\le7/8\right),
\tag{11}
\]
\[
\boxed{\partial_c\mathcal H_j(x,a_f(x),c)>0}
\quad\left(13/6\le x\le12/5,\ 5/8\le c\le7/8\right).
\tag{12}
\]

Appendix A proves all four signs from finite derivative polynomials
and complete coefficient-norm lower polynomials. The logarithm is
differentiated exactly throughout these comparisons.

The original alpha satisfies
\(a\ge a_f(x)\ge103/84>6/5\), and
\(a_f(x)\le557/420<3/2\). Thus (11) lowers alpha to \(a_f(x)\)
at fixed x,c within its full domain. Equation (12), together with
(7), then increases c to \(c_+(x)\). Consequently

\[
\mathcal H_j(x,a,c)
\le\mathcal H_j(x,a_f(x),c)
\le\mathcal H_j(x,a_f(x),c_+(x)).
\tag{13}
\]

There is no need for \(H_j\) to increase with beta at all larger
alpha values. The c comparison is used only after alpha is at its
proved lower endpoint.

## 5. One global polynomial logarithm bound

For \(0<y\le1\), put \(z=y-1\le0\). Integrating
\((1-t)^{-1}\ge1+t+t^2\) from zero to \(1-y\) gives

\[
\log y\le L(y):=z-\frac{z^2}{2}+\frac{z^3}{3}.
\tag{14}
\]

By (8), this applies everywhere it will be used.
Let \(\overline H_j\) denote (6) with \(L(2k)\) in place of
\(\log(2k)\), using whichever incoming bound is specified.

For the smaller-shape terminal expressions in (13), set

\[
\Theta(x)=288x^2+3724x-4587,\quad
\Psi(x)=864x^2+15780x+191,
\]
\[
D_{s0}=431593881600\,S^2(36x+25)^5\Theta\Psi,
\]
\[
D_{s1}=3371827200\,S^2(36x+25)^4\Theta\Psi,
\tag{15}
\]
\[
P_{sj}(x)=-D_{sj}\,
 \overline H_j(x,a_f(x),x+c_+(x)(a_f(x)-1);u_s).
\tag{16}
\]

The denominators in (15) are positive. In particular
\(\Theta(13/6)=14501/3>0\), \(\Theta'>0\), and \(\Psi\)
has positive coefficients. The degrees of \(P_{s0},P_{s1}\) are
14 and 13. Appendix B prints their entire coefficient vectors after
\(x=13/6+X\), and proves both strictly positive. Thus (13)--(16)
show \(H_0,H_1<0\) for every original smaller shape.

## 6. Larger shapes: two global polynomial signs

Put \(u=u_v\) from (10), and enlarge the shape domain to

\[
13/6\le x\le12/5,\quad3/2\le a\le12/5,
\quad b=x+c(a-1),\quad5/8\le c\le7/8.
\tag{17}
\]

The original condition \(a\le x\) may be dropped in this scalar
sign test. No geometric conclusion is attached to the added points.
By (8), the polynomial logarithm bound (14) remains valid.
Define

\[
D_{v0}=8232\,a^5S(35x+13)(a+b),
\quad D_{v1}=16464\,a^4S(35x+13)(a+b),
\]
\[
P_{vj}(x,a,c)=-D_{vj}\overline H_j(x,a,x+c(a-1);u_v).
\tag{18}
\]

The factors in \(D_{vj}\) are positive. The degrees in \((x,a,c)\)
are \((8,6,4)\) and \((7,5,4)\). Appendix C gives a global
Bernstein coefficient-norm lower bound for each. The complete lower
coefficient vectors have seven and six entries, respectively, and
every entry is strictly positive. It follows that
\(P_{v0},P_{v1}>0\) throughout (17).

Hence both tests (6) are strictly negative for every original larger
shape as well. The shared boundary \(a=3/2\) is included in both
arguments. Equation (5) now gives \(G_\tau<0\) for every original
outer endpoint and every \(2\le\tau\le T\), proving the stated
outer-face exclusion.

## Appendix A. Four complete derivative signs

All quantities in this appendix are explicit rational functions
(3),(6),(9), with \(b=x+c(a-1)\). Write

\[
B=a+b=ac+a-c+x,\qquad Z=b-1=ac-c+x-1.
\]

Define the four finite derivative polynomials

\[
A_0=-117600\,a^6S^2B^2Z^2\,\partial_a\mathcal H_0,
\]
\[
A_1=-117600\,a^5S^2B^2Z^2\,\partial_a\mathcal H_1.
\tag{A1}
\]

At \(a=a_f(x)\), put

\[
Z_f=36cx-59c+84x-84=84(b-1),
\]
\[
B_f=36cx-59c+120x+25=84(a_f+b).
\]

Then define

\[
C_0=39200\,S^2(36x+25)^5Z_f^2B_f^2
   \partial_c\mathcal H_0(x,a_f(x),c),
\]
\[
C_1=58800\,S^2(36x+25)^4Z_f^2B_f^2
   \partial_c\mathcal H_1(x,a_f(x),c).
\tag{A2}
\]

Equations (A1)--(A2) are finite polynomial specifications by sums,
products and quotient differentiation. The logarithm contributes
exactly \(\partial_a k/k\) or \(\partial_c k/k\), so no
logarithm remains. All clearing factors in (A1)--(A2) are positive.
The respective polynomial degrees are
\((11,8,7),(10,7,6)\) in \((x,a,c)\), and
\((12,6),(11,5)\) in \((x,c)\).

### A.1. Norm rule and all alpha derivative coefficients

For (A1), substitute

\[
x=13/6+X,\quad a=6/5+A,\quad c=3/4+t,
\quad0\le A\le3/10,\quad |t|\le1/8.
\]

Write each resulting polynomial as
\(\sum p_{ijk}X^iA^jt^k\). Define the exact coefficient lower
bounds

\[
d_{ij}=p_{ij0}-\sum_{k\ge1}|p_{ijk}|8^{-k},
\qquad
\ell_i=d_{i0}-\sum_{j\ge1}(-d_{ij})_+(3/10)^j.
\tag{A3}
\]

The triangle inequality first bounds each t-polynomial below by
\(d_{ij}\); then \(A\ge0\) allows every nonnegative higher term
to be discarded, while \(A^j\le(3/10)^j\) bounds every negative
one. Therefore the original polynomial is at least
\(\sum_i\ell_iX^i\). The negative-part operation in (A3) is just
finite coefficient arithmetic, not a minimum over parameter values.

The complete exact lower polynomials are

\[
A_0\ge L_{a0}(X)/18575209267200000000,
\qquad A_1\ge L_{a1}(X)/154793410560000000.
\tag{A4}
\]

Their entire coefficient vectors follow.

| Degree | \([X^i]L_{a0}\) |
| ---: | ---: |
| 0 | 550972031497948911138729683 |
| 1 | 4277459302661251496704941627 |
| 2 | 12616524488039998570831240992 |
| 3 | 19608368710044473963616608748 |
| 4 | 18065152613576496319270717392 |
| 5 | 10485813535221911365089414720 |
| 6 | 3692553454234862687350425600 |
| 7 | 639911411866867942103040000 |
| 8 | -25496971026603357634560000 |
| 9 | -33967882069490899353600000 |
| 10 | -5997440352638730240000000 |
| 11 | -365931622563840000000000 |

| Degree | \([X^i]L_{a1}\) |
| ---: | ---: |
| 0 | 2410666441810228671116774 |
| 1 | 27046059070605083265393759 |
| 2 | 85652262941425116401002842 |
| 3 | 134365336170076062904667796 |
| 4 | 123587859492694672179312024 |
| 5 | 70541411807039775173907840 |
| 6 | 25931421982622258544844800 |
| 7 | 6005585626598940991488000 |
| 8 | 819412931743739412480000 |
| 9 | 56243711027183616000000 |
| 10 | 1219772075212800000000 |

The first vector has positive coefficients through degree seven;
the sum of the absolute values of its four negative coefficients is
less than its constant coefficient. Every coefficient of the second
vector is positive. Since \(0\le X\le7/30<1\), both lower
polynomials are strictly positive. Thus (A1) proves (11).

### A.2. All c derivative coefficients at the alpha floor

For (A2), substitute \(x=13/6+X\), \(c=3/4+t\), and write
\(C_j=\sum p_{ik}X^it^k\). For \(|t|\le1/8\),

\[
C_j\ge\sum_i\left(p_{i0}-\sum_{k\ge1}|p_{ik}|8^{-k}\right)X^i.
\tag{A5}
\]

The two complete exact lower polynomials are

\[
C_0\ge L_{c0}(X)/7077888,
\qquad C_1\ge 7L_{c1}(X)/65536.
\tag{A6}
\]

| Degree | \([X^i]L_{c0}\) |
| ---: | ---: |
| 0 | 887442072189196489812963757699 |
| 1 | 6674119465475415466469765870904 |
| 2 | 21721476975729381958394734225452 |
| 3 | 40467097071715544655976128685104 |
| 4 | 47893594626011912636554544290752 |
| 5 | 37609031451415308649967346248448 |
| 6 | 19738121766782323109096508244992 |
| 7 | 6707274771839852385116038877184 |
| 8 | 1311440120589928632162318434304 |
| 9 | 74584091236518187916417630208 |
| 10 | -25304668770269718879406129152 |
| 11 | -5705145739551251634025660416 |
| 12 | -380510236458444353691451392 |

| Degree | \([X^i]L_{c1}\) |
| ---: | ---: |
| 0 | 16919733258304669075427593 |
| 1 | 124546193508112916383138768 |
| 2 | 390596922793889813244742004 |
| 3 | 687087060013466821888990320 |
| 4 | 748588742890229997023292288 |
| 5 | 523904088933840735439748352 |
| 6 | 234148237828362177647523840 |
| 7 | 62569948454746933057376256 |
| 8 | 7606054113064603802173440 |
| 9 | -479630378464578461564928 |
| 10 | -262807970302922938122240 |
| 11 | -26345647674000754606080 |

In each vector every negative coefficient is printed, and their
absolute values have sum less than the positive constant coefficient.
All other coefficients are positive. For \(0\le X<1\), dropping
the positive higher terms and bounding \(X^i\le1\) therefore gives
\(L_{cj}(X)>0\). This proves (12).

The arrays (A4),(A6) are exact coefficient sums from (A3),(A5), using
the finite specifications (A1)--(A2). They do not assert a bound for
an unlisted family of coefficient minima.

## Appendix B. Two complete one-variable terminal polynomials

The terminal polynomials are defined in (15)--(16). Put
\(X=x-13/6\). Their complete coefficients are

\[
P_{s0}(13/6+X)=L_{s0}(X)/108,
\qquad
P_{s1}(13/6+X)=L_{s1}(X)/108.
\tag{B1}
\]

| Degree | \([X^i]L_{s0}\) |
| ---: | ---: |
| 0 | 635936847767572994000288847959 |
| 1 | 25434904611226025293653372277656 |
| 2 | 127370786402814593662482341778252 |
| 3 | 296901785754371235763791829868400 |
| 4 | 406191840111267133476953218910976 |
| 5 | 356730956460770605235371614518784 |
| 6 | 209048574420219329734302636567552 |
| 7 | 82607530917186121564882204471296 |
| 8 | 21736248666213652873126589399040 |
| 9 | 3655281394295833015131859058688 |
| 10 | 357667232042531889577860268032 |
| 11 | 15595539568326917164873285632 |
| 12 | -145246398239069123848962048 |
| 13 | -34466140182795989223997440 |
| 14 | -787078913449450908155904 |

| Degree | \([X^i]L_{s1}\) |
| ---: | ---: |
| 0 | 193147686533619489094187569 |
| 1 | 2779711876277739047943679836 |
| 2 | 10447366434948620962599815532 |
| 3 | 20225277368497739547856332864 |
| 4 | 23930569465846476680464084512 |
| 5 | 18279168490435241706044071680 |
| 6 | 9137046659400110105145059328 |
| 7 | 2961179286158794979817308160 |
| 8 | 602192261914865289134972928 |
| 9 | 71820137342985171271483392 |
| 10 | 4416820514528353349271552 |
| 11 | 109768667585017716670464 |
| 12 | 178484085839068397568 |
| 13 | -7799804672134348800 |

The first vector has just three negative coefficients, at degrees
12,13,14; the second has just one, at degree 13. In each case their
absolute values have sum smaller than the positive constant
coefficient. Every other coefficient is positive. The elementary
bound \(0\le X<1\) thus proves \(P_{s0},P_{s1}>0\), including
\(X=0\) and \(X=7/30\).

## Appendix C. The large-alpha Bernstein lower bounds

The two polynomials \(P_{v0},P_{v1}\) are specified by (18), using
(3),(6),(10),(14) and \(b=x+c(a-1)\). Their alpha degrees are
\(n_0=6\), \(n_1=5\). Set

\[
a=\frac32+\frac9{10}v,\qquad0\le v\le1.
\]

There is the exact Bernstein identity

\[
P_{vj}(x,a,c)=\sum_{i=0}^{n_j}
 \binom{n_j}{i}v^i(1-v)^{n_j-i}B_{ji}(x,c),
\tag{C1}
\]

where every coefficient polynomial has the finite product/extraction
specification

\[
B_{ji}(x,c)=\sum_{m=0}^i
 \frac{\binom im}{\binom{n_j}m}
 \left(\frac9{10}\right)^m
 [A^m]P_{vj}(x,3/2+A,c).
\tag{C2}
\]

For each of these thirteen polynomials put
\(x=137/60+s\), \(c=3/4+t\), and expand
\(B_{ji}=\sum b^{ji}_{kl}s^kt^l\).
Because \(|s|\le7/60\), \(|t|\le1/8\), each term with both
even exponents and nonnegative coefficient is nonnegative.
Discarding those terms except the constant and bounding every other
term gives the exact global lower coefficient

\[
B_{ji}\ge b^{ji}_{00}-
 \sum_{\substack{k+l>0:\ k\text{ odd or }l\text{ odd}
                         \text{ or }b^{ji}_{kl}<0}}
 |b^{ji}_{kl}|(7/60)^k8^{-l}.
\tag{C3}
\]

The complete lower bounds from (C3) are

\[
B_{0i}\ge v_{0i}/89579520000000000,
\qquad
B_{1i}\ge v_{1i}/373248000000000.
\tag{C4}
\]

Every numerator is printed:

| Degree | \(v_{0i}\) |
| ---: | ---: |
| 0 | 535389266935506353130200 |
| 1 | 953746677984456779553075 |
| 2 | 1518311233627253227345089 |
| 3 | 2248750661373025481346918 |
| 4 | 3161016632662175405497832 |
| 5 | 4241023424128984829744960 |
| 6 | 5426734509997935033625200 |

| Degree | \(v_{1i}\) |
| ---: | ---: |
| 0 | 2772381713072727125050 |
| 1 | 4769420068777414077280 |
| 2 | 6783831613248817886461 |
| 3 | 7974282915625232505642 |
| 4 | 6965889472349893066776 |
| 5 | 1022720150198148138960 |

All thirteen numbers are positive. The nonnegative Bernstein
weights in (C1) sum to one, so both original polynomials are strictly
positive on the whole domain (17). This is a single global polynomial
inequality; there is no subdivision in x, alpha, beta or duration.

The tables in all three appendices are complete finite arithmetic
identities or coefficient-norm lower polynomials from their displayed
specifications. Their mathematical use is the elementary triangle
inequality, positivity of monomials, and positivity of Bernstein
weights. No numerical sample or executable checker is used as a
proof premise.
