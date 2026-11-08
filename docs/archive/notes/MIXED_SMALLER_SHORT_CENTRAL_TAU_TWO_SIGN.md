# The central-scale, tau-two floor-weighted sign

**Replacement status, 2026-11-08:** the [new tau-two proof](../../docs/lighter-proofs/SHORT_DURATION_CENTRAL_TAU_TWO.md)
replaces the large endpoint expansion with degree-eight second derivatives
and small horizontal or slanted boundary signs. The original strict sign,
incoming norm ceiling, domain and floor-weighted-envelope caller are unchanged.

Date: 2026-11-08 UTC. Complete scalar hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 13. The proof
uses explicit rational comparisons, convexity in beta, and a finite
coefficient-norm identity. No executable sign cover is a premise.

## 1. Domain and statement

Let

\[
\frac{12}5\le x\le9,\quad
1\le\alpha\le\frac{5x+4}{12},\quad
x\le\beta\le x+\frac{x(7x+1)(\alpha-1)}{R},
\qquad R=4x^2+11x+1.
\tag{1}
\]

Set S=1+x, H=x(x+2)+alpha^2,

\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad \lambda=S^2/H,\quad d=D/H,\quad q=\alpha^2/H,
\quad r_A=\alpha/(\alpha+\beta).
\]

For the norm ceiling used in this note put

\[
V_g=\frac{2(x-1)^2}{S(35x+13)},\qquad
\widehat u=\frac34+V_g\frac{x-1+(\beta-x)/8}{\beta-1}.
\tag{2}
\]

Define

\[
E=S(\widehat u-1)+\frac3S-\frac1{S^2},\quad
w=\lambda^2(1-S^{-1}+S^{-2})+d^2\widehat u-d\lambda E,
\quad E_L=2d\widehat u-\lambda E.
\]

Then the following rational quantity is strictly negative throughout
(1):

\[
\boxed{\mathcal G_2
 =\frac52w+\frac{\widehat u-1}{r_A}+r_A-q-E_L
                  +\frac{5q}{2r_A}-\frac{151}{72}<0.}
\tag{3}
\]

This is an upper bound for the actual floor-weighted expression on
the central-scale tau=2 face. Indeed the elementary tangent estimate

\[
\log y\le\frac54y-1-\log(5/4)
          <\frac54y-\frac{11}9
\tag{4}
\]

follows from log(5/4)>2/9, obtained by integrating
2/(1-z^2)>2 from 0 to 1/9. Inserting y=2q/r_A into
G=R_2+(w-3/4)/2 gives exactly (3) as its rational majorant.
The estimate (4) is valid for every y>0, including y>1.

For an actual central scale, q<=1/7 is equivalent to
alpha^2<=x(x+2)/6. The enlarged linear bound in (1) follows because

\[
\left(\frac{5x+4}{12}\right)^2-\frac{x(x+2)}6
 =\frac{(x-4)^2}{144}\ge0.
\tag{5}
\]

The beta bound in (1) is the established strong short-order bound.
No upper short-order bound is needed in this scalar lemma.

## 2. Why the simplified incoming ceiling is legitimate

Write b=beta-x. The incoming estimate already proved gives

\[
u\le\frac34+
 \frac{(x-1)V_g+b^3/(48x^2)}{x-1+b}.
\]

To bound this by (2), it suffices that

\[
b^2S(35x+13)\le12x^2(x-1)^2.
\tag{6}
\]

The domain (1) gives

\[
b\le\frac{x(7x+1)(5x-8)}{12R}.
\]

After this substitution, (6) follows from the positivity of

\[
\begin{aligned}
P_t(x)&=1728(x-1)^2R^2
 -(7x+1)^2(5x-8)^2S(35x+13)\\
 &=x^3\{x^2(162918-15227x)-335862\}
          +30432x^4+80667x^2+20880x+896.
\end{aligned}
\tag{7}
\]

The bracket is positive on the entire range. On [12/5,4], use
x^2>=144/25 and 162918-15227x>=102010; their product exceeds
335862. On [4,9], use x^2>=16 and 162918-15227x>=25875, which
bounds that bracket below by 78138. This proves (6).

The incoming upper substitution is a proved scalar comparison for G.
The coefficient formula in
[MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md)
also applies when tau=2 has passed T=2 during scale comparison:
for x>=5/2, d<=2/7; for 12/5<=x<=5/2, d<=51/175.
Thus 2d<1 for every q<=1/7, regardless of tau<=T. Inserting this
in the same coefficient estimate proves G_u>0 at tau=2. Consequently
raising the original incoming norm to (2) is legitimate at the actual
central face. The larger domain (1) is used only for the rational sign
(3), after that comparison has been justified.

## 3. Strict convexity reduces beta to its two endpoints

Put h=x-alpha>0 and

\[
u_\infty=\frac34+\frac{V_g}8,
\qquad J=\frac{7(x-1)V_g}8>0.
\]

Then widehat u=u_infinity+J/(beta-1). As a rational function of beta,
(3) has the form

\[
\mathcal G_2=P_2\beta^2+P_1\beta+P_0
       +\frac{J A_*}{\beta-1}+\frac\alpha{\alpha+\beta},
\qquad P_2=\frac{10u_\infty h^2}{H^2}>0.
\tag{8}
\]

Here P_1,P_0 depend only on x,alpha, and the residue A_* is

\[
A_*=1+\alpha^{-1}+\lambda S-2d_1
          +\frac52d_1(d_1-\lambda S),
\qquad d_1=\frac{(\alpha+1)^2}{H}.
\tag{9}
\]

For (8), collect the polynomial and the two simple-pole parts of
(3); equivalently A_* is its coefficient of u evaluated at beta=1.
The displayed leading coefficient and both residues determine its
second derivative, so no formula for P_1 or P_0 is needed.

The quantity d_1 increases with alpha on the domain. At the upper
alpha bound in (1), it is

\[
\frac{(5x+16)^2}{169x^2+328x+16}.
\]

It is at most 4/9 for x>=12/5, since
451x^2-128x-2240>0 there. For x>=3 it is at most 2/5, since
213x^2-144x-1248>0 there. Both quadratics increase on their stated
intervals and have positive values at the left endpoints.

If d_1<=2/5, (9) gives A_*>1-4/5>0. Otherwise x<3,
2/5<d_1<=4/9, and lambda*S<4; hence

\[
A_*>1-\frac49-\frac89+\frac25=\frac1{15}>0.
\]

Therefore

\[
\frac12\partial_\beta^2\mathcal G_2
 =P_2+\frac{J A_*}{(\beta-1)^3}
                  +\frac\alpha{(\alpha+\beta)^3}>0.
\tag{10}
\]

A convex function is at most the chord between its endpoint values.
It remains to prove (3) at beta=x and at the upper endpoint in (1).

## 4. A compact exact polynomial for those endpoints

The following factored definition supplies the entire polynomial
whose sign is used below. Set M=35x+13 and

\[
K_0=SM(\beta-1),\quad K=4K_0,
\quad U=3K_0+(x-1)^2(\beta+7x-8),
\]
\[
B=S^3(U-K)+(3S-1)K,\qquad
W=KS^2(S^2-S+1)+D^2U-DB,\qquad Z=2DU-B.
\]

Thus widehat u=U/K, w=W/(KH^2), and E_L=Z/(KH).
Define

\[
\begin{aligned}
N={}&45\alpha(\alpha+\beta)W
 +18(\alpha+\beta)^2H^2(U-K)+18\alpha^2KH^2\\
&-18\alpha^3(\alpha+\beta)KH
 -18\alpha(\alpha+\beta)HZ
 +45\alpha^2(\alpha+\beta)^2KH\\
&-151\alpha(\alpha+\beta)K_0H^2.
\end{aligned}
\tag{11}
\]

Direct multiplication of (3) gives the identity

\[
\mathcal G_2=
\frac{N}{72\alpha(\alpha+\beta)(\beta-1)S M H^2}.
\tag{12}
\]

All factors of this denominator are positive.
For epsilon in {0,1}, introduce

\[
x=\frac{12+X}5,\quad
\alpha=1+\frac{X+4}{12}A,\quad
\beta=x+\epsilon\frac{x(7x+1)(\alpha-1)}R,
\quad X\ge0,\quad0\le A\le1.
\tag{13}
\]

The original x range is contained in this parameter domain.
Use the positive normalization

\[
\mathcal P_\epsilon(X,A)
 =-2^{14}3^7 5^{17}R^4N(x,\alpha,\beta)
 =\sum_{i=0}^{18}\sum_{j=0}^7 p_{ij}^{\epsilon}X^iA^j.
\tag{14}
\]

Equations (11), (13), and (14) are an explicit coefficient-extraction
rule: p_ij^epsilon is the coefficient of X^i A^j in the displayed
finite product sum. Clearing R^4 makes (14) a polynomial. There is no
interpolation or sampled sign in this definition.

## 5. Four quadratic rows and two elementary norm absorptions

Let [z]_- = max(0,-z). The following small rational bounds are direct
coefficient identities and inequalities from (11)--(14). They are
listed by their complete groups; the same bounds hold for both values
of epsilon.

First C_i:=p_i0^epsilon is independent of epsilon. The polynomial of
these constants factors as

\[
\begin{aligned}
\sum_i C_iX^i={}&35831808(X+7)(X+17)(4X^2+151X+1261)^4\,Q(X),\\
Q(X)={}&3402X^7+215083X^6+5540378X^5+74222735X^4\\
&+545738670X^3+2123035969X^2+3768980206X+1708202501.
\end{aligned}
\tag{15}
\]

In particular C_i>0 for 0<=i<=17, and C_18=0.
For the first four rows the complete bounds are:

| i | lower bound for p_i1/C_i | lower bound for (p_i2-sum_{j=3}^7 [p_ij]_-) / C_i |
|---|---:|---:|
| 0 | -13/5 | 5/2 |
| 1 | -3/2 | 5/4 |
| 2 | -21/20 | 4/5 |
| 3 | -4/5 | 1/2 |

Because A^j<=A^2 for j>=3, each row is bounded below by C_i
times its listed quadratic 1-b_i A+c_i A^2. These quadratics are
strictly positive: their global minima are respectively
81/250, 11/20, 839/1280, and 17/25.

For the middle rows define

\[
\nu_i=\max_{\epsilon=0,1}
       \frac{\sum_{j=1}^7[p_{ij}^{\epsilon}]_-}{C_i}.
\]

The complete bounds are:

| i | upper bound for nu_i | i | upper bound for nu_i |
|---|---:|---|---:|
| 4 | 49/50 | 10 | 3/8 |
| 5 | 2/3 | 11 | 2/5 |
| 6 | 12/25 | 12 | 2/5 |
| 7 | 3/7 | 13 | 7/16 |
| 8 | 19/50 | 14 | 4/7 |
| 9 | 11/30 | 15 | 19/20 |

All upper bounds are less than one. Since 0<=A<=1, every middle
row is therefore at least C_i(1-nu_i)>0. Positive nonconstant
coefficients may simply be discarded in this estimate.

Finally the linear coefficients in the three last rows are

\[
\begin{aligned}
p_{16,1}^{\epsilon}
 &=477757440(118752300+31078423\epsilon),\\
p_{17,1}^{\epsilon}
 &=382205952(1371206+185535\epsilon),\\
p_{18,1}^{\epsilon}&=2229025112064.
\end{aligned}
\tag{16}
\]

They are positive. The complete remaining norm bounds are

\[
\max_\epsilon\frac{\sum_{j=2}^7[p_{ij}^{\epsilon}]_-}
                         {p_{i1}^{\epsilon}}
 \le\begin{cases}
 3/10,&i=16,\\
 9/20,&i=17,\\
 2/3,&i=18.
 \end{cases}
\tag{17}
\]

Use A^j<=A for j>=2. Each last row is nonnegative, and the first
two are strictly positive because their constants C_16,C_17 are
positive.

This proves every coefficient row in (14) is nonnegative on [0,1],
with the i=0 row strictly positive even at the endpoints A=0,1.
Consequently P_epsilon>0 for every X>=0 and 0<=A<=1. Equations
(12)--(14) prove the two endpoint values of G_2 are strictly negative.
The convexity argument (10) proves (3) on the entire beta interval.

The norm tables are finite rational arithmetic attached to the exact
product identity (11). They replace a long coefficient listing by
three explicit elementary inequalities, A^j<=A^2, A^j<=1, and
A^j<=A; their derivation and use do not require a program or a cover
of the parameter domain.
