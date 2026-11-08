# The full and eight-ninths duration faces at central scale

**Replacement status, 2026-11-08:** the [new duration-face proofs](../../docs/lighter-proofs/SHORT_DURATION_CENTRAL_UPPER_FACES.md)
replace the large endpoint generating-polynomial argument for both tests.
The original strict signs, incoming norm ceiling, domain and caller are
unchanged; the elementary beta convexity is retained explicitly.

Date: 2026-11-08 UTC. Complete hand sign, accepted in the
[independent central-duration review](MIXED_SMALLER_SHORT_CENTRAL_DURATION_AUDIT.md),
for two of the central-scale tests. The tau=2 face and the outer-scale tests are
handled separately.

## 1. The two rational expressions

Throughout this note assume
\[
\frac{12}{5}\le x\le9,\qquad
1\le\alpha\le\frac{5x+4}{12},\qquad
x\le\beta\le x+
 \frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{1}
\]
Put
\[
S=x+1,\quad K=x^2+2x+\alpha^2,\quad B=\alpha+\beta,
\quad R=4x^2+11x+1,\quad L=35x+13,
\]
\[
v_0=\frac{2(x-1)^2}{SL},\qquad
u=\frac34+v_0\frac{x-1+(\beta-x)/8}{\beta-1}.
\tag{2}
\]
The variable u in this note is exactly the rational function (2).
It is the upper incoming-norm comparison used in the central-face
reduction; the sign proved here is a scalar statement on (1).

Use the central-scale quantities
\[
q=\frac{\alpha^2}{K},\quad \lambda=\frac{S^2}{K},\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad d=D/K,
\]
\[
v=1-S^{-1}+S^{-2},\quad
E=S(u-1)+3/S-S^{-2},
\]
\[
w=\lambda^2v+d^2u-d\lambda E,\quad
E_L=2du-\lambda E,\quad r_A=\alpha/B,\quad T=r_A/q.
\tag{3}
\]
For the two pairs
\[
(c,\ell_c)=(1,0),\qquad(8/9,-1/9),
\]
define
\[
\begin{aligned}
G_c={}&(w-1)cT+(cT)^{-1}
 +(u-1)/r_A+r_A+1-q-E_L+\ell_c
 +\frac12(w-3/4).
\end{aligned}
\tag{4}
\]
Then
\[
\boxed{G_1<0,\qquad G_{8/9}<0\quad\hbox{throughout (1)}.}
\tag{5}
\]
For c=1 the logarithm in the original residual is exactly zero.
For c=8/9, the elementary inequality log(c)<=c-1 justifies the
upper value ell_c=-1/9 in (4). No restriction cT>=2 is used in
this scalar theorem.

## 2. Convexity reduces beta to its two endpoints

This section applies to either c in (4); in fact it works for every
fixed 0<c<=1 and every constant ell_c.

Write h=x-alpha>0 and
\[
u=u_\infty+\frac{J}{\beta-1},\qquad
u_\infty=\frac34+\frac{v_0}{8},\quad
J=\frac78(x-1)v_0>0.
\tag{6}
\]
At fixed x,alpha, the rational expression (4) has the partial-fraction
form
\[
G_c=P_2\beta^2+P_1\beta+P_0
       +\frac{P_-}{\beta-1}+\frac{P_+}{\alpha+\beta},
\qquad P_2=\frac{2h^2u_\infty}{K^2}>0.
\tag{7}
\]
The following residue bounds suffice; the unused coefficients P_1
and P_0 need not be expanded.

### 2.1. The pole at beta=-alpha has positive residue

At this algebraic evaluation point let
\[
M=S^2-h^2>0,\qquad d_N=M/K.
\]
The continued value of (6) satisfies
\[
u_N=u_\infty-J/(\alpha+1)\le\frac34,
\]
because 7(x-1)>=alpha+1 follows from alpha<=x and x>=12/5.
Also the derivative of the transported norm with respect to u is
\(d_N(d_N-\lambda S)<0\). Thus its value w_N is at least its
value at u=3/4.

The explicit identity
\[
\begin{aligned}
4K^2\{w_N|_{u=3/4}-1+q\}={}&
 \alpha(\alpha-1)(\alpha+1)(\alpha^2+4\alpha-1)\\
&+h(\alpha+1)(5\alpha-1)(\alpha^2+4\alpha-1)\\
&+h^2(9\alpha^3+35\alpha^2+15\alpha-3)\\
&+h^3(7\alpha^2+14\alpha+3)+2(\alpha+1)h^4
\end{aligned}
\tag{8}
\]
is strictly positive for alpha>=1,h>0. The pole residue in (7) is
\[
P_+=\frac{cK}{\alpha}(w_N-1)+\alpha
       >\alpha(1-c)\ge0.
\tag{9}
\]

### 2.2. A uniform lower bound for the other residue

Put d_1=(alpha+1)^2/K, the continued value of d at beta=1.
The coefficient of u in G_1 at beta=1 simplifies to
\[
A_1^{\rm res}=-\frac{\lambda h}{\alpha}
                 +\frac12d_1(d_1-\lambda S)<0.
\tag{10}
\]
For 0<c<=1, the corresponding coefficient A_c^res is at least
A_1^res: its difference from (10) is
\[
(1-c)\frac{K}{\alpha(\alpha+1)}d_1(\lambda S-d_1)\ge0.
\]
Consequently P_-=J A_c^res>=J A_1^res.

Differentiate (7) twice, apply (9), and use beta>=x. Since (10)
is negative,
\[
\frac12(G_c)_{\beta\beta}
\ge P_2+\frac{J A_1^{\rm res}}{(x-1)^3}
\]
\[
\ge\frac1{K^2}\left\{
\frac32h^2-\frac{hK}{16\alpha}
                    -\frac{S(\alpha+1)^2}{32}\right\}.
\tag{11}
\]
Here u_infinity>=3/4, J/(x-1)^3=7/(4SL), and
S/L<=1/28 were used. In the last negative term, discarding
the positive (alpha+1)^4 term only weakens the lower bound.

The central alpha bound in (1) gives alpha<=5x/9. On
1<=alpha<=5x/9 and 12/5<=x<=9,
\[
\frac{K}{\alpha h}\le\frac{25}{2},\qquad
\frac{S(\alpha+1)^2}{h^2}\le\frac{45}{2}.
\tag{12}
\]
For the first inequality, use
\[
\frac{K}{\alpha h}
=\frac{x+2}{\alpha}+\frac{2x+2}{x-\alpha}-1.
\]
It is convex in alpha, so its maximum occurs at alpha=1 or
alpha=5x/9. Those two values are
\(x+3+4/(x-1)\) and \(53/10+81/(10x)\), respectively.
The first is convex in x with endpoint values 289/35 and 25/2;
the second is at most 347/40.

The second expression in (12) increases with alpha. At alpha=5x/9
it is
\[
\frac{25x+115+171/x+81/x^2}{16},
\]
a convex function of x whose endpoint values are 4165/256 and 45/2.
This proves (12). Inserting these two bounds into (11) yields
\[
\boxed{\frac12(G_c)_{\beta\beta}
       \ge\frac{h^2}{64K^2}>0.}
\tag{13}
\]
Therefore it suffices to prove (5) at
\[
\beta=x,\qquad
\beta=x+\frac{x(7x+1)(\alpha-1)}R.
\tag{14}
\]

## 3. An explicit generating polynomial for the endpoint signs

The remaining arithmetic is organized by coefficients in two
nonnegative parameters. All polynomials and all bounds needed for
that arithmetic are specified below.

Define the following polynomials in x,alpha,beta:
\[
V=4SL(\beta-1),\quad
U=3SL(\beta-1)+(x-1)^2(\beta+7x-8),
\]
\[
E_N=S^3(U-V)+(3S-1)V,
\]
\[
W=S^2(S^2-S+1)V+D^2U-DE_N,
\qquad Z=2DU-E_N.
\tag{15}
\]
Thus u=U/V, w=W/(K^2V), and E_L=Z/(KV).
The cleared negative numerator is the explicit polynomial
\[
\begin{aligned}
N_c:=-\{&2cK(W-K^2V)+(2/c)\alpha^2B^2VK
       +2B^2K^2(U-V)+2\alpha^2VK^2\\
 &+(5/4+2\ell_c)\alpha BVK^2-2\alpha^3BVK
       -2\alpha BKZ+\alpha BW\}.
\end{aligned}
\tag{16}
\]
Direct multiplication of (4) shows
\[
\boxed{N_c=-2\alpha BVK^2G_c.}
\tag{17}
\]
The factor multiplying -G_c is positive on (1).

Introduce X>=0, A in [0,1], and F in [0,1] by
\[
x=\frac{12+X}{5},\qquad
\alpha=1+\frac{X+4}{12}A,
\qquad
\beta=x+\frac{x(7x+1)(\alpha-1)}R F.
\tag{18}
\]
The actual x<=9 restriction says X<=33; the coefficient argument
below works for all X>=0. The two endpoints (14) are F=0 and F=1.

Define
\[
P_c(X,A,F)=\left.R^4N_c\right|_{(18)}.
\tag{19}
\]
It is a polynomial, of degrees at most 18,7,4 in X,A,F, respectively.
For explicit coefficient extraction without rational-function
division, write
\(N_c=\sum n_{ijk}^{(c)}x^i\alpha^j\beta^k\), where k<=4.
Then (19) is equivalently the finite identity
\[
P_c=\left.\sum n_{ijk}^{(c)}x^i(1+mA)^j
 [xR+x(7x+1)mAF]^kR^{4-k}\right|_{x=(12+X)/5},
\quad m=\frac{5x-8}{12}.
\tag{20}
\]
Equations (15)--(16) and the ordinary binomial theorem determine
every coefficient in (20).

For e=0,1, write
\[
P_c(X,A,e)=\sum_{i=0}^{18}\sum_{j=0}^7
                  p_{ij}^{c,e}X^iA^j,
\qquad C_i^c=p_{i0}^{c,e}.
\tag{21}
\]
The last quantity is independent of e, because A=0 gives alpha=1
and beta=x for either endpoint.

## 4. Positive constant coefficients and a small norm table

Every C_i^c is strictly positive. Here are explicit factorizations
which also fix the normalization used in (21). Before the x
substitution in (18),
\[
P_1(X,0,e)=(x-1)^3SR^4Q_1(x),
\]
\[
P_{8/9}(X,0,e)=\frac19(x-1)SR^4Q_8(x),
\tag{22}
\]
where their shifted forms are
\[
\begin{aligned}
5^6Q_1((12+X)/5)={}&108X^6+7506X^5+206755X^4
 +2844330X^3\\
&+19943420X^2+62065636X+45865557,
\end{aligned}
\tag{23}
\]
\[
\begin{aligned}
5^8Q_8((12+X)/5)={}&864X^8+72954X^7+2594763X^6
 +50555967X^5\\
&+585685830X^4+4073454088X^3
 +16130710023X^2\\
&+30777677951X+15224862024.
\end{aligned}
\tag{24}
\]
The other factors in (22) also have strictly positive coefficients
after this substitution; for example
\(25R=4X^2+151X+1261\). This proves C_i^c>0 for every index in (21).

For a real number y let [y]_-:=max(0,-y). Define the negative
coefficient norms
\[
\nu_i^{c,e}=\frac1{C_i^c}\sum_{j=1}^7[p_{ij}^{c,e}]_-.
\tag{25}
\]
The following table consists of exact rational bounds, with the
displayed integer entries divided by 1000. In its M column,
\[
\max\{\nu_i^{1,0},\nu_i^{1,1},\nu_i^{8/9,0}\}\le M_i/1000.
\]
In its N column, \(\nu_i^{8/9,1}\le N_i/1000\). The first two
entries of the latter column are replaced by the quadratic estimates
(27) below.

| i | M_i | N_i |
|---:|---:|---:|
| 0 | 492 | — |
| 1 | 448 | — |
| 2 | 394 | 840 |
| 3 | 325 | 618 |
| 4 | 250 | 446 |
| 5 | 165 | 301 |
| 6 | 68 | 162 |
| 7 | 50 | 37 |
| 8 | 44 | 37 |
| 9 | 40 | 36 |
| 10 | 37 | 34 |
| 11 | 37 | 31 |
| 12 | 39 | 28 |
| 13 | 43 | 25 |
| 14 | 50 | 25 |
| 15 | 58 | 30 |
| 16 | 69 | 56 |
| 17 | 98 | 105 |
| 18 | 153 | 162 |

\[
\tag{26}
\]

For the exceptional two rows put
\[
\lambda_i=\frac{p_{i1}^{8/9,1}}{C_i^{8/9}},\qquad
\mu_i=\frac{p_{i2}^{8/9,1}
                  -\sum_{j=3}^7[p_{ij}^{8/9,1}]_-}{C_i^{8/9}}.
\]
The corresponding exact bounds are
\[
\lambda_0\ge-2,\quad\mu_0\ge\frac65,
\qquad
\lambda_1\ge-\frac87,\quad\mu_1\ge\frac12.
\tag{27}
\]

For clarity, (26)--(27) are coefficient inequalities for the single
explicit polynomial identity (20), not sampled bounds on variables.
For instance each M entry means
\(1000\sum_{j=1}^7[p_{ij}^{c,e}]_-\le M_iC_i^c\)
for the indicated three pairs. Each N entry has the same meaning
for the fourth pair. They can be checked by expanding the displayed
factors in (15)--(16), applying the binomial identity (20), and
multiplying positive integer denominators. These definitions and
bounds specify the entire arithmetic assertion used here; no
unpublished coefficient list or executable check is a premise.

## 5. The norm bounds prove the four endpoint signs

Fix one of the three pairs covered by the M column. Since 0<=A<=1,
\[
\frac1{C_i^c}\sum_{j=0}^7p_{ij}^{c,e}A^j
\ge1-\nu_i^{c,e}
\ge1-\frac{492}{1000}>0.
\tag{28}
\]
For the pair c=8/9,e=1, the same argument applies to i>=2,
using N_i<=840 instead.

For i=0,1 of that last pair, A^j<=A^2 when j>=3. Discarding
positive higher terms and using (27) therefore gives, respectively,
\[
\frac1{C_0^{8/9}}\sum_{j=0}^7p_{0j}^{8/9,1}A^j
\ge1-2A+\frac65A^2
=\frac65(A-5/6)^2+\frac16>0,
\tag{29}
\]
\[
\frac1{C_1^{8/9}}\sum_{j=0}^7p_{1j}^{8/9,1}A^j
\ge1-\frac87A+\frac12A^2
=\frac12(A-8/7)^2+\frac{17}{49}>0.
\tag{30}
\]
Thus each coefficient polynomial of X in (21) is strictly positive
on A in [0,1]. Since X>=0, P_c(X,A,e)>0 for all four pairs.
Equations (17)--(19) prove G_c<0 at both beta endpoints (14).
The strict convexity (13) proves (5) throughout the whole interval.

These are signs for the two explicit central-scale comparison
expressions. Their application to an actual bridge uses the separate
root/floor envelope and scale reductions; this note does not change
the actual Casimir or completion cost.
