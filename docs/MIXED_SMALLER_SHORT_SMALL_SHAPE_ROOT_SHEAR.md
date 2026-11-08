# A root forces a negative shear on the small short-shape domain

Date: 2026-11-08 UTC. Conditional scalar hand lemma. This note does not
supply the ratio or displacement restrictions in its hypotheses. The
arithmetic is organized as two explicit low-degree polynomial
majorants, not a subdivision cover or a list of coefficient minima.

## 1. Statement and actual-to-scalar scope

Suppose an actual smaller-short bridge has
\[
2\le x\le13/6,\qquad
0\le\delta:=\beta/x-1\le1/19,\qquad
\alpha=1+\eta\delta,\quad13/5\le\eta\le3.
\tag{1}
\]
At delta=0, the last formula means alpha=1. Put
\[
S=x+1,\quad B=\alpha+\beta,\quad
K_x=x^2+x+1,\quad K_A=\alpha^2+\alpha\beta+\beta^2,
\]
\[
r=\alpha/B,\quad U_1=K_x/S^2,\quad
A=\frac{(\beta x-\alpha)(\alpha x-\beta)}{S^2K_A},
\quad R=(x-1)/S.
\]
Use the actual outer scale q=rho_A and the actual physical shear h.
If the actual outer arc has a descending root in its required interval,
then
\[
\boxed{q>\frac{29}{30}
          \frac{\alpha^2}{x(x+2)+\alpha^2},\qquad
       \sqrt3\,hR+\frac{13}{3}A<0.}
\tag{2}
\]
Consequently h<0 and
\[
\boxed{-hR>\frac52A.}\tag{3}
\]
The last comparison follows from 676>675. At A=0, the strict negative
shear already proves (3).

The root premise is used exactly as in the
[outer-envelope theorem](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md): slightly
before the actual descending root, there is p with
\[
2q<p<r,\qquad \mathcal R(u;p,q)>0.
\tag{4}
\]
Here R is the proved scalar envelope residual, not a new physical
bridge. Neither the Casimir nor a physical norm ceiling is transferred
to a scalar comparison point.

## 2. A particularly simple incoming majorant

The [incoming secant bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
implies, on (1),
\[
u\le U_0(x):=\frac34+
 \frac{2(x-1)^2}{(x+1)(35x+13)}.
\tag{5}
\]
Indeed, after the secant bound is multiplied by beta-1, this follows
from
\[
(\beta-x)^2S(35x+13)\le96x^2(x-1)^2.
\]
The left side is at most 300x^2/361, whereas the right side is at least
96x^2. Define t=x-2 and
\[
\widehat u=\frac{755}{996}+\frac{t}{100}.
\]
The exact difference is
\[
\widehat u-U_0(x)
 =\frac{t(8715t^2+4012t+1)}
 {24900(x+1)(35x+13)}\ge0.
\tag{6}
\]
Moreover 3/4<uhat<=12611/16600<19/25.
The [incoming monotonicity lemma](MIXED_SMALLER_SHORT_ROOT_INCOMING_MONOTONICITY.md)
therefore permits u to be raised to uhat in (4) whenever q<=1/7.

For the rest of the root argument, evaluate the following quantities
at uhat:
\[
\epsilon=1-\alpha^{-2},\quad n=S/\alpha^2,\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad g=D/\alpha^2,
\]
\[
E_0=S(\widehat u-1)+S^{-1},
\]
\[
A_1=2\epsilon+n+gE_0,
\quad
A_2=\epsilon^2+\epsilon n+n^2+g^2\widehat u
               +g\epsilon E_0-g(2S-1)/\alpha^2,
\]
\[
A_3=2g\widehat u+\epsilon E_0-(2S-1)/\alpha^2.
\tag{7}
\]
Then
\[
\mathcal R(\widehat u;p,q)
 =E_0+\frac{\widehat u-1}{r}+r+1-pA_1+\log(p/r)
        +q(pA_2+p^{-1}-1-A_3).
\tag{8}
\]

## 3. Positivity of A2 and the two logarithm tangents

This section also applies on the enlarged scalar shape domain
\[
2\le x\le13/6,\quad1\le\alpha\le22/19,
\quad x\left(1+\frac{\alpha-1}{3}\right)
 \le\beta\le
x\left(1+\frac{5(\alpha-1)}{13}\right).
\tag{9}
\]
It contains (1). Set H=-E0, a=alpha^{-2}, and
\[
\mathcal A=\epsilon^2+\epsilon Sa+S^2a^2,
\quad K=\epsilon H+(2S-1)a,
\quad \overline H=S/4-S^{-1},
\quad\overline K=\epsilon\overline H+(2S-1)a.
\]
Here H>0, K>0, and
A2=mathcal A-gK+uhat*g^2. If g<=0 it is positive immediately.
Otherwise completing the square gives
\[
A_2\ge\mathcal A-g\overline K+\tfrac34g^2
       \ge\mathcal A-\overline K^2/3>0.
\tag{10}
\]
For the last sign put z=(S-2)^2a<=49/36<2 and use the identity
\[
\overline K^2-3\mathcal A
 =\frac{S^4-56S^2+16+2(7S^2-4)z+z^2}{16S^2}
 <\frac{S^4-28S^2+4}{16S^2}<0.
\]
Since S<5, the last numerator is at most 4-3S^2.

The elementary bounds we use are
\[
\log y\le y-1,\qquad
\log y<\frac54y-\frac{1223}{1000}\quad(y>0).
\tag{11}
\]
Indeed log(5/4)>2(1/9+1/(3*9^3))=488/2187>223/1000.
Concavity at y=4/5 proves the second bound. The lines in (11)
intersect at
\[
\theta=223/250.
\]

Put
\[
C=x(x+2)+\alpha^2,\qquad q_b=\frac{29\alpha^2}{30C}.
\tag{12}
\]
Throughout (9), qc=alpha^2/C<=121/843, hence
qb<=3509/25290<1/7. Also 2qb<r: it is enough that
alpha^2+2alpha*beta<x(x+2), and the left side is at most
\[
\frac{484}{361}+2\frac{22}{19}\frac{13}{6}
 \left(1+\frac{15}{247}\right)<8.
\]

## 4. Only three positive-scale faces remain

Assume for contradiction that q<=qb. The coefficient comparison in
Section 2 gives R(uhat;p,q)>0 at the p in (4).
For fixed p the expression (8) is affine in q on
0<=q<=min(qb,p/2). Therefore it suffices to bound q=0, q=qb,
and q=p/2.

At q=0, use the first tangent in (11), leaving an affine function of
p. Its endpoints are p=0 and p=r. On the enlarged domain (9),
\[
6/19\le r\le11/31,\quad H<1/2,\quad g<9/4,\quad A_1>3/2.
\tag{13}
\]
For g, use beta>=x and
\[
g\le1+(4\alpha-3)/\alpha^2\le1073/484<9/4.
\]
Then A1=2+(S-2)/alpha^2-gH>2+2/3-9/8>3/2.
Since H>=29/75,
\[
E_0+(\widehat u-1)/r+r
 \le-29/75-186/275+11/31=-18112/25575<-7/10.
\tag{14}
\]
The two q=0 values are therefore below -7/10 and
-7/10+1-9/19=-33/190.

On q=qb, the smaller of the two tangent majorants is convex in p on
each of its two intervals. Its only nonlinear p term is qb/p.
The three endpoint tests are thus
\[
J_2=E_0+(\widehat u-1)/r+r+277/1000
 +q_b(5/(2r)-2A_1-1-A_3)+2q_b^2A_2,
\tag{15}
\]
\[
J_\tau=E_0+(\widehat u-1)/r+r+\tau-\tau rA_1
 +q_b(\tau rA_2+(\tau r)^{-1}-1-A_3),
 \quad\tau=\theta,1.
\tag{16}
\]
An intermediate endpoint outside [2qb,r] is simply omitted. Formula
(15) uses the second tangent whether or not it is the smaller one.
On the boundary p=2q that same tangent gives a quadratic in q with
leading coefficient 2A2>0. Its qb value is (15), and its q=0
continuous extension is bounded above by -7/10+277/1000<0.
Thus (15)--(16) being negative proves the contradiction.

## 5. Convexity removes beta

All three functions (15)--(16) are strictly convex in beta at fixed
x,alpha on (9). For J2, its polynomial part has beta-squared
coefficient
\[
8q_b^2\widehat u(x-\alpha)^2/\alpha^4>0,
\]
and its only pole is alpha/(alpha+beta), with positive residue.
For Jtau, polynomial division leaves an affine function plus the pole
\[
\frac{\alpha}{\alpha+\beta}
 \{1-\tau A_1(-\alpha)+q_b\tau A_2(-\alpha)\}.
\tag{17}
\]
The notation means evaluate the polynomials A1,A2 in beta at -alpha;
it does not describe geometry. The residue is positive. The
completed-square proof of A2>0 holds for every value of g, including
this substitution. Moreover A1(-alpha)<1: here
\[
D(-\alpha)=S^2-(x-\alpha)^2\ge275/36,
\]
so DH>=(275/36)(29/75)>8/3>alpha^2+S-2. This is exactly the
required A1 inequality. Since 0<tau<=1, (17) is strictly positive.

It remains to check the two beta endpoints
\[
\alpha=1+c,\quad\beta=x(1+vc),\quad
0\le c\le3/19,\qquad v\in\{1/3,5/13\}.
\tag{18}
\]
These are six bivariate polynomial signs, with a simple common
majorant given next.

## 6. The six explicit numerators

For (18) and t=x-2 define the following polynomials. All quantities
on the right are polynomial in t,c with rational coefficients:
\[
D_u=24900S,\quad N_u=(18875+249t)S,
\quad E=S(N_u-D_u)+24900,
\]
\[
N_1=(2\alpha^2+S-2)D_u+DE,
\]
\[
N_2=((\alpha^2-1)^2+(\alpha^2-1)S+S^2)D_u
 +D^2N_u+D(\alpha^2-1)E-D(2S-1)D_u,
\]
\[
N_3=2DN_u+(\alpha^2-1)E-(2S-1)D_u.
\tag{19}
\]
Thus E0=E/Du and Ai=Ni/(alpha^{2i}Du) for i=1,2;
A3=N3/(alpha^2Du). Put lambda=29/30 and
\[
N_0=1000\alpha BE+1000B^2(N_u-D_u)
       +1000\alpha^2D_u+277\alpha BD_u,
\]
\[
P_{2,v}=-\{2N_0C^2
 +1000\lambda[5\alpha^2B^2D_uC
      -2\alpha BC(2N_1+N_3+\alpha^2D_u)]
 +4000\lambda^2\alpha BN_2\},
\tag{20}
\]
\[
P_{\tau,v}=-\{\alpha BCE+B^2C(N_u-D_u)+\alpha^2CD_u
 +\tau\alpha BCD_u-\tau CN_1
 +\lambda[\tau N_2+\alpha^2BD_u(B/\tau-\alpha)
                  -\alpha BN_3]\}.
\tag{21}
\]
Their exact relation to (15)--(16) is
\[
J_2=-\frac{P_{2,v}}{2000\alpha BD_uC^2},\qquad
J_\tau=-\frac{P_{\tau,v}}{\alpha BD_uC}.
\tag{22}
\]
Normalize each P by its positive value at t=c=0:
\[
p_2=999322600,\qquad p_\theta=242899889/5575,
\qquad p_1=49400,
\quad \widehat P_{j,v}=P_{j,v}/p_j.
\tag{23}
\]
The following is the entire polynomial bounding argument. In it,
F \succeq G means that every coefficient of F-G in t,c is
nonnegative; it does not denote a sampled or interval comparison.

Define
\[
\begin{aligned}
N_2^+={}&c(3/2+55t/2+23t^2/2+t^7/10)\\
 &+c^2(167t/5+373t^2/5+53t^3/2+t^7/10)\\
 &+c^3(183t^2/10+253t^3/10+29t^4/5+t^5/10+t^7/10)\\
 &+c^4(t^3+3t^4/2+t^5/5+t^6/10)
       +7t^5/10+2t^6/5+t^7/10,
\end{aligned}
\]
\[
N_T^+=c(61/10+56t/5+23t^2/5)
 +c^2(16/5+51t/5+117t^2/10+5t^3+4t^4/5+t^5/10)
 +t^6/10.
\tag{24}
\]
Expansion of the factored definitions (19)--(23) gives the following
four coefficientwise bounds, uniformly over the indicated two v
values and, in the T rows, the two tau values:
\[
-\partial_c\widehat P_{2,v}\succeq3-N_2^+,
\qquad
-\partial_c\widehat P_{\tau,v}\succeq14/5-N_T^+,
\tag{25}
\]
\[
\begin{aligned}
\widehat P_{2,v}(t,3/19)\succeq{}
 &17/50+2t+4t^2+5t^3+4t^4+2t^5
                  +2t^6/5+t^7/100-t^8/250,\\
\widehat P_{\tau,v}(t,3/19)\succeq{}
 &7/100+2t+5t^2+6t^3+3t^4+t^5
                  +7t^6/100-11t^7/1000.
\end{aligned}
\tag{26}
\]
These small coefficientwise inequalities can be checked directly by
multiplication: (20) has degree at most (8,6), and (21) has degree
at most (7,4). In (25), the adverse terms have all been displayed in
(24), grouped by powers of c; the remaining terms have nonnegative
coefficients. There is no maximization over a hidden coefficient
array. For (26), compare the nine, respectively eight, coefficients
in the explicitly specified univariate polynomials.

For clarity, the numerical-looking steps after (25) are the exact
rational inequalities
\[
N_2^+(1/6,1/6)=24295099/18895680<4/3,
\quad
N_T^+(1/6,1/6)=836939/559872<3/2.
\tag{27}
\]
Both majorants have nonnegative coefficients, and
0<=t<=1/6, 0<=c<=3/19<1/6. Therefore every normalized P strictly
decreases with c. At c=3/19, (26), even after all positive powers
are discarded, gives
\[
\widehat P_{2,v}>17/50-1/250>0,
\qquad
\widehat P_{\tau,v}>7/100-11/1000>0.
\]
This proves all six signs. Sections 4--5 now show that q<=qb is
incompatible with the actual root, establishing the first part of (2).

## 7. The scale bound already forces the required shear

Use the exact physical shear identity from
[MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md):
\[
\overline h:=\sqrt3h
 =H_0-\frac{2U_1Qq}{\alpha^2(1-q)},
\quad
Q=2\beta x-x-\alpha\beta>0,
\]
\[
H_0=\frac{(\beta x-\alpha)[(x+2)\alpha+(2x+1)\beta]}{S^2K_A}.
\tag{28}
\]
This uses rho/(1-rho)=q/[alpha^2(1-q)] at the original physical
point. Define
\[
m=(8x^2+8x-3)\alpha+(3x^2-8x-8)\beta,
\quad W=(\beta x-\alpha)m,
\]
\[
V=\alpha^2W+3K_xK_AQ(x-1).
\tag{29}
\]
Direct collection gives
\[
F:=H_0R+13A/3=\frac{2W}{3S^3K_A}>0,
\quad
G:=F+2U_1QR/\alpha^2=\frac{2V}{3\alpha^2S^3K_A}>0.
\tag{30}
\]
Thus (1-q)(hbar*R+13A/3)=F-Gq, and it suffices to prove
\[
q_b>F/G=\alpha^2W/V,
\quad\hbox{equivalently}\quad \Pi:=29V-30WC>0.
\tag{31}
\]
This last sign uses only the original domain (1). Substitute
x=2+t, alpha=1+(3-k)delta, beta=x(1+delta), so
0<=t<=1/6, 0<=delta<=1/19, 0<=k<=2/5.
The complete adverse part of Pi is the following four-polynomial
bound:
\[
\Pi\ge1869+9378t-\delta B_1-\delta^2B_2
                         -\delta^3B_3-\delta^4B_4,
\tag{32}
\]
where
\[
B_1=32100+66120t+24044t^2,\qquad B_2=8736+17633t,
\]
\[
\begin{aligned}
B_3={}&84240+187134t+134064t^2+22626t^3\\
 &+k^2(15252+34828t+27492t^2+9276t^3+1184t^4+6t^5),\\
B_4={}&70425+184347t+184788t^2+93906t^3
                    +26253t^4+3942t^5+261t^6\\
 &+k^2(12708+31709t+27276t^2+10413t^3+1747t^4+90t^5).
\end{aligned}
\tag{33}
\]
Equation (32) is checked simply by expansion of (29): all omitted
monomials have nonnegative coefficients. Every adverse monomial is
printed in (33).

Use k^2<=4/25 and t^j<=t/6^{j-1} for j>=1. This gives the short
linear bounds
\[
\begin{array}{c|cc}
 &\text{constant bound}&\text{slope bound}\\ \hline
B_1&32100&70200\\
B_2&8800&17700\\
B_3&86700&217000\\
B_4&72500&224000
\end{array}
\tag{34}
\]
For example the exact constant and slope before rounding in the last
two rows are respectively
\[
(2167008/25,\ 48702196/225),\qquad
(1811457/25,\ 107388721/480).
\]
After delta<=1/19, the total constant and slope from (34) are
\[
225070500/130321<1800,
\qquad492238500/130321<3800.
\]
Consequently Pi>69+5578t>0. Combining (31), q>qb, and (30) proves
the second part of (2), at the same original physical scale and
covector. No root or Casimir ceiling has been asserted at qb.
