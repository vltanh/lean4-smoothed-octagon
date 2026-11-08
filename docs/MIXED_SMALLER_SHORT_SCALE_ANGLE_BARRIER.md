# A scale angle barrier for a short bridge with x at most 12/5

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 6.
This is a conditional shape lemma. It does not establish the actual
bound x<=12/5 or close the smaller-short exclusion.

Use the notation of the
[shear and cost reduction](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md).
Assume

\[
1<x\le\frac{12}{5},\qquad
1\le\alpha<x\le\beta\le\alpha x,
\qquad \frac34\le u\le\min\{U(r),U(r_A)\},
\tag{1}
\]

that u is the original incoming secant, and the proved
[strong short order](MIXED_SMALLER_SHORT_STRONG_ORDER.md)

\[
\alpha\ge\frac\beta x+
 \frac{4(x+1)}{7x+1}(\beta-x).
\tag{2}
\]

Put

\[
R=\frac{x-1}{x+1},\quad S=x+1,\quad
K_x=x^2+x+1,\quad K_A=\alpha^2+\alpha\beta+\beta^2,
\]
\[
U_1=U(r),\quad U_2=U(r_A),\quad
A=U_1/U_2-1,\quad J=\frac{3u}{2U_1}.
\]

The physical scale is denoted by s=rho/(1-rho). The two scale caps
needed here are

\[
s\le\frac1{x(x+2)},\qquad s\le\frac1{6\alpha^2}.
\tag{3}
\]

They are respectively the central cap rho<=r^2 and the outer cap
q=rho_A<=1/7. Both remain valid along the scale interval ending at
min(q_c,1/7). No root or outgoing-floor condition is needed in this
note's first three sections.

## 1. A uniform bound on the negative shear

The exact shear is

\[
h=\frac{\sqrt3}{3}
\left\{\frac{(\beta x-\alpha)[(x+2)\alpha+(2x+1)\beta]}
 {S^2K_A}-2U_1Q_0s\right\},
\quad Q_0=2\beta x-x-\alpha\beta>0.
\tag{4}
\]

We prove the strict bound

\[
\boxed{h>-\frac{2\sqrt3}{3}R^2.}
\tag{5}
\]

Let X=x(x+2), D=4x^2+11x+1 and

\[
\beta_m=x+\frac{x(7x+1)(\alpha-1)}D.
\]

Order (2) is exactly beta<=beta_m. The two caps in (3) imply

\[
s\le\frac4{3X+6\alpha^2}.
\tag{6}
\]

Thus (5) follows from positivity of the following polynomial:

\[
\begin{split}
G={}&(3X+6\alpha^2)
 \bigl\{(\beta x-\alpha)[(x+2)\alpha+(2x+1)\beta]
             +2(x-1)^2K_A\bigr\}\\
 &-8K_xQ_0K_A.
\end{split}
\tag{7}
\]

Here and below displayed coefficient identities are ordinary finite
polynomial identities; no sign-testing procedure is a premise.

First G is strictly concave in beta on [x,beta_m]. Its cubic
coefficient is -8K_x(2x-alpha)<0. Its second derivative at beta=x is

\[
-2\bigl[
 -32\alpha^2x^2+10\alpha^2x-20\alpha^2
 -8\alpha x^3-8\alpha x^2-8\alpha x
 +36x^4+25x^3+52x^2-20x\bigr].
\]

This expression increases with alpha, so alpha<=x bounds it above by

\[
2x(4x+5)(x^2-8x+4)<0.
\tag{8}
\]

The last sign holds because x^2-8x+4 decreases on [1,12/5] and
equals -3 at one. It therefore suffices to check beta=x and beta=beta_m.

Set v=(alpha-1)/(x-1), so 0<=v<=1. In the following two lists, the
entries C_i mean the exact identity

\[
P(\alpha)=\sum_{i=0}^4\binom4i C_i(x)v^i(1-v)^{4-i}.
\tag{9}
\]

For P=G at beta=x the five entries are

\[
\begin{array}{c|l}
i&C_i(x)\\ \hline
0&-4x(x-1)(x^2-2x-2)K_x\\
1&-\frac34x(x-1)(5x^4-22x^3-21x^2-14x+10)\\
2&\frac16x(x-1)(x^4+209x^3+66x^2-106x-8)\\
3&\frac34x^2(x-1)(19x^3+72x^2-51x-10)\\
4&3x^3(x-1)(19x^2+x-14).
\end{array}
\tag{10}
\]

Every entry is strictly positive. For the first, x^2-2x-2<=-26/25.
For the second, 5x-22<0 and -21x^2-14x+10<0. For the last three,
the polynomials in parentheses have positive coefficients when expanded
in x-1, including positive constants.

For P=D^3 G at beta=beta_m, the entries are

\[
\begin{array}{c|l}
i&C_i(x)\\ \hline
0&-4x(x-1)(x^2-2x-2)K_xD^3\\
1&-x(x-1)D^2 P_1(x-1)\\
2&-\frac23x(x-1)D P_2(x-1)\\
3&-x^2(x-1)P_3(x-1)\\
4&4x^3(x-1)P_4(x-1),
\end{array}
\tag{11}
\]

where the complete polynomials are

\[
\begin{split}
P_1(d)={}&57d^6+325d^5+533d^4-225d^3
             -1620d^2-1674d-540,\\
P_2(d)={}&934d^8+7259d^7+18844d^6+6441d^5
 -64078d^4-144318d^3-139992d^2-65772d-12096,\\
P_3(d)={}&4212d^9+29788d^8+26153d^7-368022d^6
 -1637287d^5-3285554d^4-3719802d^3\\
 &-2429844d^2-846720d-119808,\\
P_4(d)={}&1850d^8+28554d^7+169131d^6+525877d^5
 +954081d^4+1037733d^3\\
 &+657180d^2+217728d+27648.
\end{split}
\tag{12}
\]

The fourth polynomial is positive. Each of the first three has all
negative coefficients below one degree and all positive coefficients
above that degree. Dividing respectively by d^3, d^4 and d^6 shows
that each quotient is strictly increasing for d>0. Their values at
the right endpoint d=7/5 are

\[
P_1(7/5)=-\frac{38304932}{15625},\quad
P_2(7/5)=-\frac{294492345406}{390625},\quad
P_3(7/5)=-\frac{77482555072276}{1953125}.
\tag{13}
\]

Consequently P_1,P_2,P_3 are negative throughout [0,7/5]. This proves
all entries of (11) positive, hence G>0 and (5).

## 2. A convenient incoming-norm estimate

The
[incoming norm bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md),
Section 1, gives

\[
\operatorname{Sec}(1,x,x)\le\frac34+\frac{R^2}{12}.
\tag{14}
\]

For s in [x,beta], strong order and alpha<=x imply

\[
0\le\frac{s-x}{s+x}
 \le\frac{\beta_m-x}{\beta_m+x}
 \le\frac R2.
\tag{15}
\]

For the final inequality it suffices to put alpha=x; after clearing
positive denominators it is (7x+1)(x+3)<=2D, whose difference is x^2-1.
The positive integral formula for the secant is

\[
u-\frac34=\frac1{4(\beta-1)}
 \int_1^\beta\frac{(s-x)^2}{(s+x)^2}\,ds.
\]

Its first part has mean at most R^2/12 by (14), and its tail has mean
at most R^2/16 by (15). Thus

\[
\boxed{u\le\frac34+\frac{R^2}{12}.}
\tag{16}
\]

Writing b_i=1-u/U_i, we consequently have

\[
b_1\ge\frac{R^2}{6U_1},\quad
0\le b_2\le b_1\le\frac{49}{916},\quad
0\le A\le\frac{R^2}{3},\quad
U_1\le\frac{229}{289}<\frac45.
\tag{17}
\]

Here U_1=3/4+R^2/4, R<=7/17 and U_2>=3/4.

## 3. The upper critical angle and clipping are absent

Fix 9/8<=kappa<=3/2. Set

\[
K=A+2+\frac{2\kappa}{J},\qquad
\mathscr D=\sqrt{K^2-A^2},\qquad
\delta=2\arctan\frac{\sqrt{h^2+A^2}-h}{K+\mathscr D}.
\]

Since J<=3/2, we have K+mathscr D>=2(K-A)>=7. The numerator is a
decreasing function of h. Applying (5) and (17) therefore gives

\[
\sqrt{h^2+A^2}-h
 <\frac{\sqrt{13}+2\sqrt3}{3}R^2
 <\frac52R^2.
\]

Hence

\[
\delta<\frac57R^2\le\frac5{17}R.
\tag{18}
\]

On the other hand, the first critical-angle parameter satisfies

\[
\theta_1=\arcsin\sqrt{\frac{3b_1}{2\kappa+3}}
 \ge\sqrt{\frac{b_1}{2}}
 \ge\frac R{\sqrt{12U_1}}>
 \frac5{16}R.
\tag{19}
\]

Thus delta<theta_1<=theta_1+theta_2 everywhere in the scale interval.
The possible interior local minimum described in the shear reduction
cannot occur.

For completeness, the fixed lower-row angle has the exact identity

\[
\psi=\arctan\frac{x-1}{\sqrt3(x+1)}
       +\arctan\frac{\beta-\alpha}{\sqrt3(\beta+\alpha)}.
\]

Since beta<=alpha*x, this gives

\[
\tan\psi\le\tan\left(2\arctan\frac7{17\sqrt3}\right)
 =\frac{357}{409\sqrt3}<\frac1{\sqrt3},
\]

so psi<pi/6. Also delta<35/289<1/6<pi/6 by (18). Therefore
psi+delta<pi/3 and the completion term is always on its active branch.

## 4. A remaining sufficient condition for decreasing scale score

This section records a useful exact reduction; its additional
hypothesis is not asserted to follow from the actual root conditions.
If

\[
\boxed{-hR\ge3A,\qquad h<0,}
\tag{20}
\]

then the fixed-kappa completion score strictly decreases with scale
throughout the interval after that point. Indeed h decreases with
scale, so (20) persists, while the upper bounds already proved hold
throughout the interval.

Here is a radical-free verification of the claim. Put H=-h>0,
c=kappa+3/2 and b=b_1+b_2. Differentiating the active score shows that
decrease with scale is equivalent to

\[
\mathcal Q_c(H^2)\le0,
\]
\[
\boxed{\mathcal Q_c(X)=J^2X^2+
 \left[-3cb+\frac92(b_1^2+b_2^2)\right]X
 +A^2\left(c-\frac32b\right)^2.}
\tag{21}
\]

For an explicit derivation, use

\[
\frac{\sin\delta}{\sqrt{H^2+A^2}}
 =\frac{K+\mathscr D H/\sqrt{H^2+A^2}}{K^2+H^2},
\qquad JK=2c-\frac32b.
\]

The desired derivative sign is c*sin(delta)>=J*sqrt(H^2+A^2).
After moving the K term, both sides are positive, because
JK-c=c-3b/2>0. Squaring and cancelling the positive factor
K^2+H^2 gives (21). In particular, mathcal Q is convex as a function
of c, so its signs at c=21/8 and c=3 would suffice.

The following estimates prove the whole interval simultaneously.
By (5), (17) and (20),

\[
H^2\le\frac{11}{10}b,\qquad
\frac{A^2}{H^2}\le\frac{R^2}{9}
 \le\frac23U_1b,\qquad
b\le\frac{49}{458}.
\tag{22}
\]

For the first inequality, H^2/b<=8U_1R^2<=89768/83521<11/10.
Using J<=3/2 and 21/8<=c<=3 in (21) now gives the strict bound

\[
\frac{\mathcal Q_c(H^2)}{H^2}
 \le b\left(\frac{99}{40}-\frac{63}{8}
             +\frac{441}{916}+\frac{1374}{289}\right)
 =-\frac{217383}{1323620}b<0.
\tag{23}
\]

The strict last sign follows from R>0 and (17). This proves the
conditional monotonicity claim. To apply it to an actual short bridge,
one must still prove the actual bound x<=12/5 and (20), or supply a
different argument locating the initial point after the lower critical
angle. Neither obligation is discharged by this note.

## 5. The sufficient shear threshold can be reduced to 5A/2

This strengthening is also accepted in Section 6 of the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md).

In fact the sufficient condition (20) can be weakened to

\[
\boxed{-hR\ge\frac52A,\qquad h<0.}
\tag{24}
\]

Here is a hand sign proof retaining the relations between the two norm
deficits. Write v=b_1, a=1-v and w=b_2=v-aA. Divide the expression in
(21) by H^2 and call the result Q. Then

\[
Q=\frac94a^2H^2-3c(v+w)+\frac92(v^2+w^2)
       +\frac{A^2}{H^2}\left(c-\frac32(v+w)\right)^2.
\tag{25}
\]

The bounds already proved imply

\[
v\ge v_0:=\frac{2R^2}{3(3+R^2)},\quad
H<\frac76R^2,\quad A\le\frac25HR\le\frac7{15}R^3.
\tag{26}
\]

Lowering v to v_0 at fixed H,A is legitimate: the resulting w is
nonnegative, because

\[
\frac{v_0}{1-v_0}-\frac7{15}R^3
 =\frac{R^2(30-63R-7R^3)}{15(9+R^2)}>0
 \qquad(0<R\le7/17).
\tag{27}
\]

The numerator's parenthesis is decreasing, and at R=7/17 it equals
17540/4913>0. Along this change, Q strictly decreases as v increases.
Indeed the derivative of its first term is nonpositive; its second
term has derivative -3c(2+A)<=-63/4. The positive derivative of the
third term is

\[
9[v+(1+A)w]
 \le9\frac{49}{916}\frac{33}{16}<1,
\]

using A<=R^2/3<=49/867<1/16. The last term has nonpositive derivative,
since c-3(v+w)/2>0. Thus Q is bounded above by its value at v=v_0.

At fixed v,H,c the expression Q strictly increases with A. Its first
two A-dependent terms have combined derivative 3a(c-3w)>0, and the
last term has nonnegative derivative. We may therefore raise A to
(2/5)HR. Condition (27) keeps w nonnegative throughout this change.

Now put d=2R/5 and substitute A=dH. The result is an upward quadratic
in H. Its linear coefficient is

\[
3ad(c-3v)(1+d^2)>0,
\]

and its quadratic coefficient is positive. It is therefore increasing
for H>=0. Raise H to 7R^2/6. Finally Q is convex in c, so it suffices
to use c=21/8 and c=3.

After these substitutions the two exact identities are

\[
Q=\frac{R^2 P_c(R)}{90000(R^2+3)^2},
\tag{28}
\]

where

\[
\begin{split}
P_{21/8}(R)={}&-1941975+2976750R+2037375R^2+1043280R^3\\
 &+1350675R^4+116970R^5+270529R^6+4200R^7\\
 &+23912R^8+784R^{10},\\
P_3(R)={}&-2073600+3402000R+2019825R^2+1300320R^3\\
 &+1359450R^4+162960R^5+270529R^6+6720R^7\\
 &+23912R^8+784R^{10}.
\end{split}
\tag{29}
\]

Every nonconstant coefficient is positive, so both polynomials increase
on [0,7/17]. Their right endpoint values are

\[
P_{21/8}(7/17)=-\frac{516943348318919900}{2015993900449}<0,
\quad
P_3(7/17)=-\frac{397497263357517500}{2015993900449}<0.
\tag{30}
\]

It follows that Q<0, proving strict score decrease under (24).
For a convenient rational target in the root equations, set
\(\bar h=\sqrt3 h\). The inequality

\[
\bar hR+\frac{13}{3}A<0
\tag{31}
\]

implies (24), because 13/(3sqrt(3))>5/2: squaring reduces this last
comparison to 676>675. The implication from actual
root feasibility to (24) or (31) remains unproved here.
