# A variable floor weight for the sharper short-ratio bound

Date: 2026-11-08 UTC. **Result:** every actual smaller-short bridge on
13/6 <= x < 12/5 forces a positive scalar value on the central or outer
scale face in Section 7. The proof below is analytic, including the
scale continuation. See the
[reconstruction audit](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_AUDIT.md).
The two positive-scale terminal signs are still separate obligations;
this reduction does not close S2 or exclude the actual bridge.

Use the actual common-covector smaller-short geometry of the
[large-ratio theorem](MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md).
Assume, for contradiction in a sharper ratio argument, that
\[
13/6\le x<12/5.
\tag{1}
\]
The [positive-diagonal theorem](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md),
together with the large-ratio theorem, supplies D>0. Put
S=1+x, Q=alpha(alpha+beta), r_A=alpha/(alpha+beta),
q=rho_A and T=r_A/q. All other transport quantities retain their
original definitions.

## 1. The actual scalar test and its envelope

Let
\[
y=\tau/T,\qquad m(y)=2-7y/4,\qquad
G_\tau=R_\tau+m(y)(w-3/4).
\tag{2}
\]
At the actual first outer root, 2<tau<T, R_tau=0 and w>3/4.
Consequently G_tau>0. The weight satisfies 1/4<=m<=2.

With geometry and tau fixed, m is independent of the opposite turn
parameters t,v. The envelope derivative identities are therefore the
ones in the
[floor-weighted envelope theorem](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md),
with z=tau+m replacing tau+1/2. Since
\[
z=2+\tau(1-7/(4T))\le T+1/4<T+1/2,
\]
and T>2, the same positive B_z argument applies. More explicitly, if
D>S, its lower bound at t=rho*S is at least
\[
1-\frac{5(D-S)}{4Q}>0,
\qquad 4Q-5(D-S)\ge x(3x-5)>0.
\]
If D<=S, positivity is immediate. Thus
\[
\boxed{0<G_\tau\le G_\tau^*
 :=R_\tau^*+m(y)(w_*-3/4).}
\tag{3}
\]
The outgoing floor was inserted before this comparison; it is not
asserted separately at w_*.

## 2. Domain bounds used below

The proof of alpha/beta<3/4 in Section 2 of the cited floor-weighted
note applies already for x>=15/7. Indeed its increasing lower function
F satisfies F(15/7)=2/351>1/196. Hence in (1)
\[
\frac5{17}<\frac1S\le r_A<\frac37.
\tag{4}
\]
The left weak inequality r_A>=1/S is beta<=alpha*x.

The two equal secants also give u<=V(x). The accepted incoming estimate
therefore gives
\[
\frac34<u\le\frac34+
 \frac{2(x-1)^2}{(x+1)(35x+13)}<\frac{61}{80}.
\tag{5}
\]
For the last inequality it suffices to check
-125x^2+368x-147>0; this concave quadratic is positive at both
endpoints of (1).

We will also use D<Q. A proof using only the stronger upper order works
on the larger interval 2<=x<=12/5. Set
\[
b_0=\frac{x(9x+8\alpha)}{9x+8}\le\beta.
\]
Since alpha-2x<0,
\[
D-Q\le1+2x+b_0(\alpha-2x).
\]
This is convex in alpha, so its maximum for 1<=alpha<=x occurs at an
endpoint. The endpoint values are
\[
1+3x-2x^2<0,\qquad
1+2x-\frac{17x^3}{9x+8}<0 \quad(x\ge2).
\tag{6}
\]
For the second sign, multiply by 9x+8: the negative of its numerator is
17x^3-18x^2-25x-8, positive at x=2 and increasing thereafter.
Thus tau*d<=T*d=D/Q<1.

Finally D<=3alpha^2 on x>=2: after using beta>=x, the difference
3alpha^2-D is bounded below by
\[
2(\alpha-x/2)^2+\frac32x^2-2x-1>0.
\tag{7}
\]
In particular 0<d<3/7 on q<=1/7.

## 3. Increasing the incoming norm is legitimate

At fixed geometry, scale and tau, the coefficient of u in G_* is
\[
(G_*)_u=\frac1{r_A}+\lambda S-2d
 +(\tau+m)d(d-\lambda S).
\tag{8}
\]
For D<=0 all terms are positive after grouping as
1/r_A-2d+(tau+m)d^2+[1-(tau+m)d]lambda*S.
For D>0, Section 2 gives
(tau+m)d<1+d/4. Discarding the nonnegative (tau+m)d^2 term gives
\[
(G_*)_u>\frac1{r_A}-d(2+\lambda S/4)
 >2-\frac37\frac{57}{20}=\frac{109}{140}>0.
\tag{9}
\]
Thus any proved upper bound on the actual u may be inserted in the
scalar endpoint tests. Equation (9) is also valid on 2<=x<=12/5 when
the stronger upper order is retained. It does not claim that an
incident norm ceiling survives that substitution.

## 4. Convexity in scale

Use A_1,A_2,A_3,C,L from the
[normalized envelope theorem](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
At fixed p=tau*q the number y=p/r_A, and hence m, is fixed. Thus
\[
G_*(q)=C(p)+m/4+q[L(p)-mA_1]+mq^2A_2.
\tag{10}
\]
We have A_2>0 throughout the original shape in (1). Here is the
completed-square proof, retaining its algebraic details. Put
\[
a=\alpha^{-2},\quad \varepsilon=1-a,\quad
\delta=D/\alpha^2,\quad H=S(1-u)-1/S,
\]
\[
A=\varepsilon^2+\varepsilon Sa+S^2a^2,
\quad K=\varepsilon H+(2S-1)a.
\]
Then A_2=A-delta*K+u*delta^2. For delta<=0 this is positive.
For delta>0, the elementary order argument in
[the previous scale reduction](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md),
Section 3, gives z=(S-2)^2a<2. Since H<=S/4-1/S, let
Kbar=epsilon(S/4-1/S)+(2S-1)a. Then
\[
A_2\ge A-\overline K^2/3,
\]
\[
\overline K^2-3A
 =\frac{S^4-56S^2+16+2(7S^2-4)z+z^2}{16S^2}
 <\frac{S^4-28S^2+4}{16S^2}<0.
\tag{11}
\]
The final sign holds for 2<S<=17/5: S^2<=25 makes the numerator at
most 4-3S^2<0. Hence (10) is strictly convex in q.

It follows that its maximum on the closed scale interval is at q=0
or
\[
q=\min\{q_c,1/7,p/2\},\qquad
q_c=\frac{\alpha^2}{S^2+\alpha^2-1}.
\tag{12}
\]

## 5. The zero-scale value is strictly negative

Write y=p/r_A. The elementary bound log y<=y-1 makes G_*(0) at most
\[
F(y)=E_0+\frac{u-1}{r_A}+r_A+\frac12
       +y\left(\frac9{16}-r_AA_1\right).
\tag{13}
\]
This is affine in y. Equations (4)--(5) give
\[
F(0)\le-\frac{19}{80}\left(\frac{19}6+\frac73\right)
 +\frac6{19}+\frac37+\frac12
 =-\frac{1317}{21280}<0.
\tag{14}
\]
At y=1, collecting A_1 gives exactly
\[
F(1)=E_0(1-D/Q)+\frac{u-1}{r_A}
 +\frac{17}{16}-r_A-\frac{r_A(x-1)}{\alpha^2}.
\]
Now E_0<0, D<Q and u<=U(r_A). Consequently
\[
F(1)<\frac1{16}-\frac{r_A(x-1)}{\alpha^2}
 \le\frac1{16}-\frac{x-1}{x^2(x+1)}
 \le\frac1{16}-\frac{175}{2448}
 =-\frac{11}{1224}<0.
\tag{15}
\]
The last middle function decreases for x>=13/6, as follows by one
differentiation. Equations (13)--(15) remove q=0.

## 6. Strict increase on the tau=2 face

Keep the actual shape and incoming norm fixed and put
G_2(q)=G^*_{tau=2}(q). Because beta<=alpha*x, (4) implies
T=r_A/q>35/17>2 for every q<=1/7. Thus this continuation never passes
an invalid duration ordering.

Direct differentiation of (10), now with p=2q, gives
\[
\begin{aligned}
G_2'(q)={}&q^{-1}-4A_1-1-A_3-\frac7{8r_A}\\
&+q\left(8A_2+\frac{7A_1}{r_A}\right)
 -\frac{21q^2A_2}{2r_A}.
\end{aligned}
\tag{16}
\]
Set p=r_A in the remainder of this section, and put Y=2q/p in [0,1].
The cubic qG_2'(q) has the Bernstein form
\[
qG_2'(q)=\sum_{i=0}^3\binom3i B_iY^i(1-Y)^{3-i},
\]
\[
\begin{aligned}
B_0={}&1,\\
B_1={}&41/48-p(1+A_3+4A_1)/6,\\
B_2={}&17/24-p(1+A_3)/3-3pA_1/4+2p^2A_2/3,\\
B_3={}&9/16-p(1+A_3)/2-pA_1/4+11p^2A_2/16.
\end{aligned}
\tag{17}
\]
Every coefficient is strictly positive, as follows.

### 6.1. The first coefficient

Put k=p*delta=D/Q, J=pK, B=p(2epsilon+Sa). Then
\[
pA_1=B-kH,\quad pA_3=2uk-J,\quad
p^2A_2=p^2A-kJ+uk^2.
\tag{18}
\]
Here k>=0 and J>0. Moreover H>=u/2: the function
S(1-u)-1/S-u/2 increases with S and decreases with u, so its minimum
on (22) is 251/4560>0. Finally B<=9/8. Indeed,
after beta>=x this last assertion is equivalent to
\[
-7\alpha^2+9\alpha x-8x+8\ge0.
\]
The quadratic is concave in alpha, and its endpoint values are x+1
and 2(x-2)^2. Therefore
\[
B_1\ge\frac{41}{48}-\frac{3/7+4(9/8)}6
 =\frac{11}{336}>0.
\tag{19}
\]

### 6.2. Complete the remaining diagonal squares

Equations (17)--(18), followed by completing the square in k, give
\[
B_2\ge F_2:=\frac{17}{24}-\frac p3-\frac{3p(2\varepsilon+Sa)}4
 +\frac{pK}3+\frac{2p^2A}3
 -\frac{(9H-8u-8pK)^2}{384u},
\tag{20}
\]
\[
B_3\ge F_3:=\frac9{16}-\frac p2-\frac{p(2\varepsilon+Sa)}4
 +\frac{pK}2+\frac{11p^2A}{16}
 -\frac{(4H-16u-11pK)^2}{704u}.
\tag{21}
\]
The coefficient of a^2 in A-K^2/(4u) is
\[
-\frac{S^2[u-U(1/S)]^2}{4u}\le0.
\]
Consequently F_2 and F_3 are concave in a. It suffices to check a=0
and a=1 on the enlarged box
\[
19/6\le S\le17/5,\quad5/17\le p\le3/7,
\quad3/4\le u\le61/80.
\tag{22}
\]

### 6.3. Monotonicity reduces the square bounds to eight quartics

Write \(F_{ie}=F_i|_{a=e}\) for \(i=2,3\), \(e=0,1\).
We first show that each \(F_{ie}\) decreases with \(p\) throughout
(22), and then use concavity in \(u\). All derivative signs needed
for this reduction are displayed below.

The coefficients of \(p^2\) in the four expressions are

\[
\begin{array}{c|cc}
 & e=0 & e=1\\ \hline
F_2 & (4u-H^2)/(6u) & [4uS^2-(2S-1)^2]/(6u)\\
F_3 & 11(4u-H^2)/(64u) & 11[4uS^2-(2S-1)^2]/(64u).
\end{array}
\tag{23}
\]

They are positive. Indeed \(0<H<3/5\), \(4u\ge3\), and

\[
4uS^2-(2S-1)^2\ge-S^2+4S-1\ge26/25>0.
\]

Thus \(\partial_p F_{ie}\) increases with \(p\), and it suffices to
bound it at \(p=3/7\). Let \(f_{ie}(S,u)=
\partial_p F_{ie}(S,3/7,u)\). Direct differentiation of (20)--(21)
gives the following four factorizations:

\[
\begin{aligned}
\partial_u f_{20}&=
 \frac{13(S^2u-S^2+1)(S^2u+S^2-1)}{56S^2u^2}<0,\\
\partial_u f_{21}&=
 -\frac{(S+3)(2S-1)(5S-7)}{56Su^2}<0,\\
\partial_u f_{30}&=
 -\frac{5(S^2u-S^2+1)(S^2u+S^2-1)}{224S^2u^2}>0,\\
\partial_u f_{31}&=
 \frac{(2S-1)(38S^2-33S+28)}{224Su^2}>0.
\end{aligned}
\tag{24}
\]

For the first and third signs,
\(S^2u-S^2+1=1-S^2(1-u)<0\) throughout (22), while
\(S^2u+S^2-1>0\). The other factors are positive on \(S\ge19/6\).
The maximum in \(u\) is therefore at \(u=3/4\) in the first two
rows and at \(u=61/80\) in the last two. The negative of each maximum
has the following explicit form:

\[
\begin{aligned}
-f_{20}(S,3/4)&=
 \frac{-13S^4+952S^2-208}{672S^2}>0,\\
-f_{21}(S,3/4)&=
 \frac{-10S^3+19S^2+256S-84}{168S}>0,\\
-f_{30}(S,61/80)&=
 \frac{361S^4+86752S^2+6400}{218624S^2}>0,\\
-f_{31}(S,61/80)&=
 \frac{361S^3-1653S^2+3488S-560}{3416S}>0.
\end{aligned}
\tag{25}
\]

Here are elementary checks of all four numerator signs. In the first,
\(S^2<12\) bounds the numerator below by \(796S^2-208>0\).
In the second, \(S<4\) gives successively

\[
-10S^3+19S^2+256S-84
 >-21S^2+256S-84>172S-84>0.
\]

The third numerator has positive coefficients. For the fourth put
\(h=S-19/6\ge0\); its numerator is exactly

\[
361h^3+\frac{3553}{2}h^2+\frac{46549}{12}h
 +\frac{1160533}{216}>0.
\]

Equations (23)--(25) prove \(\partial_p F_{ie}<0\), so it suffices
to take \(p=3/7\) when finding a lower bound.

At fixed \(S,p,e\), the expressions \(F_{ie}\) are concave in \(u\).
In fact \(H\) and \(K\) are affine in \(u\), every term outside the
negative square in (20) or (21) is affine in \(u\), and a negative
square divided by \(u>0\) has the form
\(-(A-Bu)^2/(c u)\), whose second derivative is
\(-2A^2/(c u^3)\le0\). Thus the minimum in \(u\) is attained at
one of \(3/4,61/80\).

### 6.4. Eight explicit endpoint identities

The final check is univariate. For each row below,

\[
F_{ie}(S,3/7,u)=
 \frac{c_0+c_1h+c_2h^2+c_3h^3+c_4h^4}{dS^2},
\qquad h=S-19/6\in[0,7/30]\subset[0,1/4).
\tag{26}
\]

Every coefficient of each quartic is printed, so the identities are
verified by substitution in (20)--(21) and collection of four powers.
The signs follow from the short estimates immediately after the table.

| \(i,e,u\) | \(d\) | \(c_0\) | \(c_1\) | \(c_2\) | \(c_3\) | \(c_4\) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| \(2,0,3/4\) | 75264 | 24164423/432 | 1930181/18 | 69135/2 | 634 | -507 |
| \(2,0,61/80\) | 30607360 | 8143072511/432 | 740586173/18 | 27831159/2 | 407626 | -183027 |
| \(2,1,3/4\) | 75264 | 48298295/432 | 4320821/18 | 289599/2 | 37594 | 3669 |
| \(2,1,61/80\) | 30607360 | 14301349999/432 | 1512552205/18 | 106561127/2 | 14249450 | 1419357 |
| \(3,0,3/4\) | 413952 | 396921719/1296 | 24626333/54 | 1033583/6 | 55498/3 | -25 |
| \(3,0,61/80\) | 168340480 | 135808237103/1296 | 9137501813/54 | 394305047/6 | 21464794/3 | -9025 |
| \(3,1,3/4\) | 12936 | 11117935/1296 | 1276571/108 | 9773/3 | -619/3 | -107 |
| \(3,1,61/80\) | 10521280 | 7848857819/1296 | 488973617/54 | 15819323/6 | -373118/3 | -80389 |

The third and fourth numerators have all coefficients positive. For
the first, second, fifth and sixth rows, the only negative term is
the quartic one; the numerator is greater than
\(c_0-|c_4|/256>0\). The following integer comparisons give these
four signs without approximation:

\[
\begin{array}{c|cc}
\text{row}&c_0>&|c_4|/256<\\ \hline
1&50000&2\\
2&18000000&715\\
5&300000&1\\
6&100000000&36.
\end{array}
\]

For the seventh row, the sum of the absolute values of the negative
terms is bounded above by

\[
\frac{619}{192}+\frac{107}{256}<4,
\qquad c_0>8000.
\]

For the eighth it is bounded above by

\[
\frac{373118}{192}+\frac{80389}{256}<2258,
\qquad c_0>6000000.
\]

All denominators in (26) are positive. Hence all eight endpoint
values are strictly positive; (23)--(25) and concavity in \(u\) give
\(F_2,F_3>0\) on (22). Concavity in \(a\) then yields
\(B_2,B_3>0\) in (20)--(21). Together with (19) and \(B_0=1\),
the Bernstein identity (17) proves \(G_2'(q)>0\) over the full
continuation under consideration. This argument uses only the eight
displayed quartic identities and elementary derivative signs.

## 7. The two remaining scalar obligations

By Sections 4--6, positive actual G forces a positive upper-envelope
value on one of just
\[
q=q_c\le1/7,\qquad q=1/7\le q_c,
\tag{27}
\]
with 2<=tau<=T and the actual equal-secant shape fixed. The incoming
norm may then be raised by Section 3. The fixed-geometry quantities
remain scalar comparison data; neither physical cost nor an upper
Casimir cap is transferred to (27).

A rational duration majorant suitable for these two signs is
\[
\log y\le2r+\frac23r^3,\qquad
r=\frac{y-1}{y+1}\in[-1,0].
\tag{28}
\]
Indeed log y=2 integral_0^r (1-s^2)^(-1) ds, and subtracting the first
two terms leaves the integral of 2s^4/(1-s^2), which is nonpositive
when r<=0. Formula (28) is one global inequality, not a covering of
duration intervals. The rational signs after these substitutions are
the only remaining obligations of this reduction.
