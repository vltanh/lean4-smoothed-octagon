# Shape monotonicity for a simpler low-t large-gap residual

## Status and exact scope

This note proves a new, small-identity shape reduction on the entire domain of
[the low-t unit-shape sign](../../archive/notes/MIXED_NONSHORT_LARGE_GAP_LOW_T_SIGN.md).
It also proves the scalar substitution signs for its new multipliers.
The remaining unit-shape inequality for the **new** residual is not proved here.
Consequently this note alone does not replace the existing unit-shape certificate
or close a new top-level exclusion gate.

The replacement interface is

\[
\boxed{\partial_k G_n(t,x,q,k)>0\qquad(1\le k\le1+j).}
\tag{1}
\]

If the separate claim \(G_n(t,x,q,1)>0\) is proved, the actual low-t caller
in theorem fh_LGA_core of FwdHand/LargeGap.lean closes using (1), with both old
shape endpoint certificates replaced by that one claim. The old unit-shape
certificate is for different multipliers; it cannot be substituted for this
missing claim.

All expansions below are staged in one variable, with the coefficient
polynomials kept opaque. The largest bivariate identity has total degree eight.
The displayed sign polynomials have at most 20 monomials; the final univariate
identities have degree at most seven and at most eight monomials.
There are no coefficient tables, parameter subdivisions, or executable sign
premises.

## 1. Domain and the new necessary condition

Assume

\[
\frac13\le t\le\frac38,\qquad h=1-2t,\qquad
\frac1{30}\le j\le\frac{5h}{7},\qquad x=h+j,
\qquad 1\le q\le\frac{1+x}{1+2j}.
\tag{2}
\]

Write

\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad
Y=x^2+2x,\quad J=t+x^2+2x,\quad y=q-1,\quad e=q/W.
\]

The following consequences will be used:

\[
\frac{17}{60}\le x\le\frac47,\qquad
0\le y\le\frac9{32},\qquad
y\le\frac{29-60t}{32}<b(t):=\frac{18-37t}{20}.
\tag{3}
\]

Indeed \(y\le(h-j)/(1+2j)\), which decreases with \(j\), so the last
bound before \(b(t)\) follows by setting \(j=1/30\).
The difference is

\[
b(t)-\frac{29-60t}{32}=\frac{4t-1}{160}>0.
\tag{4}
\]

Use the simple multipliers

\[
\boxed{a=\frac72-10y,\qquad m=8j+8y-\frac16.}
\tag{5}
\]

Thus \(a\ge11/16\) and \(m\ge1/10\).
Use the original single logarithm majorant

\[
\log q\le L(q):=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}
\qquad(q\ge1)
\tag{6}
\]

and the following incoming bound:

\[
T_L(x)=\frac{912-401x}{24(17x+76)},\qquad
V_L=1-\frac{cp}{W^2}+\frac{cx}{W^2}(T_L(x)-t).
\tag{7}
\]

It is an upper bound for the original incoming majorant. More precisely,
with \(T_G(x)=(90-19x^2)/(12(x^2+10x+15))\),

\[
T_L(x)-T_G(x)=
\frac{5x(7x-3)^2}
 {24(17x+76)(x^2+10x+15)}\ge0\qquad(x\ge0).
\tag{8}
\]

The numerator is \(245x^3-210x^2+45x\): three monomials, degree three.
Thus the existing strict actual bound \(v<V_G\) implies \(v<V_L\).

Let \(N,\mathcal T_U,\mathcal T_*,C_*\) have the original meanings in
[the multiplier note](../../archive/notes/MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md).
Set

\[
F_\ell=1+\frac{p^2q}{W^2}
       -\frac pW\frac{q^2+10q+1}{6(q+1)},
\]

\[
\boxed{
G_n=(a+1-Je^2)N(V_L,L)
       +C_*(3/4-\mathcal T_U(V_L))+m(F_\ell-V_L).
}
\tag{9}
\]

This is negative at every hypothetical actual eligible point in (2).
Here is the complete substitution argument. The original actual inequalities
give

\[
\mathcal H_n=aN+C_*(3/4-\mathcal T_*)+m(F-v)<0.
\]

The original transport identity rewrites its first two terms as
\((a+1-Je^2)N+C_*(3/4-\mathcal T_U)\).
The multiplier note already proves on this domain

\[
Je^2<17/16,\quad WD/x\le41/24,\quad W^2Dek<3h,\quad
A:=-N_v\ge xeWk>0.
\]

In particular \(a+1-Je^2>5/8\).
If \(a\ge2\), the same coefficient estimate as in that note gives

\[
(\mathcal H_n)_v<
-\frac{31}{16}A+W^2Dek-m
\le-\frac{11}{48}A-m<0.
\]

If \(a<2\), then \(y>3/20\), and

\[
m>\frac8{30}+\frac65-\frac16=\frac{13}{10}>3h.
\]

Discarding the negative \(N_v\) contribution now gives
\((\mathcal H_n)_v<W^2Dek-m<0\).
The logarithm coefficient is negative because it is the sum of
\((a+1-Je^2)N_\ell<0\) and \(-m(p/W)q/(q-1)<0\).
The already justified scalar substitutions therefore imply \(G_n<0\).
At \(q=1\) the rational expression has its continuous endpoint value;
actual arc durations are positive.

## 2. Product definitions for the shape calculation

For free scalar arguments \(v,\ell\), put

\[
B=k+2tx+x^2,\quad Z=v-1+t^2,\quad
H=kZ+t^2(2-t),
\]

\[
Q=t(k^2-kt+t^2)+HY+tvY^2,\qquad
E_0=q^2B+W^2-2pqW.
\]

Retain the product expressions

\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
 &-tBqWp\ell-tBqW^2v-q^2Q+qWp(H+2tvY),\\
\mathcal P={}&3tE_0^2-4tvW^4
                +4q^2W^2(H+2tvY)-4q^4Q,\\
F(v,\ell,k)={}&(a+1-Je^2)N
                   +\frac{qJ-pW}{4qW^2}\mathcal P.
\end{aligned}
\tag{10}
\]

Then \(G_n=F(V_L,L,k)+m(F_\ell-V_L)\), so
\(\partial_kG_n=F_k(V_L,L,k)\).
The last two terms have no shape dependence.

We will compare the scalar arguments to

\[
\overline T=\frac12-\frac7{24}x,\qquad
\overline V=1-\frac{cp}{W^2}+\frac{cx}{W^2}(\overline T-t),
\qquad
\overline L=y-\frac5{12}y^2.
\tag{11}
\]

These are algebraic comparisons with the fixed bounds (6)--(7),
not additional analytic approximation premises. Indeed

\[
\overline T-T_L(x)
=\frac{x(73-119x)}{24(17x+76)}>0
\tag{12}
\]

because \(119x\le68\). Its numerator has two monomials and degree two.
Also

\[
y-L(q)=\frac{y^2(5q+1)}{6q(q+1)}\ge\frac5{12}y^2,
\tag{13}
\]

since \(1\le q\le41/32\) and
\[
2+5q-5q^2\ge
2+5(41/32)-5(41/32)^2=\frac{203}{1024}>0.
\]
The polynomial in this last check has three monomials and degree two.
Thus \(V_L<\overline V\) and \(L\le\overline L\).

## 3. The mixed shape derivatives have negative signs

Differentiating the products in (10) gives

\[
A_k:=-N_{kv}=xq\{1+tW+(x+2)y\}>0,
\]

\[
F_{kv}=-(a+1-Je^2)A_k+q(qJ-pW)(1-Ye^2),
\qquad
F_{k\ell}=-(a+1-Je^2)tpqW<0.
\tag{14}
\]

The full sign of the first expression has a short coefficient proof.
It is independent of \(k,v,\ell\). Write

\[
F_{kv}=-\frac{q}{2W}\,\mathcal B(t,x,y),\qquad
\mathcal B=B_0+B_1y+B_2y^2,
\tag{15}
\]

where every coefficient polynomial is printed:

\[
\begin{aligned}
B_0={}&-2t^2x+7tx^3+14tx^2+9tx+7x^2+7x,\\
B_1={}&-4t^2x-24tx^3-52tx^2-26tx-2t+7x^3+x^2-6x,\\
B_2={}&-2x(t^2+tx^2+3tx+t+10x^2+30x+20).
\end{aligned}
\tag{16}
\]

These have respectively 6, 8 and 7 monomials, all of degree at most four
in \(t,x\). To check (15), collect the coefficients in \(y\) of

\[
x\{(a+1)W^2-Jq^2\}\{1+tW+(x+2)y\}
 -(qJ-pW)(W^2-q^2Y)=\frac W2\,\mathcal B.
\]

This consists of three separate bivariate coefficient identities.
There is no need to expand the entire three-variable expression.

One has \(B_2<0\), and

\[
-B_1=2t+(4t^2+26t+6)x+(52t-1)x^2+(24t-7)x^3>0.
\]

Thus \(\mathcal B\) decreases with \(y\ge0\). At its larger endpoint,
the complete eight-monomial identity is

\[
\begin{aligned}
512\mathcal B(t,x,9/32)
={}&-1681t^2x+47tx^3-563tx^2+783tx-288t\\
 &+198x^3+1298x^2+1100x.
\end{aligned}
\tag{17}
\]

The degree is four. Its cubic and quadratic coefficients in \(x\) are
positive, and \(783-1681t\ge1221/8>0\). Consequently

\[
512\mathcal B(t,x,9/32)\ge1100x-288t
\ge\frac{611}{3}>0.
\]

Equations (14)--(17) prove \(F_{kv}<0\).
Finally,

\[
F_{kk}=-\frac{tq^3(qJ-pW)}{2W^2}<0,
\tag{18}
\]

because \(qJ-pW\ge J-pW=xc>0\). The identity follows from the
two quadratic shape terms in \(\mathcal P\), whose second derivatives
are \(6tq^4\) and \(-8tq^4\); \(N\) is affine in shape.

Combining (11)--(18), for \(k\le k_+:=1+j=2t+x\),

\[
\partial_kG_n
\ge F_k(V_L,L,k_+)
> F_k(\overline V,\overline L,k_+).
\tag{19}
\]

## 4. A quartic lower bound with small coefficient identities

At the arguments on the right of (19), one has

\[
F_k(\overline V,\overline L,k_+)
=\frac{q}{48W^3}S(t,x,y),\qquad
S=S_0+S_1y+S_2y^2+S_3y^3+S_4y^4.
\tag{20}
\]

Here are all five coefficient polynomials:

\[
\begin{aligned}
S_0={}&x(1-t)\bigl[
24t(1-2t)+(84-60t-72t^2)x\\
&\hspace{27mm}+(133-129t-14t^2)x^2+(49+14t)x^3+49tx^4
\bigr],\\[1mm]
S_1={}&96t^3x^4+316t^3x^3+384t^3x^2+96t^3x-48t^3\\
&-524t^2x^4-1382t^2x^3-1354t^2x^2-432t^2x+24t^2\\
&-49tx^5+313tx^4+1000tx^3+898tx^2+240tx\\
&+49x^5+91x^4-30x^3-72x^2,\\[1mm]
S_2={}&2\bigl[
(-82t^3+45t^2)+(-164t^3+198t^2-195t)x\\
&+(-70t^3+428t^2-392t-240)x^2\\
&+(31t^3+670t^2-427t-500)x^3\\
&+(24t^3+632t^2-415t-330)x^4
+(247t^2-190t-70)x^5\bigr],\\[1mm]
S_3={}&-8tW^2(5t^2+30tx^2+62tx+25t+27x^3+54x^2+25x),\\
S_4={}&-20t(t+x)W^2(t+x^2+2x).
\end{aligned}
\tag{21}
\]

Their expanded monomial counts are 16, 19, 20, 13 and 11; their degrees
are 7, 7, 7, 6 and 6. The coefficients have at most four digits.

For a staged check of (20), put \(U=1-t+t^2\) and use

\[
F_k(U,y,k_+)=\frac{tq}{2W^2}
   (D_0+D_1y+D_2y^2+D_3y^3),
\]

\[
\begin{aligned}
D_0={}&x(1-t)\{1-2t+(-2t^2+9t-1)x+14tx^2+7tx^3\},\\
D_1={}&t-2t^2+(11-22t+8t^2)x
 +(31-68t+30t^2+4t^3)x^2\\
&+(38-95t+56t^2)x^3+(14-38t+24t^2)x^4,\\
D_2={}&-6t^2+(4t-6t^2-20)x+(2t^3+53t-85)x^2\\
&+(8t^2+81t-107)x^3+(2t^2+38t-44)x^4,\\
D_3={}&xWJ.
\end{aligned}
\tag{22}
\]

The first three follow from the four small endpoint derivative identities
in Section 5 of
[the high-ratio shape reduction](NONSHORT_HIGH_RATIO_SHAPE.md):
subtract \(W^2A_0\), \(W^2A_1+20W^2A_0\), and \(20W^2A_1\),
respectively, where \(A_0=tx^2-t^2x^2\) and
\(A_1=2x^2+x-2tx^2-tx\). This is exactly the change of multiplier
from \(4\) to \(7/2-10y\). \(D_3\) is unchanged.
The expanded counts in (22) are 11, 15, 13 and 5; degrees are at most six.

Now set

\[
K=12-24t+7x-24tx,
\]

\[
e_0=9/2-t+7x+(7/2)x^2,\quad
e_1=-10-2t-24x-12x^2,\quad e_2=-t-2x-x^2.
\]

These have 4, 4, 4 and 3 monomials, of degree at most two.
The five identities needed for (20) are precisely

\[
\begin{aligned}
S_0&=24tWD_0+cxKB_0,\\
S_1&=24tWD_1+cxKB_1,\\
S_2&=24tWD_2+cxKB_2+20tpW^2e_0,\\
S_3&=24tWD_3+20tpW^2e_1,\\
S_4&=20tpW^2e_2.
\end{aligned}
\tag{23}
\]

Each is an identity in \(t,x\) only. The product sides have total degree
at most eight before cancellation and fewer than 60 distinct monomials.
Their reduced coefficient polynomials are the 16, 19, 20, 13 and
11 monomials printed in (21). Keep these coefficients opaque when
reassembling the quartic in \(y\).

## 5. Concavity reduces the event variable to two endpoints

The factors show \(S_3,S_4<0\). Also \(S_2<0\).
For the latter, the coefficients of \(x^2,x^3,x^4,x^5\) in \(S_2/2\)
are negative: their positive parts are bounded respectively by
\(61,96,91\), and \(247t^2\), while their displayed negative parts
already dominate these bounds.
For its constant and linear terms, use

\[
-82t^3+45t^2\le\frac{135}{8}t,\qquad
-164t^3+198t^2-195t<-120t.
\]

Since \(x\ge1/4\), their sum is less than \(-105t/8\).
This proves \(S_2<0\), and therefore

\[
S_{yy}=2S_2+6S_3y+12S_4y^2<0\qquad(y\ge0).
\tag{24}
\]

At \(y=0\), every coefficient in the braces of \(S_0\) is positive.
In particular

\[
84-60t-72t^2\ge411/8,\qquad
133-129t-14t^2\ge2645/32,
\]

and \(24t(1-2t)>0\). Thus \(S(t,x,0)>0\).
By (3), (24), and concavity, only \(S(t,x,b(t))>0\) remains.

## 6. The other endpoint is a sum of positive univariate coefficients

There is the coefficientwise identity

\[
\boxed{
8000S(t,x,b(t))=
t^2(18-37t)Z_0(t)+txZ_1(t)
 +x^2 Z_2(t)+x^3 Z_3(t)+x^4 Z_4(t)+x^5 Z_5(t).
}
\tag{25}
\]

The six polynomials are

\[
\begin{aligned}
Z_0={}&50653t^4-128686t^3-63196t^2+102768t-22800,\\
Z_1={}&-3748322t^6+5723789t^5+36108744t^4-41328112t^3\\
 &+3467160t^2+7369680t-1773600,\\
Z_2={}&-1874161t^7-7445991t^6+84864310t^5-51268680t^4\\
 &-31421920t^3+12717104t^2+9023904t-2956800,\\
Z_3={}&-9370805t^6+59999163t^5+27973184t^4-104352976t^3\\
 &+24356048t^2+18664240t-5632000,\\
Z_4={}&-1874161t^6+9621332t^5+69857480t^4-112663832t^3\\
 &+36734704t^2+7372048t-3229600,\\
Z_5={}&-1874161t^5+28113784t^4-42193912t^3+18455680t^2\\
 &-783488t-554400.
\end{aligned}
\tag{26}
\]

Their counts are 5, 7, 8, 7, 7 and 6 monomials; degrees are 4, 6, 7,
6, 6 and 5. Their coefficients have at most nine digits.
To verify (25), collect the coefficient of each \(x^i\) in (21), and
substitute \(y=b(t)\) **separately in that coefficient**. The six
resulting identities are univariate in \(t\), have degree at most seven
and at most eight monomials. A single expanded two-variable identity
for the whole of (25) is unnecessary and is outside the intended
verification interface.

Each \(Z_i\) is strictly concave on \(1/3\le t\le3/8\). All six
second-derivative polynomials are printed here:

\[
\begin{aligned}
Z_0''={}&607836t^2-772116t-126392,\\
Z_1''={}&-112449660t^4+114475780t^3+433304928t^2\\
 &-247968672t+6934320,\\
Z_2''={}&-78714762t^5-223379730t^4+1697286200t^3\\
 &-615224160t^2-188531520t+25434208,\\
Z_3''={}&-281124150t^4+1199983260t^3+335678208t^2\\
 &-626117856t+48712096,\\
Z_4''={}&-56224830t^4+192426640t^3+838289760t^2\\
 &-675982992t+73469408,\\
Z_5''={}&-37483220t^3+337365408t^2-253163472t+36911360.
\end{aligned}
\tag{27}
\]

These have 3, 5, 6, 5, 5 and 4 monomials, degrees at most five, and
coefficients of at most ten digits. Bound a positive term \(ct^r\)
above by \(c(3/8)^r\), and a negative term above by \(c(1/3)^r\).
Applied to the explicitly printed polynomials (27), the resulting
six upper bounds are, respectively,

\[
-\frac{4772593}{16},\quad
-\frac{35043346471}{3456},\quad
-\frac{100280584499}{5184},\quad
-\frac{183096838513}{3456},\quad
-\frac{21185620079}{864},\quad
-\frac{76826929}{54}.
\tag{28}
\]

Every one is negative. No unspecified coefficient or omitted sign
claim is used in this comparison.

The endpoint evaluations are

\[
\begin{aligned}
Z_0(1/3)&=23767/81,& Z_0(3/8)&=4368669/4096,\\
Z_1(1/3)&=1260517/729,& Z_1(3/8)&=5803119123/131072,\\
Z_2(1/3)&=12297464/2187,& Z_2(3/8)&=317312677677/2097152,\\
Z_3(1/3)&=7377196/729,& Z_3(3/8)&=68480296091/262144,\\
Z_4(1/3)&=26323979/729,& Z_4(3/8)&=54283641239/262144,\\
Z_5(1/3)&=2843615/243,& Z_5(3/8)&=2100924669/32768.
\end{aligned}
\tag{29}
\]

They are all positive; the largest integer has twelve digits.
Concavity therefore gives \(Z_i(t)>0\) throughout the interval.
Also \(18-37t\ge33/8>0\). Every summand in (25) is nonnegative,
and its constant term is strictly positive. Hence
\(S(t,x,b(t))>0\).

Sections 5--6 prove \(S>0\) on the entire domain (2).
Equations (19)--(20) prove the shape monotonicity (1).

## Validation and remaining obligation

The coefficient identities (15)--(17), (22)--(23), the six separate
univariate identities making up (25), and the evaluations (28)--(29)
were checked with exact rational symbolic arithmetic. Their displayed
identities and inequalities are the proof; the computation is only a
transcription check. No Lean compilation, Lake, typechecking or CI
was run, and no Lean timing or memory reduction is claimed.

The first-priority unit-shape claim

\[
G_n(t,x,q,1)>0
\]

is still open under the requested identity budget. Only after that
claim is proved can the negative actual necessary condition in
Section 1 and the positive shape derivative in (1) be combined into
a replacement for fh_LGA_core's two old endpoint signs.
