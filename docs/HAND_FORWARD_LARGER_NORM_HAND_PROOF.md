# The larger-neighbor forward norm is below 49/64

Date: 2026-11-07 UTC. Complete hand derivation, accepted in the
[independent scalar audit](HAND_FORWARD_NORM_AUDIT.md).

The norm here is the actual norm adjacent to the larger neighboring
margin at an all-forward minimum. In the centered notation, the result
is delta v<1/64. Together with the sum bound delta u+delta v<1/35,
the [conditional Casimir theorem](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md)
gives the strict forward contradiction.

This proof uses exact differentiation, two elementary logarithm bounds
and explicit short bounds on polynomial coefficients. Every coefficient
used is displayed in the appendix. No numerical minimum, interval cover
or executable sign test is a premise.

## 1. Concavity leaves two tangent values on the symmetric face

By Section 4 of
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md),
it suffices to prove

\[
\mathcal E_v(h)=r(h)-n(h)L(z,h)-m(h)/64<0
\tag{1}
\]

on the equal-neighbor domain

\[
1\le z\le4/3,\quad 1+6z/5\le U<3,\quad
I:=\frac{(1+z)^2}{z^2+U}\le h\le
h_c:=\frac{(1+z)(5U-2-3z)}{3(z^2+U)}.
\tag{2}
\]

The functions r,n,m,L are the exact ones displayed in that note.
The exterior-factor concavity proof in
[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) applies unchanged to (1):
the right norm enters through a multiple of m, which is affine in h.
Thus E_v is concave on [I,h_c]. Its tangent at I gives

\[
\mathcal E_v(h)\le
\mathcal E_v(I)+(h-I)\mathcal E_v'(I).
\]

It is therefore enough to prove the two strict signs

\[
E:=\mathcal E_v(I)<0,\qquad
T:=\mathcal E_v(I)+(h_c-I)\mathcal E_v'(I)<0.
\tag{3}
\]

This includes the collapsed interval I=h_c.

## 2. A small rectangle and two logarithmic coefficients

Put

\[
a=\frac{z-1}{z+1},\quad b=1-a,\quad t=I-1,\quad
c=1-aI,\quad D=(1+a)I-1.
\]

The necessary domain is contained in the rectangle

\[
0\le a\le1/7,\qquad 0<t\le1/4.
\tag{4}
\]

The upper bound on I follows from
\(5(z^2+1+6z/5)-4(z+1)^2=(z-1)^2\).
The actual strict scale U<3 makes t>0. In these coordinates,

\[
S=1+z=\frac2b,\quad z=\frac{1+a}{b},\quad
Z=\frac{S^2}{I},\quad K=\frac{S^2c}{I},\quad q=\frac Ic,
\]
\[
H_c=h_c-1=
\frac{2(1+a)-t(5+3a+2a^2)/b}{3},
\quad
h_c-I=\frac{2[1-a^2-(4+a^2)t]}{3b}.
\tag{5}
\]

In particular b>=6/7, c>=23/28, and all denominators below are positive.

After collecting the logarithms in E, its coefficient of log I is
\(C_0/b^2\), where

\[
\begin{aligned}
C_0={}&1-2t-t^2+a(3+3t)\\
&-a^2(5+6t+3t^2)+a^3(1+t).
\end{aligned}
\tag{6}
\]

After collecting them in T, its coefficient of log I is
\(C_c/(3b^3)\), where

\[
\begin{aligned}
C_c={}&1+5t^2+a(14-17t+3t^2)
+a^2(-28-5t+17t^2)\\
&+a^3(10+13t+9t^2)+a^4(3+9t+6t^2).
\end{aligned}
\tag{7}
\]

Both coefficients are positive on the whole rectangle. For (6),
\(1-2t-t^2\ge7/16\) and

\[
3+3t-a(5+6t+3t^2)
\ge3-\frac{107}{112}>0.
\]

For (7), the two possibly competing terms satisfy

\[
a(14-17t+3t^2)+a^2(-28-5t+17t^2)
\ge\frac{39}{4}a-\frac{117}{4}a^2
\ge\frac{39}{7}a.
\]

All other terms in (7) are nonnegative, with constant term one.

The coefficients of log c are respectively

\[
c(1+St)>0,\qquad c(1+SH_c)>0.
\tag{8}
\]

For the second sign it is enough to use the actual domain H_c>=t>0.
Equations (6)--(8) are the only sign information needed to replace the
logarithms in both tangent values.

## 3. Rational upper bounds and their exact numerators

The following two elementary estimates have the correct upper-bound
direction:

\[
\log I\le\frac{I-I^{-1}}2-\frac{t^3}{3I(I+1)},
\qquad
\log(1-aI)\le-aI-\frac{a^2I^2}{2}-\frac{a^3I^3}{3}.
\tag{9}
\]

The first is the bound
\(f(I)\ge t^3/[3I(I+1)]\), proved by a displayed nonnegative
derivative in Section 2 of
[HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md).
The second follows by integrating
\(1/(1-s)\ge1+s+s^2\) from zero to aI.

Apply (9) after the logarithmic terms have been combined as in
(6)--(8). Ordinary collection gives the two upper bounds

\[
\boxed{
E\le\frac{N_0(a,t)}{192b^3I(I+1)},\qquad
T\le\frac{N_c(a,t)}{576b^4I^2(I+1)}.
}
\tag{10}
\]

Here

\[
N_0(a,t)=\sum_{j=0}^7 A_j(t)a^j,\qquad
N_c(a,t)=\sum_{j=0}^8 B_j(t)a^j,
\tag{11}
\]

and all seventeen coefficient polynomials are displayed in the appendix.
Sections 4--5 prove their signs by elementary estimates on the rectangle;
the number of coefficients is not a sign premise.

For clarity, the identities in (6)--(11) can be checked without
reconstructing a PMP system. The exact scalar expression (1) has the form

\[
\mathcal E_v(h)=R_{\rm rat}(h)+\alpha(h)\Phi-F(h)f(h),
\]
\[
\alpha(h)=c[1+S(h-1)],\qquad
F(h)=z[1+n_1h/S],\qquad
n_1=\frac{S^2(1-D)}2,
\]
\[
m_0=\frac{SDc}{I},\qquad m_1=S^2c-\frac{Sc^2}{I}.
\]

With H=h-1, y=(1+a)/2, E_1=t-aI+a^2I, and
\(B_1=t-a+a^2I\), its rational part is

\[
\begin{aligned}
R_{\rm rat}(h)={}&
\frac{aE_1t}{2b^2I}(1+SH)
+\frac{HD B_1y}{bI}
+\frac{Ha^2(1+a)c^2}{2b^2I}\\
&-\frac{n_1yaH^2}{2}
+\frac{zDH^2}{2h}
-\frac{m_0+m_1H}{64}.
\end{aligned}
\tag{12}
\]

Finally

\[
\Phi=\frac S2-\frac2S+\frac2K-\frac K8-\log I+\log c.
\tag{13}
\]

Substitute h=I in (12)--(13), or differentiate first for the tangent
value T, and then use (9). Multiplication by the positive denominators
in (10) gives exactly the appendix. This supplies a direct algebraic
verification of the entire scalar calculation.

## 4. The lower-factor value has negative numerator

Separate the constant-in-t part of N0:

\[
P_0(a):=N_0(a,0)
=4a(1-a)^2[-3+3a+16a^2+16a^3-32a^4].
\]

Since a<=1/7,

\[
-3+3a+16a^2+16a^3-32a^4\le-\frac{754}{343},
\]

and therefore

\[
P_0(a)\le-\frac{108576}{16807}a\le-6a.
\tag{14}
\]

The coefficient independent of a satisfies

\[
A_0(t)=t[-24-36t+308t^2+320t^3+64t^4]
\le-\frac{17}{2}t.
\tag{15}
\]

Indeed, in the bracket, the last three terms are at most
\(77t+20t+t\), so the bracket is at most
\(-24+62t\le-17/2\).

For j>=1 set \(R_j(t)=[A_j(t)-A_j(0)]/t\), with its polynomial
extension at zero. The appendix shows R5,R7<=0. Dropping only explicitly
negative terms in the other rows gives the following upper bounds:

| j | Polynomial upper bound for Rj | Upper bound for \(a^{j-1}R_j\) |
| --- | --- | --- |
| 1 | \(18+72t+118t^2+364t^3+224t^4\) | 50 |
| 2 | \(78+42t+90t^3+96t^4\) | 13 |
| 3 | \(110+92t+64t^5\) | 3 |
| 4 | \(266+1718t+3358t^2+3494t^3+2240t^4+832t^5+128t^6\) | 3 |
| 6 | \(2080+5696t+8512t^2+7488t^3+3872t^4+1088t^5+128t^6\) | 1 |

Each bound in the last column follows just by substituting a<=1/7 and
t<=1/4 into a polynomial with nonnegative coefficients. Their sum is 70.
Consequently (14)--(15) imply

\[
N_0(a,t)\le-6a-\frac{17}{2}t+70at.
\]

The two inequalities at<=a/4 and at<=t/7 imply their convex combination

\[
at\le a/12+2t/21.
\]

Thus

\[
\boxed{N_0(a,t)\le-\frac a6-\frac{11t}{6}<0.}
\tag{16}
\]

The strictness follows from t>0. This proves the first sign in (3).

## 5. The cost-endpoint tangent has negative numerator

For every 0<=t<=1/4, the appendix gives

\[
B_5(t)<0,\qquad B_7(t)<0,\qquad B_8(t)<0.
\tag{17}
\]

For B5, discard all negative terms except -1348 and bound the four
positive terms at t=1/4; their sum is less than 20. For B7 the three
positive terms have sum less than one, while its constant term is -576.
Every coefficient of B8 is negative.

### The interval 0<=t<=1/5

On this interval the remaining coefficients have the bounds

\[
\begin{array}{c|rrrrrr}
j&0&1&2&3&4&6\\ \hline
B_j(t)\le&-12&27&312&138&81&6700.
\end{array}
\tag{18}
\]

Here is a short verification of every entry. For B0, dropping its
negative terms of degree at least four leaves
\(-24-60t+456t^2+680t^3\), a convex function. Its maximum over
[0,1/5] is at an endpoint and is at most -308/25<-12.
For B1, the remaining upper bound is
\(-36+186/5+642/25<27\). For B2 use \(264+240/5=312\).
For B3 use \(136+2934/5^5+800/5^6<138\).
For B4 use
\(-312+1208/5+3294/5^2+2406/5^3<81\).
For B6 bound every positive term at 1/5; their sum is less than 6700.
All omitted terms in these comparisons are negative and displayed.

Since a<=1/7, (17)--(18) yield

\[
\begin{aligned}
N_c(a,t)
&\le-12+\frac{27}{7}+\frac{312}{49}+\frac{138}{343}
       +\frac{81}{2401}+\frac{6700}{117649}\\
&=-\frac{150884}{117649}<0.
\end{aligned}
\tag{19}
\]

### The interval 1/5<=t<=1/4

On this interval,

\[
B_0\le-\frac{255}{32},\quad B_1<12,\quad B_2<264,\quad
B_3<0,\quad B_4<234,\quad B_6<9000.
\tag{20}
\]

For B0, its displayed derivative satisfies

\[
B_0'(t)\ge
-60+\frac{912}{5}+\frac{2040}{25}
-\frac{5392}{64}-\frac{13120}{256}-\frac{6528}{1024}
=\frac{497}{8}>0.
\]

Hence its maximum is \(B_0(1/4)=-255/32\).
For B2, \(B_2'(t)\le240-11466/25<0\), and
\(B_2(1/5)<264\).
For B3, use

\[
B_3(t)\le
136-\frac{312}{5}-\frac{2018}{25}-\frac{3718}{125}
+\frac{2934}{1024}+\frac{800}{4096}<0.
\]

For B4, drop all terms of degree at least four and evaluate its positive
terms at 1/4, giving
\(-312+1208/4+3294/16+2406/64<234\).
For B6, evaluating all positive terms at 1/4 gives a sum less than 9000.

To check the one nonmonotone row B1, its second derivative is

\[
B_1''(t)=1284-3444t-72168t^2-157360t^3-85440t^4<-3600.
\]

The last inequality follows already at t=1/5 and strengthens thereafter.
At the rational point p=9/40, direct substitution gives
\[
B_1(p)=\frac{183891267}{16000000}<\frac{23}{2},\qquad
B_1'(p)=\frac{9705459}{3200000}\in(0,4).
\]
Taylor's inequality with the displayed second-derivative bound therefore
gives, for every t in the interval,

\[
B_1(t)\le B_1(p)+B_1'(p)(t-p)-1800(t-p)^2
<\frac{23}{2}+\frac1{450}<12.
\]

This verifies all of (20). Using (17), a<=1/7 and (20),

\[
\begin{aligned}
N_c(a,t)
&\le-\frac{255}{32}+\frac{12}{7}+\frac{264}{49}
                    +\frac{234}{2401}+\frac{9000}{117649}\\
&=-\frac{2608047}{3764768}<0.
\end{aligned}
\tag{21}
\]

Equations (19) and (21) cover the rectangle. They prove the second
sign in (3).

## 6. Actual forward consequence

Both tangent values in (3) are strictly negative, so concavity proves
E_v<0 on the entire symmetric interval. The proved monotonicity in the
larger neighbor transfers this strict sign back to the actual ordered
data. The first stationary row and the genuine left exterior floor
therefore imply

\[
\boxed{\delta v<1/64,\qquad v<49/64.}
\]

No endpoint in this scalar comparison is called a physical trajectory.
The proof uses the actual common-covector equation and the already
accepted whole-period geometric restrictions.

## Appendix: exact numerator identities

The following two finite polynomial identities are the expansions in
(10)--(11). Their signs are proved in Sections 4--5 by the displayed
bounds; checking a coefficient table by execution is not a premise.

### Coefficients of N0

\[
\begin{aligned}
A_{0}(t)={}&-24t-36t^{2}+308t^{3}+320t^{4}\\
&+64t^{5}.
\end{aligned}
\]

\[
\begin{aligned}
A_{1}(t)={}&-12+18t+72t^{2}+118t^{3}\\
&+364t^{4}+224t^{5}.
\end{aligned}
\]

\[
\begin{aligned}
A_{2}(t)={}&36+78t+42t^{2}-70t^{3}\\
&+90t^{4}+96t^{5}.
\end{aligned}
\]

\[
\begin{aligned}
A_{3}(t)={}&28+110t+92t^{2}-130t^{3}\\
&-332t^{4}-64t^{5}+64t^{6}.
\end{aligned}
\]

\[
\begin{aligned}
A_{4}(t)={}&-52+266t+1718t^{2}+3358t^{3}\\
&+3494t^{4}+2240t^{5}+832t^{6}+128t^{7}.
\end{aligned}
\]

\[
\begin{aligned}
A_{5}(t)={}&-192-1824t-5984t^{2}-10176t^{3}\\
&-10144t^{4}-5984t^{5}-1920t^{6}-256t^{7}.
\end{aligned}
\]

\[
\begin{aligned}
A_{6}(t)={}&320+2080t+5696t^{2}+8512t^{3}\\
&+7488t^{4}+3872t^{5}+1088t^{6}+128t^{7}.
\end{aligned}
\]

\[
\begin{aligned}
A_{7}(t)={}&-128-704t-1600t^{2}-1920t^{3}\\
&-1280t^{4}-448t^{5}-64t^{6}.
\end{aligned}
\]

### Coefficients of Nc

\[
\begin{aligned}
B_{0}(t)={}&-24-60t+456t^{2}+680t^{3}\\
&-1348t^{4}-2624t^{5}-1088t^{6}.
\end{aligned}
\]

\[
\begin{aligned}
B_{1}(t)={}&-36+186t+642t^{2}-574t^{3}\\
&-6014t^{4}-7868t^{5}-2848t^{6}.
\end{aligned}
\]

\[
\begin{aligned}
B_{2}(t)={}&264+240t-30t^{2}-3822t^{3}\\
&-9006t^{4}-6662t^{5}-1472t^{6}.
\end{aligned}
\]

\[
\begin{aligned}
B_{3}(t)={}&136-312t-2018t^{2}-3718t^{3}\\
&-334t^{4}+2934t^{5}+800t^{6}-320t^{7}.
\end{aligned}
\]

\[
\begin{aligned}
B_{4}(t)={}&-312+1208t+3294t^{2}+2406t^{3}\\
&-2582t^{4}-9294t^{5}-9664t^{6}-4224t^{7}\\
&-640t^{8}.
\end{aligned}
\]

\[
\begin{aligned}
B_{5}(t)={}&-1348-9378t-23784t^{2}-25044t^{3}\\
&-3332t^{4}+16166t^{5}+15136t^{6}+5824t^{7}\\
&+896t^{8}.
\end{aligned}
\]

\[
\begin{aligned}
B_{6}(t)={}&2024+13140t+36832t^{2}+56440t^{3}\\
&+50136t^{4}+25172t^{5}+6080t^{6}+192t^{7}\\
&-128t^{8}.
\end{aligned}
\]

\[
\begin{aligned}
B_{7}(t)={}&-576-3680t-9760t^{2}-13632t^{3}\\
&-10240t^{4}-3296t^{5}+480t^{6}+640t^{7}\\
&+128t^{8}.
\end{aligned}
\]

\[
\begin{aligned}
B_{8}(t)={}&-128-1344t-5632t^{2}-12736t^{3}\\
&-17280t^{4}-14528t^{5}-7424t^{6}-2112t^{7}\\
&-256t^{8}.
\end{aligned}
\]

