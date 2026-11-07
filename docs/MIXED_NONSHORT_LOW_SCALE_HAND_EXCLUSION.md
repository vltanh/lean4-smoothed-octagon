# Hand exclusion of the common nonshort low-scale domain

Date: 2026-11-07 UTC. Complete hand proof, accepted in the
[independent low-scale audit](MIXED_NONSHORT_LOW_SCALE_HAND_AUDIT.md).

This note proves that the actual smaller-nonshort window cannot have
\(a\le1/2\). The proof uses explicit logarithm inequalities and polynomial
identities with all required signs displayed. It uses no interval cover,
numerical minimum, runtime certificate, or Casimir bound at an artificial
point.

The common-order reduction is
[MIXED_NONSHORT_REVERSE_HAND_EXCLUSION](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
Section 5. The separate high-ratio derivative lemma is
[MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE](MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE.md).
Both are hand arguments. The computational low-\(a\) theorem is not a
premise of this note.

## 1. Two scalar comparison faces

Normalize the actual margins as in
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md):
\[
t=\frac a{a+c},\qquad x=\frac{d-a}{a+c},\qquad
k=\frac{a^2+4}{(a+c)^2},\qquad
W=1+x,\quad X=x+2,\quad p=t+x,\quad Y=x(x+2).
\]
The exact incoming norm is
\[
v=1+\frac{(1-t)^2}{W}
       -(1-t)\frac{\log W}{x}.
\]
The retained actual inequalities include
\[
v<U(t)=1-t+t^2,\qquad
v>g:=1-\frac{(1-t)p}{W^2},\qquad
v\ge F_{p/W}(q),\qquad q>1,
\]
where
\[
F_\eta(q)=1+\eta^2q-\eta\frac{q\log q}{q-1}.
\]
The normalized incident-upper residual \(N_k\) is strictly negative
at the actual data and is strictly increasing in \(k\), with
\(t,x,q,v\) fixed.

Suppose \(a\le1/2\). The accepted
[low-scale domain reduction](MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION.md)
gives
\[
0<t<7/20,\qquad k\ge\max\{1,17t^2\}.
\]
The common-order corollary gives
\[
k<2t+x.
\tag{1}
\]
The common duration bound \(d/c<7/3\), proved in the
[exact secant comparison](MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON.md),
gives \(x<7/3-(10/3)t<7/3\).

Use the rational secant upper bound
\[
\bar v=1+\frac{(1-t)^2}{W}
 -\frac{2(1-t)}X\left(1+\frac{x^2}{3X^2}\right)>v.
\]
The exact identity
\[
\bar v-g=\frac{(1-t)x}{W^2}\{T(x)-t\},\qquad
T(x)=\frac{-2x^3-x^2+10x+12}{3X^3}
\tag{2}
\]
therefore gives \(t<T(x)\). Also
\[
T'(x)=-\frac{11x^2+24x+16}{3X^4}<0,\qquad T(1)=19/81<1/4.
\]

If \(t\le1/4\), lower the shape to \(k=1\). By (1),
\(x>1-2t\ge1/2\). It suffices to exclude
\[
k=1,\quad 0<t\le1/4,\quad
1/2\le x<7/3,\quad x\ge1-2t,\quad t<T(x).
\tag{3}
\]
The weak inequalities enlarge the domain.

If \(t\ge1/4\), lower the shape to
\[
k_h=2t+\frac12.
\]
This is legitimate because
\(17t^2-(2t+1/2)>0\) for \(t\ge1/4\): its value at \(1/4\) is
\(1/16\), and its derivative is \(34t-2>0\).
Equation (1) also gives \(x>17t^2-2t\ge9/16>1/2\).
By (2) and \(T(1)<1/4\), one has \(x<1\).
It suffices to exclude the rectangle
\[
k=k_h,\qquad 1/4\le t\le7/20,\qquad 1/2\le x\le1.
\tag{4}
\]

In both comparisons the exact incoming norm and its missing-control
floor are unchanged. No condition on a new outgoing switch and no
Casimir cap is transported. The strict increase of \(N_k\) gives a
negative residual at the selected lower shape if an actual point exists.

## 2. A rational quartic lower bound

For either shape in (3)--(4), put
\[
B=k+2tx+x^2,\qquad Z=qB/W,
\]
\[
H_0=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+H_0Y+vY^2}{B^2},
\]
\[
R=(1-t)+Z-\frac{p^2}W-\frac{p^2}Z+\frac{p^3}B
-p\log q-Wv-Zw_U+\frac{p(H_0+2vY)}B,\qquad N_k=tBqWR.
\]

The elementary logarithm bounds are
\[
\log W>\frac{2x}{X}+\frac{2x^3}{3X^3},\qquad
\log q<L_+(q):=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
The first is obtained by integrating
\(1/(1-z^2)>1+z^2\). For the second,
\[
(L_+-\log q)'=\frac{(q-1)^4}{6q^2(q+1)^2}>0,\qquad
L_+(1)-\log1=0.
\]
Consequently
\[
F_\ell:=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)}
<F_{p/W}(q)\le v<\bar v.
\tag{5}
\]

Let \(\bar N_k\) be \(N_k\) with \(v=\bar v\) and \(\log q=L_+\).
Write \(y=q-1\), and define
\[
I_0=k+tx+tW(k-2t),\qquad I_1=kX+txX^2,\qquad
A=xq(I_0+I_1y).
\]
Direct differentiation gives \(N_v=-A\).
Here \(I_0,I_1>0\): on the unit face \(k-2t\ge1/2\), and on
the other face \(k_h-2t=1/2\). The log coefficient of \(N_k\) is
\(-tpqWB<0\). Thus
\[
N_k>\bar N_k>
\bar N_k-A(\bar v-F_\ell).
\tag{6}
\]
Define the rational quartic
\[
Q=6(q+1)W^2\{\bar N_k-A(\bar v-F_\ell)\}
 =P_0+P_1y+P_2y^2+P_3y^3+P_4y^4.
\tag{7}
\]
All its coefficient denominators divide \(X^3\). Therefore \(Q>0\)
contradicts the required \(N_k<0\).

Here are explicit formulas for the five coefficients, to specify the
algebra independently of coefficient extraction. In the following
formulas \(v=\bar v\) and \(H_0\) has the same substitution. Set
\[
\begin{aligned}
C&=t(B^2-k^2+kt-t^2-H_0Y-vY^2),\\
D&=t\{BW(1-t)-Bp^2+Wp^3-BW^2v+Wp(H_0+2vY)\},\\
E&=tp^2W^2,\qquad L=tBWp,
\end{aligned}
\]
\[
\begin{aligned}
c_0&=12(C+D-E),&
c_1&=30C+18D-6E-12L,\\
c_2&=24C+6D-12L,&
c_3&=6C-L,
\end{aligned}
\]
\[
G_0=12W^2(v-g),\qquad
G_1=6W^2(v-1)-18p^2+12pW,\qquad M=p(6p-W).
\]
Then
\[
\begin{aligned}
P_0&=W^2c_0-xI_0G_0,\\
P_1&=W^2c_1-x\{(I_0+I_1)G_0+I_0G_1\},\\
P_2&=W^2c_2-x\{I_1G_0+(I_0+I_1)G_1-I_0M\},\\
P_3&=W^2c_3-x\{I_1G_1-(I_0+I_1)M\},\\
P_4&=xI_1M.
\end{aligned}
\tag{8}
\]
Indeed
\[
\bar N_k=Cq^2+Dq-E-LqL_+,\qquad
6(q+1)W^2(v-F_\ell)=G_0+G_1y-My^2.
\]
These two identities immediately give (8).

## 3. Six signs suffice for every first-event factor

Define
\[
\begin{aligned}
J_0&=P_0,&J_1&=P_1+2P_0,&J_2&=P_2+48P_0,\\
J_3&=P_3+4P_2,&J_4&=P_3-P_0,&J_5&=P_4-P_0.
\end{aligned}
\tag{9}
\]
We shall prove \(J_i>0\) on both comparison domains.

Here is the complete univariate implication. Put
\(b=-P_2/P_0\). The signs imply
\[
b<48,\quad P_1/P_0>-2,\quad
P_3/P_0>\max\{1,4b\},\quad P_4/P_0>1.
\]
If \(b\le0\), the lower bound is
\(1-2y+y^3+y^4\).
For \(0\le b\le48\), minimize the affine lower bound in \(b\)
on each side of \(b=1/4\). Its minimum is attained at
\(b=0,1/4,\) or \(48\).
The case \(b=0\) is larger than the case \(b=1/4\).
Thus only the following two polynomials need be checked:
\[
f(y)=1-2y-\frac14y^2+y^3+y^4,
\qquad
g(y)=1-2y-48y^2+192y^3.
\]
(The nonnegative \(y^4\) term was dropped in the second case.)
For all \(y\ge0\),
\[
\begin{aligned}
f(y)
&=\frac4{81}+\frac5{27}(y-\tfrac23)
 +\left(\frac{29}{12}+\frac73y+y^2\right)(y-\tfrac23)^2\\
&\ge\frac4{81}-\frac{25}{7047}
 =\frac{323}{7047}>0,\\
g(y)
&=\frac29-2(y-\tfrac16)
 +(16+192y)(y-\tfrac16)^2\\
&\ge\frac29-\frac1{16}=\frac{23}{144}>0.
\end{aligned}
\tag{10}
\]
This proves \(Q>0\) once the six signs in (9) are established.

## 4. Four normalized polynomials on the unit shape

In this section \(k=1\). The formulas (8) have the factorizations
\[
J_0=\frac{4(1-t)x^2}{X^3}F_0,\qquad
J_1=\frac{2(1-t)x}{X^3}F_1,\qquad
J_2=\frac{F_2}{X^3},\qquad
J_3=\frac{F_3}{X^3}.
\tag{11}
\]
These equations define four polynomials \(F_i(t,x)\);
substitution in (8) cancels the indicated factors exactly.
All multipliers in (11) are positive on the required domain.

We first prove the derivative comparison
\[
-\partial_tF_i(t,x)\ge-\partial_tF_i(1/4,x)>0
\quad
(0\le t\le1/4,\ 1/2\le x\le7/3).
\tag{12}
\]
Appendix A gives each derivative as a complete polynomial identity.
Here is its sign proof. Set
\[
s=1-4t\in[0,1],\qquad z=2x-1\in[0,11/3].
\]
For \(F_0,F_2\), every displayed derivative coefficient is positive.
For \(F_1\), the only negative term is in its constant-in-\(s\)
coefficient, where
\[
26z^6-4z^7\ge(34/3)z^6\ge0.
\]
All coefficients of the positive powers of \(s\) are nonnegative.

For \(F_3\), the constant-in-\(s\) coefficient is positive because
\[
15744z^2+5856z^3+591z^4+20z^5
\le\frac{150764185}{243}<919286.
\]
This absorbs its four negative terms into \(919286z^4\).
The only other negative terms are the first four terms of its
\(s^3\) coefficient. Since \(s^3\le s\), they are absorbed into
the \(s\) coefficient: the first four remaining coefficients are
\[
94878,\quad 2136096,\quad5129784,\quad5077432,
\]
all positive, and every further coefficient is displayed as positive.
Thus in every row the full derivative is at least its value at
\(s=0\), and that value is positive. This proves (12).

Integrating (12) gives the useful tangent lower bound
\[
F_i(t,x)\ge
F_i(1/4,x)+(1/4-t)\{-\partial_tF_i(1/4,x)\}.
\tag{13}
\]

## 5. Positivity of the four unit-shape polynomials

### 5.1 The interval \(1/2\le x\le1\)

Direct substitution in (11) gives
\[
F_0(1/4,x)=\frac3{32}b_0(x),\quad
F_1(1/4,x)=\frac1{32}b_1(x),\quad
F_2(1/4,x)=\frac3{64}b_2(x),
\]
\[
F_3(1/4,x)=\frac1{64}
 \{b_3(x)+804x^8+160x^9\},
\tag{14}
\]
where
\[
b_0=-24+36x+58x^2-x^3-23x^4-6x^5,
\]
\[
b_1=48-768x+1280x^2+1788x^3
 -647x^4-1279x^5-354x^6-8x^7,
\]
\[
b_2=32+56x-8188x^2+10114x^3+16565x^4
 -2618x^5-8919x^6-2452x^7-60x^8,
\]
\[
b_3=496+1184x-13536x^2+12140x^3+27561x^4
 -957x^5-11896x^6-2456x^7.
\]

First \(b_0\ge-24+36x+28x^2\ge1\), since \(x\le1\)
and the last quadratic is increasing for \(x\ge1/2\).

For each of \(b_1,b_2,b_3\), the function \(b_i'(x)/x^2\)
is strictly concave on \([1/2,1]\).
The three exact second derivatives are respectively
\[
\frac{-4608+5120x}{x^4}-12790-12744x-672x^2,
\]
\[
\frac{336-32752x}{x^4}
 -26180-321084x-205968x^2-9600x^3,
\]
\[
\frac{7104-54144x}{x^4}-9570-428256x-206304x^2.
\tag{15}
\]
The last two are visibly negative.
For the first, \((-4608+5120x)/x^4\) is increasing on this interval
and at most \(512\), so the first expression is also negative.

The following exact endpoint data complete the argument:
\[
\begin{array}{c|ccc}
 &b_i(1/2)&b_i(1)&b_i'(1/2)\\ \hline
b_1&243/2&60&17001/16\\
b_2&72&4530&39789/8\\
b_3&22691/32&12536&123765/16.
\end{array}
\tag{16}
\]
A concave function positive at the left endpoint can pass from
positive to negative at most once. Applying this to \(b_i'/x^2\)
shows that \(b_i\) increases and then possibly decreases.
Its minimum is therefore at an endpoint, and (16) proves \(b_i>0\).
Equations (12)--(14) prove \(F_i(t,x)>0\) for every
\(0\le t\le1/4,\ 1/2\le x\le1\).
No turn-floor hypothesis is needed for these base signs.

### 5.2 The interval \(1\le x\le7/3\)

Here \(t<T(x)<1/4\). Define
\[
H_i(x)=F_i(1/4,x)
 +(1/4-T(x))\{-\partial_tF_i(1/4,x)\}.
\]
Then (13) gives \(F_i(t,x)>H_i(x)\).
The exact tangent identities are
\[
H_0=\frac{h_0}{48X^3},\qquad
H_1=\frac{xh_1}{48X^3},\qquad
H_2=\frac{h_2}{192X^3},\qquad
H_3=\frac{h_3}{192X^3},
\tag{17}
\]
with
\[
h_0=-576-1536x+432x^2+3592x^3+3136x^4
 +846x^5+22x^6+70x^7+39x^8,
\]
\[
h_1=-3264-18240x-17088x^2+11184x^3+27452x^4
 +18376x^5+6068x^6+872x^7-185x^8-100x^9,
\]
\[
\begin{aligned}
h_2={}&4608-192x-199488x^2-1462352x^3-1100096x^4\\
&+1581228x^5+2409300x^6+934137x^7
 -9606x^8-46243x^9+3512x^{10}-408x^{11},
\end{aligned}
\]
\[
\begin{aligned}
h_3={}&25344+51392x+183232x^2-561552x^3-1461360x^4
 -287940x^5\\
&+1611992x^6+1682639x^7+609643x^8
 -3828x^9-63320x^{10}-16312x^{11}-1280x^{12}.
\end{aligned}
\]

Every sign has a short term comparison.
For \(h_0\), the first four terms are at least \(1912\),
and all later terms are positive.
For \(h_1\), use \(x\ge1\) on its lower terms and \(x\le7/3\)
on its last two negative terms to get
\[
h_1\ge7920+136x+10364x^2+\frac{102341}{27}x^6>0.
\]
Indeed the coefficient charged to \(6068x^6\) is at most
\[
185(7/3)^2+100(7/3)^3=\frac{61495}{27}<6068.
\]
Similarly,
\[
h_2\ge1228400x^5+\frac{17492264}{27}x^7>0.
\]
The first coefficient comes from
\(1581228+2409300-(192+199488+1462352+1100096)=1228400\).
The negative high-degree terms cost at most
\[
9606(7/3)+46243(7/3)^2+408(7/3)^4
 =\frac{7729435}{27}<934137
\]
units of \(x^7\).
Finally,
\[
h_3\ge983779x^6+\frac{875143}{81}x^8>0.
\]
Here
\(1611992+1682639-(561552+1461360+287940)=983779\),
and the high-degree charge is
\[
3828(7/3)+63320(7/3)^2+16312(7/3)^3+1280(7/3)^4
 =\frac{48505940}{81}<609643.
\]
This proves all four signs in (11) on the full unit-shape domain (3).

## 6. The remaining two coefficient comparisons

Still let \(k=1\).
Appendix B gives the exact derivative identity proving
\[
\partial_t(P_3-P_0)>0
\quad(0\le t\le1/4,\ x\ge1/2).
\tag{18}
\]
For \(1/2\le x\le1\), the order condition in (3) gives
\(t\ge(1-x)/2\), and the exact lower-face value is
\[
(P_3-P_0)((1-x)/2,x)
 =\frac{W^3}{4X^3}
 \{16+112x+136x^2+16x^3-55x^4-15x^5
                  +23x^6+20x^7+6x^8\}.
\tag{19}
\]
The brace is at least \(16+112x+66x^2>0\) when \(x\le1\).
For \(x\ge1\), compare instead with \(t=0\):
\[
(P_3-P_0)(0,x)=\frac{x^2}{X^3}
 \{-120-20x+270x^2+277x^3+100x^4+11x^5\}>0.
\tag{20}
\]
The first three terms are already at least \(130\) for \(x\ge1\).
Thus \(J_4>0\).

For \(J_5\), no additional coefficient expansion is necessary.
On any interval from \(0\) to a point of (3), Section 5 gives
\(F_0>0\) and Section 4 gives \(\partial_tF_0<0\).
Formula (11) therefore makes \(P_0\) strictly decreasing in \(t\).
Meanwhile
\[
P_4=x(X+txX^2)(t+x)(6t+5x-1)
\]
is strictly increasing in \(t\) for \(x\ge1/2\).
At \(t=0\), exact subtraction yields
\[
(P_4-P_0)(0,x)=\frac{x^2}{X^3}
 \{5x^5+39x^4+84x^3+56x^2-16x-16\}>0.
\tag{21}
\]
The brace is \(99/32\) at \(x=1/2\), and its derivative is
\[
25x^4+156x^3+252x^2+112x-16>0
\qquad(x\ge1/2).
\]
Hence \(J_5>0\).

The algebraic evaluations at \(t=0\) in (20)--(21) are values of the
continuous rational coefficient extensions in (8).
They are not assigned a geometric or switching interpretation.
The factors \(tH_0\) in (8) already remove the apparent \(1/t\).

Sections 4--6 establish every sign in (9) on (3).
They also establish all six base signs at
\(t=1/4,\ 1/2\le x\le1\), without requiring (2) there.

## 7. The high-ratio face and the actual contradiction

On \(k=k_h=2t+1/2\), the
[proved high-ratio derivative lemma](MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE.md)
states
\[
\frac{d}{dt}J_i(t,x)>0
\quad(1/4\le t\le7/20,\ 1/2\le x\le1),
\qquad i=0,\ldots,5.
\]
At \(t=1/4\), \(k_h=1\), so the six base signs just proved apply.
Every \(J_i\) is therefore positive on (4) as well.

The comparison in \(t\) moves only a proved rational polynomial
inequality. It makes no claim that an exact incoming norm or its
missing-control floor is preserved when \(t\) changes.
The actual floor is used in (5)--(6) at the original \(t,x,q\),
after the polynomial positivity has been established.

By Section 3, \(Q>0\) on both selected shape faces.
Equation (6) then gives \(N_k>0\) at the selected lower shape,
contradicting the negative residual inherited by shape monotonicity
from an actual low-scale window.
The assumption \(a\le1/2\) is impossible. Consequently
\[
\boxed{a>1/2}
\]
for every actual smaller-nonshort window in the hand domain.

The proof uses the common incoming conditions and the common-order
corollary. It is independent of which actual switch follows the first
forward continuation, and it transfers no artificial Casimir cap.

## Appendix A. Complete derivative identities for (12)

Use
\[
\operatorname{pol}(a_0,\ldots,a_n)=\sum_{j=0}^n a_jz^j.
\]
With \(s=1-4t\), \(z=2x-1\), the identities are
\[
-\partial_tF_i
 =\frac1{\rho_i}\sum_{j=0}^3D_{ij}(z)s^j,\qquad
(\rho_0,\rho_1,\rho_2,\rho_3)=(128,256,1024,1024).
\tag{22}
\]
The derivative is with respect to the original \(t\).
Rows not listed are zero. These identities and the endpoint
identities (14), (17) follow by substituting (8) into (11);
all their coefficients are displayed here.

### Polynomial \(F_0\)

\[
D_{00}=\operatorname{pol}(1737,3492,1732,422,67,6).
\]
\[
D_{01}=\operatorname{pol}(7836,8202,3276,688,88,6).
\]
\[
D_{02}=\operatorname{pol}(3375,3150,1080,162,9).
\]

### Polynomial \(F_1\)

\[
D_{10}=\operatorname{pol}(31059,95463,103944,47570,10667,1131,26,-4).
\]
\[
D_{11}=\operatorname{pol}(69852,176766,161946,75928,21056,3550,330,12).
\]
\[
D_{12}=\operatorname{pol}(10125,33075,25290,8046,1161,63).
\]

### Polynomial \(F_2\)

\[
D_{20}=\operatorname{pol}(712125,3018882,4660402,3280502,1091800,189470,19702,1322,3).
\]
\[
D_{21}=\operatorname{pol}(2544954,8488868,10812816,6806036,2361044,497932,66464,4796,66).
\]
\[
D_{22}=\operatorname{pol}(2174013,6472242,7348218,4058022,1220256,216174,23886,1530,27).
\]
\[
D_{23}=\operatorname{pol}(409500,1228200,1357140,697776,181380,23208,1164).
\]

### Polynomial \(F_3\)

\[
D_{30}=\operatorname{pol}(222345,1641168,3177744,2594168,919286,109420,-15744,-5856,-591,-20).
\]
\[
D_{31}=\operatorname{pol}(193878,2309496,5219064,5091304,2554500,719784,115544,9848,342).
\]
\[
D_{32}=\operatorname{pol}(255141,575244,987096,969072,519702,161052,29112,2856,117).
\]
\[
D_{33}=\operatorname{pol}(-99000,-173400,-89280,-13872,1608,648,48).
\]

## Appendix B. The increasing comparison in (18)

For \(s=1-4t\in[0,1]\), \(z=2x-1\ge0\), direct differentiation
of (8) gives
\[
1024X^3\partial_t(P_3-P_0)
 =E_0(z)+sE_1(z)+s^2E_2(z)+s^3E_3(z),
\tag{23}
\]
with the four explicit polynomials below.
Every coefficient of \(E_1\) is negative; \(E_3\) has positive
coefficients; and the only negative coefficients of \(E_2\) are
its last four. Since \(0\le s\le1\), the right side of (23) is
at least
\[
\operatorname{pol}(190599,435842,342674,149042,118708,
                  81456,28616,5408,516,20)>0.
\tag{24}
\]
This lower polynomial is exactly \(E_0+E_1\) plus the negative
part of \(E_2\). Thus no sign is omitted in (18).

\[
E_0=\operatorname{pol}(511785,1471494,1829902,1349526,680324,237046,54442,7706,603,20).
\]

\[
E_1=\operatorname{pol}(-321186,-1035652,-1487228,-1200484,-561616,-154444,-24644,-2124,-78).
\]

\[
E_2=\operatorname{pol}(83133,288522,313878,143838,26004,-1146,-1182,-174,-9).
\]

\[
E_3=\operatorname{pol}(18000,43800,39960,17904,4224,504,24).
\]
