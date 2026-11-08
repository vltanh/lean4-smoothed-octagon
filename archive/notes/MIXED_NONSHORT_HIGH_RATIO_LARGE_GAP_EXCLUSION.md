# Hand exclusion of the high-ratio, large-gap forward case

Date: 2026-11-08 UTC. This proves the remaining high-ratio part of the
nonshort forward gap bound. The low-ratio and upper-shape signs for
the other multiplier are separate lemmas.

Use the unchanged normalized nonshort geometry and notation of
[the large-gap reduction](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md).
In particular c=1-t, p=t+x, W=1+x, Y=x(x+2), J=t+Y,
B=k-t^2+p^2, e=q/W, D=eJ-p>0, E=e^2B+1-2pe>0,
and C_*=tW^2DE^2/e. The incoming norm is v, and N and
T_* are the incident-upper residual numerator and the transported
solved-boundary norm. Actual eligibility gives
\[
N<0,\qquad \mathcal T_*\ge3/4,\qquad F_{p/W}(q)\le v.
\tag{1}
\]

**Theorem.** No actual eligible nonshort forward window satisfies
\[
\frac38\le t<\frac25,\qquad j=2t+x-1\ge\frac1{30}.
\tag{2}
\]

The already proved derivative-floor and swap bounds put such a point in
\[
h=1-2t\in[1/5,1/4],\qquad
1/30\le j\le5h/7,\qquad x=h+j,
\]
\[
1<q\le\frac{1+h+j}{1+2j},\qquad
\frac{29}{4}t^2<k\le1+j.
\tag{3}
\]
The proof below uses positive constant multipliers 4 and 1, keeping
the original incoming floor in the scalar comparison.

## 1. A simpler rational necessary condition

Let
\[
\mathcal H_4=4N+C_*(3/4-\mathcal T_*)+F_{p/W}(q)-v<0.
\]
The exact transport identity gives
\[
\mathcal H_4=(5-Je^2)N+C_*(3/4-\mathcal T_U)+F_{p/W}(q)-v.
\tag{4}
\]
Here T_U is the transported norm at the central incident ceiling.
Temporarily treating v and ell=log q as independent scalar arguments,
the coefficient calculations of the large-gap reduction apply with
alpha=4 and M=1. Its proved bounds Je^2<17/16 and WD/x<=41/24
therefore give
\[
(\mathcal H_4)_v<-
\left(\frac{63}{16}-\frac{41}{24}\right)(-N_v)-1<0,
\qquad (\mathcal H_4)_\ell<0.
\tag{5}
\]
The latter also uses N_ell=-tpBqW<0 and the negative logarithm
coefficient in the original floor. These signs hold for all scalar
v and ell at the fixed geometry.

Use the proved rational bounds
\[
V=1-\frac{cp}{W^2}+\frac{cx}{W^2}\{T_G(x)-t\},
\quad T_G(x)=\frac{90-19x^2}{12(x^2+10x+15)},
\]
\[
L_+=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
F_\ell=1+\frac{p^2q}{W^2}
 -\frac pW\frac{q^2+10q+1}{6(q+1)}.
\]
They satisfy V>v and L_+>log q at actual q>1. Thus the rational
function
\[
\boxed{G_4=(5-Je^2)N(V,L_+)
 +C_*(3/4-\mathcal T_U(V))+F_\ell-V}
\tag{6}
\]
satisfies G_4<0 at every hypothetical actual point in (2).

## 2. This rational residual increases with shape

We prove \((G_4)_k>0\) throughout the part of (3) with 1<=k<=1+j.
First,
\[
U(t)-V=\frac{cx}{W^2}\{1-tW-T_G(x)\}>0.
\tag{7}
\]
Indeed x>=1/5 and T_G decreases, so
T_G(x)<=2231/5112<7/16. Also x<=12h/7 gives
\[
tW\le\frac{(1-h)(1+12h/7)}2
\le\frac{361}{672}<\frac{11}{20}.
\]
The middle bound follows by completing the square in 5h-12h^2.
Hence the brace in (7) is greater than 1/80.

Let F_4 denote the first two terms of (4), before scalar substitution.
The floor term in (6) is independent of k. Differentiating the
coefficient estimate used for (5) gives
\[
(F_4)_{kv}<-
\left(\frac{63}{16}-\frac{41}{24}\right)A_k<0,
\quad A_k=-N_{kv}\ge xeW>0.
\tag{8}
\]
In detail the possible positive transport contribution is at most
W^2De, which is at most (WD/x)A_k. Also
\((F_4)_{k\ell}=(5-Je^2)(-tpqW)<0\).
Because L_+<q-1 for q>1, (7)--(8) imply
\[
(G_4)_k>(F_4)_k(U(t),q-1).
\tag{9}
\]
Both sides have the continuous interpretation at q=1, where (7)
still supplies the strict comparison.

The quadratic coefficient of F_4 in k is -tW^2De^3/4<0, as in
the original ratio reduction. Thus its k derivative decreases with k,
and the right side of (9) is bounded below by its value at k=1+j=2t+x.
Writing y=q-1, direct collection gives
\[
\left.(F_4)_k(U(t),y)\right|_{k=2t+x}
=\frac{tq}{2W^2}(d_0+d_1y+d_2y^2+d_3y^3),
\tag{10}
\]
where
\[
d_0=xc\{1-2t+x(-2t^2+10t-1)+16tx^2+8tx^3\}>0,
\qquad d_3=xWJ>0,
\]
\[
\begin{aligned}
d_1={}&t-2t^2+(12-23t+8t^2)x
 +(35-52t+10t^2+4t^3)x^2\\
&+(43-60t+16t^2)x^3+(16-20t+4t^2)x^4,
\end{aligned}
\]
\[
\begin{aligned}
d_2={}&-6t^2+(-16t-6t^2)x+(-5-27t+2t^3)x^2\\
&+(-7-19t+8t^2)x^3+(-4-2t+2t^2)x^4<0.
\end{aligned}
\]
The displayed signs hold on 3/8<=t<=2/5, x>0. Furthermore
\[
\begin{aligned}
4d_1+d_2={}&4t-14t^2+(48-108t+26t^2)x\\
&+(135-235t+40t^2+18t^3)x^2\\
&+(165-259t+72t^2)x^3+(60-82t+18t^2)x^4>0.
\end{aligned}
\tag{11}
\]
For an explicit check, the constant is at least -16/25, the linear
coefficient is at least 224/25, and x>=1/5. Those terms together
are at least 144/125. The remaining three coefficients exceed
41, 307/5 and 136/5, respectively, after dropping positive terms.
Since 0<=y<=h<=1/4 and d_2<0, (11) gives
d_1+d_2y>=d_1+d_2/4>0. This proves positivity in (10), hence
\[
\boxed{(G_4)_k>0.}
\tag{12}
\]
Lowering k to 29t^2/4 would therefore preserve the negative sign
forced by an actual point. It remains to prove positivity there.

## 3. Reduce that shape face to h=1/4

At k=29t^2/4, put R=x^2+10x+15 and define
\[
P(h,j,y)=192q(q+1)W^3R\,G_4,
\quad t=(1-h)/2,\quad x=h+j,\quad q=1+y.
\tag{13}
\]
Every multiplying factor is positive. The
[polynomial monotonicity theorem](MIXED_NONSHORT_HIGH_RATIO_POLYNOMIAL_MONOTONICITY.md)
specifies this polynomial completely and proves
\[
P_h<-237\quad\hbox{on}\quad
h\in[1/5,1/4],\ j\in[1/30,1/5],\ y\in[0,1/4].
\tag{14}
\]
The original domain lies in this rectangle because
j<=5h/7<=5/28 and y<=(h-j)/(1+2j)<=13/64.
Moreover increasing h to 1/4 only enlarges the allowed y interval.
Therefore
\[
P(h,j,y)\ge P(1/4,j,y)
\quad\hbox{for}\quad
1/30\le j\le5/28,\quad
0\le y\le\frac{1/4-j}{1+2j}.
\tag{15}
\]

## 4. Concavity in the event factor

Write P_0(j,y)=P(1/4,j,y). The finite identities in Appendix A give
\[
-33554432(P_0)_{yy}
=2S_2(j)+6S_3(j)y+36S_4(j)y^2
 +30S_5(j)y^3+90S_6(j)y^4>0.
\tag{16}
\]
All coefficients of S_3,S_4,S_5 are positive, and S_6 has the
displayed positive factorization. S_2 has only one negative
coefficient, its constant; its positive linear term alone exceeds
that constant for j>=1/30. Thus P_0 is strictly concave in y.
It suffices to prove positivity at y=0 and y=(1/4-j)/(1+2j).

At y=0, the exact factorization is
\[
P_0(j,0)=-\frac{5(4j+1)}{33554432}F_6(j),
\]
\[
\begin{aligned}
F_6(j)={}&377487360j^6+3882024960j^5+13037322240j^4\\
&+16853397568j^3+5310959344j^2-2566640212j-2298115.
\end{aligned}
\tag{17}
\]
This polynomial is convex on j>=0, since its second derivative has
positive coefficients. Its maximum on [1/30,5/28] is thus bounded
by the larger endpoint value. Both are negative:
\[
F_6(1/30)=-\frac{6860638166131}{84375},\qquad
F_6(5/28)=-\frac{21333408272640}{117649}.
\tag{18}
\]
Hence P_0(j,0)>0.

At the other endpoint the exact identity is
\[
(1+2j)^6P_0\left(j,\frac{1/4-j}{1+2j}\right)
=-\frac{(4j+5)^2}{137438953472}Q_{13}(j).
\tag{19}
\]
Appendix B displays the entire polynomial Q_13. Its coefficients
of degrees 0 through 3 are negative, and those of degrees 4 through
13 are positive. Writing the latter as a_i, their weighted sum obeys
\[
\sum_{i=4}^{13}a_i(5/28)^{i-2}<4500000000000
<6238486162096.
\tag{20}
\]
The last integer is the absolute quadratic coefficient of Q_13.
For 0<=j<=5/28, its negative quadratic term therefore absorbs
every positive higher term. Its remaining constant is strictly
negative, and the remaining linear and cubic terms are nonpositive.
Thus Q_13<0, proving positivity in (19).

Both endpoint signs and concavity prove P_0>0 on (15). Equations
(13)--(15) then prove G_4>0 on the entire scale face, including
its enlarged points where k may exceed 1+j. Only the original
actual k interval was used for the preceding shape comparison.

## 5. Actual contradiction

A hypothetical actual point in (2) forces G_4<0 by (1)--(6).
The proved shape monotonicity lowers k to 29t^2/4 while keeping
t,x,q fixed, retaining that negative sign. The last two sections
prove the opposite strict sign at precisely that scalar shape.
This contradiction proves the theorem.

All three original inequalities in (1) are used before any scalar
change. The proof assigns neither a missing-control floor nor a
competitive Casimir cap to a new physical trajectory. It is a
hand inequality on the same comparison coordinates and leaves
the common covector and actual twisted seam untouched.


## Appendix A. Complete concavity identities

Write poly(c_0,...,c_n)=sum c_i j^i. The four complete polynomials
used in (16) are given below, with coefficients in increasing degree.
Their signs are visible term by term, except the single negative
constant of S_2 addressed in the proof.

\[
\begin{aligned}
S_2={}&\operatorname{poly}(
-3452577725,749621562620,5798138644160,\\
&16854881258496,23857368553728,18269993214976,\\
&7767802183680,1761936408576,193072201728,\\
&9663676416).
\end{aligned}
\]

\[
\begin{aligned}
S_3={}&\operatorname{poly}(
206999424875,2666739707200,12350032027040,\\
&28962466017280,38029908750080,29356703211520,\\
&13449039790080,3528836775936,478704304128,\\
&25769803776).
\end{aligned}
\]

\[
\begin{aligned}
S_4={}&\operatorname{poly}(
118191026375,972679084600,3454910298400,\\
&6978799754240,8587056326400,6595613337600,\\
&3150843904000,895156748288,133928321024,\\
&7516192768).
\end{aligned}
\]

\[
\begin{aligned}
S_5={}&\operatorname{poly}(
116973369375,789233626000,2360385612000,\\
&4209951820800,4830819296000,3634022830080,\\
&1770813358080,528039804928,83701530624,\\
&4831838208).
\end{aligned}
\]

The last coefficient factors as
\[
S_6=(4j+5)(256j^2+575)(16j^2+40j+15)
       (16j^2+168j+281)(256j^2+320j+325)>0.
\]
All these identities follow by substitution of h=1/4 into the compact
polynomial specified in the monotonicity note and collection in y.
In particular S_2>0 for j>=1/30 follows already from
749621562620/30>3452577725.

## Appendix B. Complete upper-endpoint polynomial

The coefficients below specify Q_13(j)=sum a_i j^i in (19).

| i | a_i |
| ---: | ---: |
| 0 | -32780511755 |
| 1 | -2142060814760 |
| 2 | -6238486162096 |
| 3 | -1149178936512 |
| 4 | 16169916102400 |
| 5 | 252207913837568 |
| 6 | 1497080020561920 |
| 7 | 4163517254975488 |
| 8 | 6518120300675072 |
| 9 | 6131951271673856 |
| 10 | 3451166990008320 |
| 11 | 1087575108354048 |
| 12 | 161164352815104 |
| 13 | 6236292513792 |

For an exact arithmetic check of (20), the weighted positive sum is
\[
\frac{8859712500098641534000}{1977326743}<4500000000000.
\]
