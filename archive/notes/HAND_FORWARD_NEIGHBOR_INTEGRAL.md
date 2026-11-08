# A hand forward-neighbor bound by integral comparison

Date: 2026-11-07. The asymmetric initial-value identities and the
negative logarithmic term are proved below. Section 3 proves the whole
symmetric comparison face; the companion
[asymmetric hand proof](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md)
completes the other face. Together they prove the uniform neighbor
bound `1<=b/a,c/a<4/3` without the interval contraction cover.

## 1. The asymmetric initial logarithm is nonpositive

Use the actual necessary residual of
[GLOBAL_FORWARD_NEIGHBOR_CONTRACTION](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md),
and write

\[
S=1+z,\quad T=1+w,\quad K=1+U,\quad
Z=z^2+U,\quad W=w^2+U,
\]
\[
q=ST/K,\quad H=S^2/Z,\quad I=T^2/W,
\quad x=z/S,\quad y=w/T.
\]

The comparison domain has

\[
11/5\le U\le3,\quad1\le z\le w,\quad w\ge4/3,
\quad z+w\le5(U-1)/3.
\tag{1}
\]

For fixed `w`, define

\[
F_w(q)=\frac{q-1}{T}+\frac wT(1-q^{-1})-\log q.
\tag{2}
\]

**Lemma.** On (1), `F_w(q)<=0`.

Indeed,

\[
\partial_qF_w=\frac{(q-1)(q-w)}{Tq^2}.
\]

Thus its maximum on an interval starting at `q=1` is at one of the
two endpoints. The budget and `z<=w` give

\[
q\le\frac{(1+z)(1+w)}{2+3(z+w)/5}
\le\overline q(T):=\frac{5T^2}{2(3T+2)}.
\tag{3}
\]

For the second inequality, the middle expression increases with `z`:
its derivative has the positive numerator
`(1+w)(7+3w)/5`. Moreover

\[
\frac d{dT}F_{T-1}(\overline q(T))
=-\frac{(5T^2-6T-4)(9T^3-5T^2-22T-12)}
        {5T^4(3T+2)^2}<0
\tag{4}
\]

for `T>=7/3`. Both numerator factors are positive there: on putting
`r=T-7/3>=0`, they become

\[
5r^2+\frac{52}3r+\frac{83}9,
\qquad
9r^3+58r^2+\frac{305}3r+\frac{214}9.
\]

At `T=7/3`, one has `qbar=245/162`, and the rational part of
(2) is `38263/92610`. The elementary inequality

\[
\log a\ge2\left(\rho+\frac{\rho^3}{3}\right),
\qquad \rho=\frac{a-1}{a+1},\quad a\ge1,
\]

therefore gives the explicit comparison

\[
F_{4/3}(245/162)
\le-\frac{2208606511}{6243686833230}<0.
\tag{5}
\]

Together with `F_w(1)=0`, equations (3)--(5) prove the lemma.

There is also a uniform negative margin on the actual comparison
domain (1). Here `q>=7/6`, and

\[
\partial_wF_w(q)=-\frac{(q-1)^2}{q(1+w)^2}<0.
\]

The same two-term logarithm bound gives

\[
F_{4/3}(7/6)\le-\frac{703}{645918}<-\frac1{3000},
\]

while the bound in (5) is also strictly smaller than `-1/3000`.
Apply the endpoint-maximum argument on `[7/6,qbar(T)]`, and use
the decrease in `w` at the lower endpoint and (4) at the upper
endpoint. It follows that

\[
\boxed{F_w(q)<-1/3000.}
\tag{5a}
\]

This margin is optional in the symmetric proof below, but may be
retained in other comparisons.

## 2. The asymmetric integral upper bound

Let

\[
d_z=H-1,\quad d_w=I-1,\quad e=h-1,
\qquad f(h)=\frac{h-h^{-1}}2-\log h,
\]
\[
\Delta_w=F_y(I)-(1-y+y^2),
\qquad
\Delta_0=y(y-1/2)d_w+\frac{y d_w^2}{3(d_w+2)}.
\tag{6}
\]

For the exact residual `E=alpha A-B-nF_x(h)-mF_y(I)`, direct
substitution and differentiation at `h=1` give

\[
\mathcal E(1)=\frac KZ F_w(q)
 -\frac{K^2(q-1)}{SZ}\Delta_w,
\tag{7}
\]
\[
\mathcal E_h(1)=\frac{SK}{Z}
 \left[F_w(q)+\frac{x(q-1)(q/T-y)}q\right]
 -\frac{K^2(Sq-1)}{SZ}\Delta_w.
\tag{8}
\]

The left ratio in the extra slope term is `x=z/S`; the expression
`q/T-y=(q-w)/T` uses the right neighbor. No symmetry is assumed
in (7)--(8).

The second derivative is

\[
\mathcal E_{hh}=-\frac{zP_*(h)}{Zh^3},
\qquad
P_*(h)=(U-z)h^2(2zh-S)+Zh-2zS.
\]

On (1), `U>z`, `P_*(1)=-zZ d_z`, and `P_*'(h)>=Z` for
`h>=1`. Integrating twice gives

\[
\mathcal E(h)\le\mathcal E(1)+e\mathcal E_h(1)
 +\frac{z^2d_z e^2}{2h}-zf(h).
\tag{9}
\]

The elementary derivative identity

\[
\frac d{dh}\left[f(h)-\frac{(h-1)^3}{3h(h+1)}\right]
=\frac{(h-1)^4}{6h^2(h+1)^2}\ge0
\]

proves the Padé lower bound on `f`. Also

\[
\Delta_w=y(y-1/2)d_w+\frac{yI f(I)}{d_w}\ge\Delta_0,
\]

with the continuous interpretation at `d_w=0`. Using Section 1
to discard the nonpositive term `K(1+Se)F_w(q)/Z`, equation (9)
therefore yields

\[
\boxed{
\begin{aligned}
\mathcal E(h)\le\mathcal B_w:={}&
\frac{eSK}{Z}\frac{x(q-1)(q/T-y)}q\\
&-\frac{K^2}{SZ}\{q-1+e(Sq-1)\}\Delta_0
 +\frac{z^2d_z e^2}{2h}-\frac{ze^3}{3h(h+1)}.
\end{aligned}}
\tag{10}
\]

The coefficient of `Delta_0` is nonnegative. Thus its use has the
required upper-bound direction.

The stronger exterior cost budget also gives

\[
H\le h\le h_c:=\frac{S(5U-2-3w)}{3Z}.
\tag{11}
\]

This follows by bounding the actual other factor below by `I`, so
its cost term is at least `T`. Decreasing `w` to `max(z,4/3)`
preserves (11), as well as the domain of the monotone residual
comparison. Hence the two faces listed in Section 1 of
[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) remain exhaustive.

## 3. The symmetric face is excluded by hand

**Theorem.** Suppose

\[
w=z,\qquad4/3\le z\le5/3,
\qquad1+6z/5\le U\le3,
\]
\[
H\le h\le\min\{S/z,h_c\}.
\tag{12}
\]

Then the exact necessary residual satisfies `E(h)<0`.

### 3.1 A simple enlarged factor domain

Set

\[
\lambda=\frac{U-z}{S},\qquad
m=1-\lambda=\frac{2z+1-U}{S},
\qquad v=\frac{S(h-1)}h.
\]

These are the same variables as in
[HAND_H5_INTEGRAL_RATIONAL_BOUND](HAND_H5_INTEGRAL_RATIONAL_BOUND.md).
The current scale and cost restrictions give

\[
\frac27\le m\le\frac12,\qquad
\frac43\le z\le\frac{2+m}{2-m},\qquad m\le v\le1.
\tag{13}
\]

Indeed, `U<=3` gives `m>=2(z-1)/(z+1)>=2/7` and the upper
bound on `z`. The central budget gives `m<=4z/[5(z+1)]<=1/2`.
The factor bounds give `m<=v<=1`.

The cost restriction (11) yields the stronger bound

\[
v\le v_c(z,m):=
\frac{(z+1)\{(4-5m)z-2m\}}{(7-5m)z+3-5m}.
\tag{14}
\]

For fixed `m` in (13), this function increases with `z`. To check
this directly, put `A=4-5m`, `B=-2m`, `C=A+3`, `D=A-1`.
The numerator of its derivative is

\[
ACz^2+2ADz+(A+B)D-BC>0,
\]

since `A,D,A+B,C>0` and `B<0`. Thus (13)--(14) imply

\[
v\le\frac{8-10m-3m^2}{(2-m)(5-4m)}<1-\frac45m.
\tag{15}
\]

For the last comparison, clear its positive denominators. The
difference has the positive numerator

\[
10-55m+87m^2-16m^3
\ge79m^2-55m+10>0.
\]

The final quadratic has discriminant `-135`; equivalently its
minimum is `135/316>0`.

### 3.2 Reuse the cubic rational upper bound

On the symmetric face, (10) is precisely the rational expression
in Section 1 of the linked H5 integral-bound note. The two elementary
weakenings in its Section 2 do not use `U>=3`; they therefore still
give

\[
\mathcal B_z\le
-\frac{zP}{6S^2(z+\lambda)^2(S-v)},
\tag{16}
\]

where

\[
\begin{aligned}
P={}&(z+\lambda)^2v^3-3zmS(z+\lambda)v^2\\
 &+\left[(1+\lambda)mSz\{3(z-1)+m\}
 -6(z+\lambda)(z-\lambda)(1-z\lambda)\right]v\\
 &+(1+\lambda)mS\{3(z-1)+m\}(z-\lambda),
\qquad\lambda=1-m.
\end{aligned}
\tag{17}
\]

We prove `P>0` on the enlarged domain

\[
z\ge4/3,\quad2/7\le m\le1/2,
\quad m\le v\le1-4m/5.
\tag{18}
\]

### 3.3 The cubic increases from z=4/3

Write `r=z-4/3>=0`. Direct expansion gives

\[
P=P_0+C_1r+C_2r^2+C_3r^3,
\tag{19}
\]

where `P_0=P(4/3,m,v)` and

\[
C_3=3\{(2-m^2)v+m(2-m-v^2)\}\ge0,
\]
\[
\begin{aligned}
C_2={}&v^3+3m(m-6)v^2+(18-10m^2-m^3)v\\
 &+m(18-m-4m^2),
\end{aligned}
\]
\[
\begin{aligned}
3C_1={}&(14-6m)v^3+3m(11m-35)v^2\\
 &+(7m^3-71m^2+36m+30)v\\
 &+m(-3m^3-26m^2+49m+30).
\end{aligned}
\tag{20}
\]

For `C_2`, use `v^2<=v` and `m<=1/2` to obtain

\[
C_2\ge(18-18m-7m^2-m^3)v+m(18-m-4m^2)
\ge\frac{57}{8}v+\frac{33}{2}m>0.
\]

For `C_1`, discard the positive cubic term and use `v^2<=v`:

\[
3C_1\ge C+Dv,
\]
\[
C=m(-3m^3-26m^2+49m+30)\ge185m/8,
\qquad D=7m^3-38m^2-69m+30.
\]

Also

\[
C+D=-3m^4-19m^3+11m^2-39m+30\ge127/16.
\]

Consequently

\[
3C_1\ge(1-v)\frac{185m}{8}+v\frac{127}{16}>0.
\tag{21}
\]

It remains to prove `P_0>0`.

### 3.4 A four-term identity proves the boundary sign

The complete boundary cubic is

\[
\begin{aligned}
9P_0={}&(7-3m)^2v^3-28m(7-3m)v^2\\
 &+(44m^3-134m^2+36m+14)v\\
 &+7m(-3m^3+2m^2+7m+2).
\end{aligned}
\tag{22}
\]

Write `v=m+(1-9m/5)t`, so `0<=t<=1` on (18). Direct
multiplication gives

\[
9P_0=mA_0(1-t)^3+\frac25A_1t(1-t)^2
       +\frac1{25}A_2t^2(1-t)+\frac1{125}A_3t^3,
\tag{23}
\]

with

\[
\begin{aligned}
A_0={}&9m^4+65m^3-267m^2+85m+28,\\
A_1={}&-54m^5+168m^4-82m^3-472m^2+237m+35,\\
A_2={}&432m^5-7347m^4+18871m^3-12455m^2+1415m+700,\\
A_3={}&-576m^5+4543m^4-27746m^3+60960m^2-39600m+7875.
\end{aligned}
\tag{24}
\]

All four are positive on `2/7<=m<=1/2`. For the first two,
the second derivatives are

\[
A_0''=6(18m^2+65m-89)<0,
\]
\[
A_1''=-4(270m^3-504m^2+123m+236)<0.
\]

The first bracket is at most `-52`; the second is at least
`236-504/4=110`. Their minima on the interval are therefore at
the endpoints. Those values are

\[
A_0(2/7)=\frac{76990}{2401},\quad A_0(1/2)=\frac{199}{16},
\]
\[
A_1(2/7)=\frac{1063679}{16807},\quad A_1(1/2)=\frac{545}{16}.
\]

For the other two, put `n=1/2-m`, so `0<=n<=3/14<1/4`.
Their exact expansions are

\[
A_2=\frac{3311}{16}+\frac{1701}{4}n+5371n^2
 -5257n^3-6267n^4-432n^5,
\]
\[
A_3=\frac{1803}{16}-2642n+\frac{50871}{2}n^2
 +20100n^3+3103n^4+576n^5.
\]

Using `n<=1/4` in the three negative terms of `A_2` gives

\[
A_2\ge\frac{3311}{16}+\frac{1701}{4}n
 +\frac{58533}{16}n^2>0.
\]

For `A_3`, discard its three positive terms of degree at least
three and weaken the remaining coefficients:

\[
A_3\ge25000n^2-2700n+100
 =25000(n-27/500)^2+271/10>0.
\]

This proves (23) strictly positive. Equations (19)--(23) show
`P>0`, and then (10), (16) give `E(h)<0` on the whole symmetric
face (12).

## 4. The asymmetric face and the completed neighbor bound

The other neighbor comparison is

\[
w=4/3,\qquad1\le z\le4/3,\qquad
9/5+3z/5\le U\le3,
\]
\[
H\le h\le\min\left\{S/z,
\frac{S(5U-6)}{3Z}\right\}.
\]

The [asymmetric hand proof](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md)
proves the exact residual strictly negative on this entire domain.
It retains the explicit negative logarithmic margin (5a), lowers
the opposite floor to a rational affine function, and reduces the
factor dependence to the endpoints of a concave quadratic. The two
remaining planar signs are proved by derivative concavity and
explicit edge inequalities.

The monotone comparison in Section 2 sends every ordered candidate
with `w>=4/3` to either this face or the symmetric face of Section 3,
preserving the required factor and cost bounds. Both faces contradict
the actual necessary condition `E>=0`. Therefore a competitive
all-forward period with the stated upstream hand prerequisites has

\[
\boxed{1\le b/a<4/3,\qquad1\le c/a<4/3.}
\]

This closes the neighbor gate for the hand route. The separate
stationary norm-sum or direct Casimir comparison remains open.
