# A hand exclusion of the asymmetric forward-neighbor face

Date: 2026-11-07. This completes the remaining face in
[HAND_FORWARD_NEIGHBOR_INTEGRAL](HAND_FORWARD_NEIGHBOR_INTEGRAL.md).
All identities, constants, and sign arguments needed below are
displayed. No interval cover or undisplayed coefficient table is used.

## 1. Domain and the integral comparison

Fix the right neighbor `w=4/3`, and put

\[
r=z-1,\quad d=3-U,\quad S=z+1=r+2,\quad
T=7/3,\quad K=4-d,\quad Z=z^2+3-d.
\]

The remaining planar domain is the triangle

\[
0\le r\le\frac13,
\qquad0\le d\le D(r):=\frac35(1-r).
\tag{1}
\]

For the left factor,

\[
H=S^2/Z\le h\le h_c=\frac{S(9-5d)}{3Z}.
\]

Set `e=h-1`, `tau=e/h`. Its permitted interval is

\[
\tau_H=\frac{2r+d}{(r+2)^2}\le\tau\le
\tau_c=\frac{3z(3-z)-d(5z+2)}{S(9-5d)}.
\tag{2}
\]

The strong cost budget gives the upper endpoint. The original strict
star bound can be retained, but enlarging to the interval (2) is
harmless. All denominators are positive on (1).

Use the notation of the integral note:

\[
q=ST/K,\quad I=T^2/(w^2+U),\quad
x=z/S,\quad y=4/7,\quad d_z=H-1,
\]
\[
\Delta_0=y(y-1/2)(I-1)+\frac{y(I-1)^2}{3(I+1)},
\]
\[
a=\frac{SK}{Z}\frac{x(q-1)(q/T-y)}q,
\qquad C=\frac{K^2}{SZ}.
\]

Its proved integral bound, retaining the uniform logarithmic margin
`F_w(q)<-1/3000`, implies for `h>1`

\[
-\frac{6\tau}{e}\mathcal E(h)
\ge z\tau^3-3z^2d_z\tau^2
 +6(Cqz\Delta_0-a)\tau+6C(q-1)\Delta_0
 +\frac{K(1+z\tau)}{500Z}.
\tag{3}
\]

To obtain the cubic in (3), one only weakens the negative cubic
term in the integral bound using

\[
\frac{e^2}{3h(h+1)}
=\frac{\tau^2}{3(2-\tau)}\ge\frac{\tau^2}{6}.
\]

The last term in (3) follows from
`(tau/e)(1+Se)=1+z tau`. Since `6 tau/e=6/h>0`, a positive
lower bound in (3) proves the required strict sign `E(h)<0`.

## 2. A linear floor and a fixed cubic tangent

First we prove the useful floor bound

\[
\boxed{\Delta_0\ge\frac{7+15d}{1000}.}
\tag{4}
\]

Indeed,

\[
b:=I-1=\frac{6+9d}{43-9d}\le\frac13
\qquad(0\le d\le3/5).
\]

Because `y=4/7`, the definition of `Delta_0` therefore gives

\[
\Delta_0\ge\frac{2b(1+2b)}{49}
=\frac{2(6+9d)(55+9d)}{49(43-9d)^2}.
\]

After subtracting the right side of (4), the numerator over the
positive denominator `49000(43-9d)^2` is

\[
-59535d^3+703107d^2+4467d+25793
\ge667386d^2+4467d+25793>0.
\]

Next, for `tau>=0`, the exact identity

\[
\tau^3-3\tau_0^2\tau+2\tau_0^3
=(\tau-\tau_0)^2(\tau+2\tau_0)\ge0,
\qquad\tau_0=3/16,
\tag{5}
\]

supplies a fixed affine lower bound on the cubic. The coefficients
of `Delta_0` in (3) are nonnegative. Substitute (4)--(5), and put

\[
A=7z-5+3d,
\qquad B=7z-9+4d,
\qquad N=2r+d.
\]

Direct simplification of (3) gives the lower bound

\[
\boxed{
\begin{aligned}
Q(\tau)={}&-\frac{3z^2N}{Z}\tau^2\\
&+z\left\{\frac{27}{256}
 +\frac{K(10+21d)}{100Z}
 -\frac{6AB}{49SZ}\right\}\tau\\
&+\frac{K\{A(7+15d)+S\}}{500SZ}-\frac{27z}{2048}.
\end{aligned}}
\tag{6}
\]

This is concave in `tau`. It suffices to prove its two endpoint
values in (2) strictly positive.

Define their cleared numerators by

\[
Q(\tau_H)=\frac{N_H(r,d)}{12544000S^4Z},
\qquad
Q(\tau_c)=\frac{N_C(r,d)}{12544000(9-5d)^2S^2Z}.
\tag{7}
\]

These definitions, together with (2) and (6), specify the polynomials
completely. The identities needed to prove their signs are given next.

## 3. The lower-factor endpoint

We use the following elementary observation twice: if `f'` is
concave on an interval starting at zero and `f'(0)>=0`, then `f`
has its minimum at one of the interval's endpoints. The set where
the concave function `f'` is nonnegative is an interval containing
zero, so `f` first increases and then, possibly, decreases.

For fixed `r`, the polynomial `N_H` has degree at most three in `d`.
Its cubic coefficient is

\[
[d^3]N_H=-7680(490r^3+9897r^2+21508r+12248)<0.
\tag{8}
\]

Thus `partial_d N_H` is concave in `d`. Its initial value is

\[
\begin{aligned}
\partial_dN_H(r,0)={}&1488375r^5-641424945r^4
 -1407264896r^3-561144056r^2\\
 &+301678288r+93904752.
\end{aligned}
\]

Using `r^4<=r/27`, `r^3<=r/9`, `r^2<=r/3`, and discarding
the positive fifth-degree term gives

\[
\partial_dN_H(r,0)
\ge93904752-\frac{196466929}{3}r
\ge\frac{648675839}{9}>0.
\tag{9}
\]

The observation therefore reduces positivity of `N_H` to its two
boundary polynomials

\[
\begin{aligned}
N_H(r,0)={}&2261056+129417184r+237264592r^2\\
 &-449724768r^3-1006229700r^4-441992250r^5\\
 &+826875r^6-165375r^7,
\end{aligned}
\tag{10}
\]

and

\[
\begin{aligned}
25N_H(r,D(r))={}&1421414128+2465276800r-5874871904r^2\\
 &-17301347232r^3-14628219819r^4\\
 &-4234220298r^5-52456950r^6-4134375r^7.
\end{aligned}
\tag{11}
\]

The polynomial in (11) is strictly concave in `r`. The polynomial
in (10) has initial derivative `129417184>0` and strictly negative
third derivative: its only positive contribution to that derivative
is at most `120*826875/27=3675000`, whereas its negative constant
contribution is `-6*449724768`. The same observation therefore
reduces (10) to its endpoints as well.

The four endpoint values are

\[
N_H(0,0)=2261056,
\qquad N_H(1/3,0)=\frac{3310141828}{81},
\]
\[
N_H(0,3/5)=\frac{1421414128}{25},
\qquad N_H(1/3,2/5)=\frac{60873520876}{2025}.
\tag{12}
\]

They are all strictly positive. This proves `N_H>0` on (1).

## 4. The cost endpoint is concave in the smaller neighbor

We next prove

\[
\partial_r^2N_C<0
\qquad\hbox{throughout (1)}.
\tag{13}
\]

Put `g=partial_d partial_r^2 N_C`. All derivatives in this section
are partial derivatives taken before substituting `d=D(r)`; they
are not derivatives along the sloping edge. Direct differentiation
of (2), (6), and (7) gives

\[
\begin{aligned}
\partial_d^2g=-180\{&52684800dr+217712640d+392125440r^2\\
 &+1286256605r+654063907\}<0.
\end{aligned}
\tag{14}
\]

Thus `g` is concave in `d`. Its two endpoint values are

\[
\begin{aligned}
g(r,0)=90\{&348890351+2160242309r+1432873484r^2\\
 &-1447386500r^3-858921000r^4\},
\end{aligned}
\tag{15}
\]
\[
\begin{aligned}
g(r,D(r))=\frac{18}{5}\{&5937910120+23176294082r
 +19766965431r^2\\
 &-2958844713r^3-5029858820r^4\}.
\end{aligned}
\tag{16}
\]

Both are positive. In (15), use `r^3,r^4<=r^2/3`; the remaining
quadratic coefficient is `1992312952/3>0`. In (16), even the
weaker bounds `r^3,r^4<=r^2` leave the positive coefficient
`11778261898`. Concavity now gives `g>0` throughout its interval.

Consequently `partial_r^2 N_C` increases with `d`. At the upper
boundary its exact value is

\[
\partial_r^2N_C(r,D(r))=-\frac{54}{25}J(r),
\]
\[
\begin{aligned}
J(r)={}&1565534004+5426482060r-226516619r^2\\
 &-10427674468r^3-5662504317r^4+484238090r^5.
\end{aligned}
\tag{17}
\]

Dropping its positive fifth-degree term and using
`r^2<=r/3`, `r^3<=r/9`, `r^4<=r/27` gives

\[
J(r)\ge1565534004+\frac{35843612776}{9}r>0.
\]

This proves (13).

## 5. Three edges finish the cost-endpoint sign

For fixed `d`, its allowed `r` interval is

\[
0\le r\le\min\{1/3,\,1-5d/3\}.
\]

By (13), it suffices to check `r=0`, the edge `r=1/3` where
`d<=2/5`, and the sloping budget boundary.

At `r=0`, direct substitution gives

\[
\begin{aligned}
\frac14N_C(0,d)={}&372749796-595799313d+313274906d^2\\
 &+74188915d^3-116121600d^4-14112000d^5.
\end{aligned}
\tag{18}
\]

Since `d<=3/5<1`, the two negative high-degree terms can be
absorbed into the quadratic term, leaving its coefficient at least
`313274906-116121600-14112000=183041306>0`. Hence

\[
\frac14N_C(0,d)
\ge372749796-595799313d
\ge\frac{76351041}{5}>0.
\tag{19}
\]

At `r=1/3`, the exact polynomial is

\[
\begin{aligned}
\frac{81}{4}N_C(1/3,d)={}&2263207897-15861116861d
 +80664321487d^2\\
 &-43606562955d^3-21170304000d^4-1333584000d^5.
\end{aligned}
\tag{20}
\]

Here `d<=2/5`. Absorbing the last three terms into the quadratic
leaves the positive coefficient

\[
80664321487-\frac25(43606562955)
 -\frac4{25}(21170304000)-\frac8{125}(1333584000)
=59749098289.
\]

Therefore

\[
\begin{aligned}
\frac{81}{4}N_C(1/3,d)
&\ge10^9(59d^2-16d+2)\\
&=10^9\left\{59(d-8/59)^2+54/59\right\}>0.
\end{aligned}
\tag{21}
\]

Finally, on the budget boundary `d=D(r)`, one has `h_c=H`, so
the two values of `Q` coincide. Their denominators in (7) have
ratio nine, because `9-5D(r)=3(r+2)=3S`. Thus

\[
N_C(r,D(r))=9N_H(r,D(r))>0.
\tag{22}
\]

This completes the three edge comparisons, proving `N_C>0` on (1).

## 6. Conclusion for the neighbor gate

Equations (7), (12), and (19)--(22) prove that both endpoints of
the concave quadratic (6) are strictly positive. Hence `Q(tau)>0`
throughout the permitted factor interval. Equations (3)--(6) give
`E(h)<0` at every actual factor `h>1` on the asymmetric face.

Together with the symmetric-face theorem and the monotone reduction
in [HAND_FORWARD_NEIGHBOR_INTEGRAL](HAND_FORWARD_NEIGHBOR_INTEGRAL.md),
this contradicts the actual necessary condition `E>=0` whenever
the larger neighbor is at least `4/3`. Therefore the competitive
all-forward minimum satisfies the hand-proved bound

\[
\boxed{1\le b/a<4/3,\qquad1\le c/a<4/3.}
\]

This replaces the neighbor-contraction cover for the hand route.
The separate stationary norm-sum or direct Casimir comparison is
not proved here.
