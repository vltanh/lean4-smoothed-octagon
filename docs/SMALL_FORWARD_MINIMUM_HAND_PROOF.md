# A hand replacement for the hard small-forward-minimum face

Date: 2026-11-07 UTC. Accepted independent internal hand review.

This note replaces Section 6, the large H5 coefficient identity, of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
The actual common-covector stationarity identities, genuine exterior
switching floors, scalar larger-neighbor comparison and two easy faces
remain exactly Sections 1--5 of that note. Their hand arguments do not
depend on its later coefficient tables.

The present replacement uses an integral estimate and a cubic with an
explicit elementary sign proof. Neither executing a checker nor trusting
a large coefficient list is a premise. It closes this one prerequisite;
the later all-forward and mixed-period exclusions remain separate tasks.

## 1. Normalize the remaining face

In the symmetric comparison face put

\[
U=4/a^2,\quad z=b/a=c/a,\quad S=1+z,\quad
L=1+U,\quad Z=z^2+U,
\]
\[
q=S^2/L,\qquad H=S^2/Z,
\qquad x=z/S.
\]

The domain to be excluded is exactly

\[
U\ge3,\qquad (U-1)/2<z<U,
\qquad H\le h<S/z.
\tag{1}
\]

In particular `z>1`, `H>1` and `q>1`. Write

\[
F_x(v)=1+x^2v-xv\frac{\log v}{v-1},
\qquad F_x(1)=1-x+x^2.
\]

The original scalar residual divided by the positive a is

\[
\mathcal E(h)=\alpha A-B_0-nF_x(h)-mF_x(H),
\tag{2}
\]
\[
\begin{aligned}
A&=1+2z-2/S+1/L-\log q,\\
B_0&=hZ/S+1-z^2S/(hZ)-z^2/S+z^3/Z-z\log h,\\
\alpha&=L(hS-z)/Z,\\
n&=S^2(U-z)(h-1)/Z,\\
m&=L^2\{q-1+(h-1)(Sq-1)\}/(SZ).
\end{aligned}
\]

The actual PMP inequalities force this residual to be nonnegative.
We prove it strictly negative on (1).

## 2. The central logarithmic term is nonpositive

Define

\[
F(q)=\frac{q-1}{S}+x(1-q^{-1})-\log q.
\]

At fixed z,

\[
F'(q)=\frac{(q-1)(q-z)}{Sq^2}.
\tag{3}
\]

Thus on any interval `[1,Q]`, its maximum is at an endpoint: it first
decreases and then increases. We claim `F(q)<=0` on the whole domain
(1), by checking the permitted upper endpoint.

If `1<=z<=3`, then `U>=3` implies `q<=S^2/4`. At that upper endpoint,

\[
F(S^2/4)=S/4+1-2/S-4/S^2+4/S^3-2\log(S/2),
\]

whose derivative with respect to S is

\[
\frac{(S-6)(S-2)^2(S+2)}{4S^4}\le0\qquad(2\le S\le4).
\]

Its value at S=2 is zero. If `z>=3`, use `U>=z`, hence `q<=S`.
Now

\[
F(S)=x+x^2-\log S,
\qquad \frac{d}{dS}F(S)=-\frac{(S-1)(S-2)}{S^3}<0.
\]

At S=4 the value is `21/16-log 4<0`, since
`log 4=2 log 2>4/3>21/16`; the bound `log 2>2/3` follows by
integrating `1/(1-t^2)>1` from zero to 1/3. Together with (3), these
two cases prove

\[
F(q)\le0.
\tag{4}
\]

## 3. Integrate the second derivative from the zero exterior factor

Let

\[
d=H-1,\qquad e=h-1,\qquad
\Delta=F_x(H)-(1-x+x^2).
\]

The initial-value identities already used in the easy symmetric face,
with the opposite-floor difference retained, are

\[
\mathcal E(1)=\frac LZ F(q)
 -\frac{L^2(q-1)}{SZ}\Delta,
\]
\[
\mathcal E'(1)=\frac{SL}{Z}
 \left\{F(q)+\frac{x(q-1)(q/S-x)}q\right\}
 -\frac{L^2(Sq-1)}{SZ}\Delta.
\tag{5}
\]

These identities can also be verified immediately from (2), taking
the continuous value of `F_x` at one. The exact second derivative is

\[
\mathcal E''(h)=-\frac{zP(h)}{Zh^3},
\quad P(h)=(U-z)h^2(2zh-S)+Zh-2zS.
\tag{6}
\]

Here

\[
P(1)=-zZd,\qquad
P'(h)=2(U-z)h(3zh-S)+Z\ge Z\quad(h\ge1).
\]

Consequently `P(h)>=-zZd+Z(h-1)`, and (6) gives

\[
\mathcal E''(h)\le\frac{z^2d}{h^3}-\frac{z(h-1)}{h^3}.
\]

Integrate twice from one. The two exact integrals are

\[
\int_1^h\frac{h-r}{r^3}\,dr=\frac{e^2}{2h},
\qquad
\int_1^h\frac{(h-r)(r-1)}{r^3}\,dr
=f(h):=\frac{h-h^{-1}}2-\log h.
\]

Thus

\[
\mathcal E(h)\le\mathcal E(1)+e\mathcal E'(1)
 +\frac{z^2de^2}{2h}-zf(h).
\tag{7}
\]

## 4. Two short logarithm bounds give the rational upper expression

The elementary Padé estimate used in the hand refinements is equivalent to

\[
f(h)\ge\frac{(h-1)^3}{3h(h+1)}\qquad(h\ge1).
\tag{8}
\]

For a direct proof, the difference is zero at one and its derivative
is `(h-1)^4/[6h^2(h+1)^2]>=0`. Also

\[
\Delta=x(x-1/2)d+\frac{xH}{d}f(H)
\ge\Delta_0:=x(x-1/2)d+\frac{xd^2}{3(d+2)}.
\tag{9}
\]

The coefficient of Delta in (5) after forming the combination in (7)
is `-L^2{q-1+e(Sq-1)}/(SZ)<0`. Hence inserting (8)--(9), and
discarding the nonpositive multiple of F from (4), proves

\[
\mathcal E(h)\le\mathcal B,
\]
\[
\begin{aligned}
\mathcal B={}&\frac{eSL}{Z}\frac{x(q-1)(q/S-x)}q
 -\frac{L^2}{SZ}\{q-1+e(Sq-1)\}\Delta_0\\
&+\frac{z^2de^2}{2h}-\frac{ze^3}{3h(h+1)}.
\end{aligned}
\tag{10}
\]

## 5. The elementary cubic theorem completes the hard face

Put

\[
\lambda=\frac{U-z}{1+z},\qquad s=\frac{1+z}{h}-z.
\]

The domain (1) gives `0<lambda<1`, `0<s<=lambda` and
`z>=(3-lambda)/(1+lambda)`. These are precisely the hypotheses of
[HAND_H5_INTEGRAL_RATIONAL_BOUND](HAND_H5_INTEGRAL_RATIONAL_BOUND.md).
That note proves the expression (10) strictly negative whenever h>1,
using four displayed grouped polynomial identities, two elementary
ranges, and completed-square comparisons. Its proof
includes all weak boundaries of this enlarged domain.

It follows that `E(h)<=B<0`, contradicting its necessary nonnegative
sign. This proves the entire hard symmetric face without the old H5
coefficient table.

Together with the unchanged hand arguments in Sections 1--5 of the
original minimum note, every comparison face is now excluded by hand.
Therefore a competitive pure-forward period beyond the retained short
terminal cases has `a_min^2>4/3`. For a mixed period, the already proved
minimum structure and existence of a reverse centre below that scale
force a global minimum to be a reverse centre. The common physical
covector and true twisted seam are inherited from the original
stationarity and switching-floor identities; no scalar comparison is
asserted to be a new physical trajectory.

The independent review is recorded in
[SMALL_FORWARD_MINIMUM_HAND_AUDIT](SMALL_FORWARD_MINIMUM_HAND_AUDIT.md).
