# Exact reverse secant monotonicity in the nonshort shape comparison

Date: 2026-11-07 UTC. Hand reductions; the final endpoint sign remains open.

This note strengthens the single upper endpoint in
[MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON](MIXED_NONSHORT_REVERSE_AFFINE_COMPARISON.md):
the exact extended reverse secant may be retained at that endpoint.
The reduction is accepted in the
[independent endpoint review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).
Every sign below follows from an integral comparison or the displayed
short identities. No interval cover or sampled minimum is a premise.

## 1. A sharper duration ratio

Suppose 0<a<c, a<d, and

\[
g_c(d)<v:=\operatorname{Sec}(a,c,d)<g_c(a),
\qquad g_c(s)=1-\frac{cs}{(c+s)^2}.
\]

Then

\[
\boxed{d<7c/3.}
\tag{1}
\]

Indeed g_c(s)>=g_c(a)>v for 0<=s<=a, so extending the secant average
to start at zero gives Sec(0,c,d)>v>g_c(d). With h=d/c this says

\[
\log(1+h)<\frac{h(1+2h)}{(1+h)^2}.
\]

The difference of the left and right sides has derivative
h(h-1)/(1+h)^3, which is positive for h>1. At h=7/3, the first
three positive terms of the atanh series give

\[
\log(10/3)>
2\left[\frac7{13}+\frac{(7/13)^3}{3}
                 +\frac{(7/13)^5}{5}\right]
=\frac{6678322}{5569395}>\frac{119}{100}.
\tag{2}
\]

The last strict comparison has positive cross-product difference
5074195. Since h(1+2h)/(1+h)^2=119/100 at h=7/3,
the required strict inequality cannot hold for h>=7/3. This proves (1).

In the actual smaller-nonshort geometry, the incoming secant has
both displayed strict bounds, so (1) applies to c. In the reverse-next
case the actual outgoing norm and the extended secant give
Sec(a,r,d)>g_r(d), while r^2>=ad implies Sec(a,r,d)<g_r(a).
For the latter implication, at a<s<d,

\[
g_r(s)-g_r(a)=
\frac{r(s-a)(as-r^2)}{(a+r)^2(s+r)^2}<0.
\]

Consequently the same proof gives d<7r/3. In particular
r>3d/7, and (3/7)^2+2(3/7)-1=2/49>0.

## 2. An upper bound for the weighted secant derivative

For 0<a<d define, as in the
[weighted secant reduction](MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md),

\[
J_{a,d}(R)=(R+d)^2[1-\operatorname{Sec}(a,R,d)]
=\frac1{d-a}\int_a^d\frac{R(R+d)^2s}{(R+s)^2}\,ds.
\]

For R>=3d/7, differentiation under the integral gives

\[
J'_{a,d}(R)=\frac1{d-a}\int_a^d f_R(s)\,ds,
\quad
f_R(s)=
\frac{s(R+d)(R^2-Rd+3Rs+ds)}{(R+s)^3}<d\qquad(a\le s<d).
\tag{3}
\]

Here is a pointwise proof of the strict upper bound. Put z=R/d and
u=s/d. Direct subtraction gives

\[
d-f_R(s)=
\frac{d(1-u)[z^3+(3z^2+z)u-u^2]}{(z+u)^3}.
\tag{4}
\]

The bracket is a concave quadratic in u. Its values at u=0 and u=1
are z^3 and (z+1)(z^2+2z-1), respectively. Both are positive for
z>=3/7. Thus (4) is positive for every 0<=u<1.
Averaging over the nontrivial interval [a,d] proves

\[
J'_{a,d}(R)<d\qquad(R\ge3d/7).
\]

The strictness does not depend on differentiating a numerical secant
approximation.

## 3. The exact weighted root gap decreases with k

Use the established normalized variables and solved boundary root:

\[
p=t+x,\quad W=1+x,\quad H=t+x(x+2),\quad
B=k+2tx+x^2,\quad r=qB/W-p,\quad D=qH/W-p>0,
\]
\[
w_*=1+\frac{n_1}{DB}+\frac{n_0}{DB^2},
\]
\[
\begin{aligned}
n_1={}&H(1-t-p^2/W-p\log q)+(p-HW)v
             +p(2p^2-1+t-t^2),\\
n_0={}&p[(H^2-p^2)v+p^2(1+2(1-t)x)-HpW/q].
\end{aligned}
\tag{5}
\]

Keep t,x,q and the exact v fixed while increasing k. Since dr/dk=q/W,
the exact identity from the weighted secant reduction gives

\[
\begin{aligned}
\frac{d}{dk}\{B^2[w_*-\operatorname{Sec}(t,r,p)]\}
&=\frac{n_1}{D}+\frac Wq J'_{t,p}(r)\\
&<\frac{n_1}{D}+\frac{pW}{q}.
\end{aligned}
\tag{6}
\]

The actual reverse inequality p<7r/3 from Section 1 is enough to use
Section 2, and it remains true as k increases.

It remains to check that the right side of (6) is negative. Assume
only 0<t<1/2, x>0, q>1 and the unchanged derivative floor

\[
v>g_{1-t}(p)=1-(1-t)p/W^2.
\]

As p-HW<0, replacing v by this lower bound and replacing log q by
2(q-1)/(q+1) strictly increases n1. Let Lbar_p denote the resulting
upper bound for n1/D+pW/q. With y=q-1, direct collection gives

\[
-2q(q+1)W^2D\,\overline L_p
=P_0+P_1y+P_2y^2,
\tag{7}
\]
\[
P_0=4x^2(1-t)(t+x)^2,
\]
\[
P_1=x(1-t)\left[
 4t+(6t^2+8t+4)x+8(1+2t)x^2+10x^3\right],
\]
\[
P_2=2\left[
 t^2+t(t+4)x+(3+8t-t^3)x^2
 +(7+6t-3t^2)x^3+(6-t)x^4+x^5\right].
\tag{8}
\]

All three polynomials are strictly positive for the stated ranges.
For example 3+8t-t^3>3-t^3>0, 7+6t-3t^2>7-3/4>0,
and 6-t>0. All factors in (7) outside Lbar_p are positive.

For a short algebra check against the earlier affine note, replacing
mu=(t+p)/2 by p adds xW/(2q) to its affine coefficient.
Thus its right side in the earlier three-coefficient identity is
reduced by x(q+1)W^3D; collecting that single expression gives (8).
No further sign coefficients are suppressed.

Together with (6)--(8), this proves

\[
\boxed{
\frac{d}{dk}\{B^2[w_*-\operatorname{Sec}(t,r,p)]\}<0.
}
\tag{9}
\]

## 4. The strengthened single upper endpoint

Write the incident-upper residual numerator as N(k)=A_N k+B_N,
where A_N>0 by
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
Set k_top=-B_N/A_N. The actual boundary necessary conditions give
N(k)<0 and w*<Sec(t,r,p), hence k<k_top.

The r bound from Section 1 persists along this increase of k, and
v is unchanged. Therefore (9) sends the actual strict negative gap
to the upper endpoint:

\[
\boxed{
\left.B^2[w_*-\operatorname{Sec}(t,r,p)]\right|_{k=k_{\rm top}}<0.
}
\tag{10}
\]

At k_top the incident root norm equals its upper envelope.
Formula (10) retains the exact secant, improving the earlier rational
line necessary inequality. It does not assert that this endpoint is a
physical trajectory. Constraints changed by the k comparison require
their own transfer proof; in particular, the original root Casimir
cap is not imposed there.

For an original actual centre with a>=3/4, the separately proved
monotonicity in Section 5 of
[MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md)
does allow its explicit retained Gt bound to reach this endpoint,
with exact v fixed. The final nonnegativity sign contradicting (10)
is still open.
