# A reverse-successor order bound from the two actual norm floors

Date: 2026-11-07 UTC. Hand necessary condition, accepted in the
[independent endpoint review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

This note uses the two actual missing-control norm floors and the
extended reverse secant ceiling. It does not move a norm floor to the
solved boundary root. The scalar data a,c,d,r stay unchanged during the
usual b-boundary comparison.

## 1. The swapped secant order

Write

\[
\operatorname{Sec}(a,c,d)
=\int_0^1 g\left(\frac{a+\theta(d-a)}c\right)\,d\theta,
\qquad g(s)=1-\frac{s}{(1+s)^2}.
\]

If 0<a<c<d, then

\[
\boxed{\operatorname{Sec}(a,d,c)>
       \operatorname{Sec}(a,c,d).}
\tag{1}
\]

For a pointwise proof set

\[
u=\frac{a+\theta(c-a)}d,\qquad
v=\frac{a+\theta(d-a)}c.
\]

One has v>u>0. For 0<=theta<1 their product is less than one, since
the two numerators are respectively less than c and d. The exact
identity

\[
g(u)-g(v)=
\frac{(v-u)(1-uv)}{(1+u)^2(1+v)^2}>0
\tag{2}
\]

therefore proves (1) by integration. This also explains the equality
when c=d.

We shall also use the following elementary starting-point monotonicity:
for a fixed 0<c<=d, the function z -> Sec(z,d,c) is strictly decreasing
on 0<z<c. Indeed g_d(s)=g(s/d) strictly decreases on 0<s<d, and

\[
\partial_z\operatorname{Sec}(z,d,c)
=\frac{\operatorname{Sec}(z,d,c)-g_d(z)}{c-z}<0.
\tag{3}
\]

The endpoint c=d causes no loss of strictness, since the integrand
still strictly decreases in the interior.

## 2. The two actual norm floors as secants

Assume the actual reverse-next data satisfy

\[
0<a<c,\quad a<d,\quad a<r,\qquad cd<4,\quad dr<4,
\]
\[
q=\frac{(c+d)(d+r)}{d^2+4}>1.
\]

Put

\[
A_0=\frac{4-cd}{c+d},\qquad
B_0=\frac{4-dr}{d+r}.
\tag{4}
\]

The star bounds make A0,B0 positive. The positive forward factor
makes A0<r and B0<c. Recall

\[
F_\eta(q)=1+\eta^2q-\eta q\frac{\log q}{q-1}.
\]

Direct substitution in the secant formula gives the two exact identities

\[
F_{d/(c+d)}(q)=\operatorname{Sec}(B_0,d,c),\qquad
F_{d/(d+r)}(q)=\operatorname{Sec}(A_0,d,r).
\tag{5}
\]

The actual incoming norm is v=Sec(a,c,d), so its missing-control
floor is the first inequality below. The actual outgoing norm is
at least the second F-floor and at most Sec(a,r,d), because the
next reverse centre is at least the actual global minimum a.
Consequently the following two unchanged-coordinate conditions hold:

\[
\operatorname{Sec}(a,c,d)\ge\operatorname{Sec}(B_0,d,c),
\]
\[
\operatorname{Sec}(a,r,d)\ge\operatorname{Sec}(A_0,d,r).
\tag{6}
\]

These are consequences of the actual lift. Neither condition asserts
that the artificial solved boundary norm satisfies an outgoing floor.

## 3. The order bound

Let

\[
K=a^2+4,\qquad b_*=\frac K{a+c}-a,
\]

and assume the smaller-side shape bound c<=b*. Then (6) forces

\[
\boxed{d\le b_*.}
\tag{7}
\]

Suppose instead that d>b*>=c. Formula (1), applied to c<d, gives

\[
\operatorname{Sec}(a,d,c)>
\operatorname{Sec}(a,c,d)
\ge\operatorname{Sec}(B_0,d,c).
\]

By the strict starting-point monotonicity (3), B0>a. Using (4),
this is equivalent to

\[
(a+d)(a+r)<K.
\]

Since d>b*=K/(a+c)-a, it follows that

\[
a+r<\frac K{a+d}<a+c,\qquad\text{hence }r<c<d.
\]

Apply (1) again, now to r<d. The second inequality in (6) implies

\[
\operatorname{Sec}(a,d,r)>
\operatorname{Sec}(a,r,d)
\ge\operatorname{Sec}(A_0,d,r).
\]

The same starting-point monotonicity forces A0>a. But d>b* is
equivalent to (a+d)(a+c)>K, hence to A0<a. This contradiction proves (7).

There is also a precise equality statement. If d=b*>c, the first
strict swapped order still forces r<c, and the second one would
force A0>a even though A0=a. Thus equality in (7) can only occur
when d=b*=c. In that case the first inequality in (6), together
with (3), gives B0>=a and hence r<=c. If r<c the second strict
swapped order again contradicts A0=a. Therefore

\[
d=b_*\quad\Longrightarrow\quad c=d=r=b_*.
\tag{8}
\]

For the actual positive reverse factor and c<=b, one has
(a+c)^2<=(a+b)(a+c)<K, hence c<b*. Thus the actual case is
strictly d<b*. The weak form (7) retains its closed boundary limits.

## 4. The reduced shape lower face

Use t=a/(a+c), x=(d-a)/(a+c), and k=K/(a+c)^2. Then

\[
\frac{b_*}{a+c}=k-t,\qquad \frac d{a+c}=t+x.
\]

Consequently (7) is exactly

\[
\boxed{k\ge2t+x.}
\tag{9}
\]

Together with the accepted smaller-side bound k>=1 and the
nonshort hand scale a<4/5, a reverse-next necessary point therefore
satisfies

\[
k\ge\max\{1,\ 2t+x,\ (29/4)t^2\}.
\tag{10}
\]

The last lower bound may be made weak in an enlarged domain.
The incident-upper residual N is strictly increasing in k by
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
Thus replacing k by the maximum in (10) preserves the necessary
inequality N<0, while keeping the exact incoming secant and both
k-independent incoming norm conditions.

No k-dependent star, outgoing-floor or Casimir condition is moved
without a separate proof. In particular, (10) supplies a new
lower-face reduction, not a completed exclusion. Proving the
remaining scalar residual sign on these three lower faces is still
open here.
