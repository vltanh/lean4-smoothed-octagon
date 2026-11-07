# Secant concavity and endpoint shape reduction for a reverse successor

Date: 2026-11-07 UTC. Hand proofs, reviewed independently in
[MIXED_NONSHORT_SHAPE_REDUCTION_AUDIT](MIXED_NONSHORT_SHAPE_REDUCTION_AUDIT.md).

This note supplies hand reductions. It does not prove the remaining endpoint
signs and is not a completed reverse-next exclusion.

## 1. A strictly concave weighted secant deficit

For `0<=a<d` and `r>0`, define

\[
\operatorname{Sec}(a,r,d)
 =1-\frac r{d-a}\int_a^d\frac{s}{(r+s)^2}\,ds,
\qquad
J_{a,d}(r)=(r+d)^2[1-\operatorname{Sec}(a,r,d)].
\tag{1}
\]

**Lemma 1.** The function `J_{a,d}` is strictly concave on `(0,infinity)`.

**Proof.** Differentiate the continuous rational integrand in (1) twice:

\[
J_{a,d}''(r)=\frac2{d-a}\int_a^d
 \frac{s(s-d)[s(2d+3r)-dr]}{(r+s)^4}\,ds.
\tag{2}
\]

The integrand is positive for `0<s<s0`, zero at `s0`, and negative
for `s0<s<d`, where `s0=dr/(2d+3r)` lies strictly between zero and d.
For the interval starting at zero, elementary integration gives

\[
J_{0,d}(r)=\frac{r(r+d)^2}{d}\log(1+d/r)-r(r+d),
\]
\[
J_{0,d}''(r)=-d/r-6+(4+6r/d)\log(1+d/r)<0.
\tag{3}
\]

The strict sign in (3) follows without a series remainder: for `z>0`,

\[
\frac{z(z+6)}{4z+6}-\log(1+z)>0,
\tag{4}
\]

because its value at zero is zero and its derivative is

\[
\frac{z^3}{(z+1)(2z+3)^2}>0.
\]

If `a<=s0`, removing the interval `[0,a]` from the integral in (2)
removes only a nonnegative part, so the remaining integral is strictly
negative by (3). If `a>=s0`, its entire remaining integrand is negative
apart from endpoints. These two cases establish `J_{a,d}''<0`.

The proof also gives `J'_{a,d}(r)>(a+d)/2`, because its decreasing
derivative has the limit `(a+d)/2` at infinity. In particular, for every
`r>=r0>0`,

\[
J_{a,d}(r)\ge J_{a,d}(r_0)+\frac{a+d}{2}(r-r_0).
\tag{5}
\]

The inequality is strict if `r>r0`.

## 2. Exact dependence of the boundary root on the shape parameter

Use the normalized variables of [MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md):

\[
t=a/T,\quad x=(d-a)/T,\quad k=K/T^2,\quad p=t+x,
\quad W=1+x,\quad H=t+x(x+2),
\]
\[
B=k+2tx+x^2,\quad r_0=qB/W-p,\quad
V=1-t+t^2,\quad D_0=qH/W-p.
\tag{6}
\]

Here `r0` denotes the normalized actual margin `r/T`; it is not the
zero-factor comparison margin from the upper-envelope gap lemma.
The incoming norm

\[
v=\operatorname{Sec}(t,1-t,t+x)
\]

is held fixed together with `t,x,q`. Since `H-pW=(1-t)x>0` and `q>1`,
one has `D0>0`.

Define the following quantities, all independent of `k`:

\[
\begin{aligned}
n_1={}&H(1-t-p^2/W-p\log q)+(p-HW)v+p(2p^2-V),\\
n_0={}&p[(H^2-p^2)v+p^2(1+2(1-t)x)-HpW/q],\\
A={}&-n_1/D_0,\qquad C=-n_0/D_0.
\end{aligned}
\tag{7}
\]

**Lemma 2.** The solved boundary root has the exact form

\[
\boxed{w_*(k)=1-\frac A B-\frac C{B^2}.}
\tag{8}
\]

**Proof.** In these units the constant `4/T^2` is
`F=k-t^2=B-p^2`, and the boundary quantity `L0/T^2` is
`k+1-t=B-p^2+V`. Central stationarity and transport give

\[
16H(h_d/T^2)=B^2w_*+(H^2+F)v-F(k+1-t).
\]

The normalized forward stationarity equation is

\[
C_d-Wv-(qB/W)w_*+16p(h_d/T^2)/B=0,
\]
\[
C_d=1-t+qB/W-p^2/W-p^2W/(qB)+p^3/B-p\log q.
\]

Eliminating the diagonal gives

\[
B^2D_0w_*
 =HB C_d+[p(H^2+F)-HBW]v-pF(k+1-t).
\tag{9}
\]

Substitute `F=B-p^2` and `k+1-t=B-p^2+V`. The coefficient of `B^2`
is `Hq/W-p=D0`, the coefficient of `B` is `n1`, and the constant term
is `n0` as displayed in (7). For the constant term, the elementary
identity `H+V-p^2=1+2(1-t)x` gives precisely that expression. Dividing
(9) by its positive denominator proves (8).

## 3. Concavity of the reverse comparison gap

**Lemma 3.** On any interval where `r0=qB/W-p>0`, the function

\[
\mathcal G(k)=B^2[w_*(k)-\operatorname{Sec}(t,r_0,p)]
\tag{10}
\]

is strictly concave.

Indeed (8) gives

\[
\mathcal G(k)=(W/q)^2J_{t,p}(r_0)-AB-C.
\]

Both `B` and `r0` are affine in `k`, with derivatives `1` and `q/W`.
Consequently

\[
\mathcal G''(k)=J_{t,p}''(r_0)<0
\tag{11}
\]

by Lemma 1. This calculation uses no transported Casimir cap or outgoing
norm floor.

## 4. A necessary endpoint alternative

Let `N(k)` be the normalized incident-upper residual numerator in
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md). That note proves

\[
N(k)=A_N k+B_N,\qquad A_N>0.
\]

Thus the necessary root ceiling `u*<U*` is `N(k)<0`, equivalently
`k<k_top:=-B_N/A_N`.

The necessary smaller-turn shape, sharpened reverse-centre scale and
reverse-turn log-concavity supply

\[
k\ge k_{\rm low}:=\max\left\{1,\ 7t^2,\
 \frac{W[p+\sqrt{tp}]}q-2tx-x^2\right\}.
\tag{12}
\]

The third lower bound is important: it is exactly `r0>=sqrt(tp)`,
and ensures that the entire closed interval `[k_low,k_top]` remains in
the domain of the secant in (10). The strict actual scale can be
weakened to the displayed closed bound.

For the actual reverse successor, the boundary comparison gives
`w*<Sec(t,r0,p)`, so `G(k)<0`. Since `k_low<=k<k_top` and G is concave,
its value is at least the linear interpolation of its two endpoint
values. Therefore at least one of the following necessary alternatives
holds:

\[
\boxed{\mathcal G(k_{\rm low})<0
\quad\hbox{or}\quad \mathcal G(k_{\rm top})<0.}
\tag{13}
\]

At `k_top` the incident root equals its upper envelope, `u*=U*`, and
hence `w*=w_U`. At `k_low`, one of the three explicit lower bounds in
(12) is an equality. No claim is made that either endpoint is an actual
trajectory, retains compact inequalities depending on k, or inherits an
original norm floor. To finish an exclusion from (13), the endpoint
signs must be proved on correctly retained enlarged domains.

Some useful unchanged-coordinate restrictions are

\[
0<t<1/2,\quad x>0,\quad t(2+x)<1,
\quad v>g_{1-t}(t+x),
\]
\[
v\ge F_{p/W}(q),\qquad
\frac{W}{2p}<q<\frac Wp.
\tag{14}
\]

Here `t(2+x)<1` is incoming strict turn log-concavity. The upper q
bound is exactly the strict star condition `dr<4`; the lower q bound
is exactly the reverse-only symmetric centre gap `d^2+2dr>4` proved in
[MIXED_NONSHORT_UPPER_ENVELOPE_GAP](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md).
Every condition in (14) is independent of k. Conditions affected by k
may be used only after checking their direction of transfer or by
retaining their necessary bound on the original interval.
