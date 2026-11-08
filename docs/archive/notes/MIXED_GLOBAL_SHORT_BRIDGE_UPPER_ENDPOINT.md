# The entire upper endpoint in the short-bridge minimum comparison

Research proof checkpoint, 2026-11-07. This proves a strict upper-endpoint
sign for either sign of the bridge diagonal. It is not a complete M2
exclusion. The proof uses an explicit square and a static table of 803
positive integer coefficients; no numerical sign, endpoint rank,
independently fitted covector, Lean/Lake, CI or word enumeration is used.

## 1. Exact statement

Suppose

\[
1\le\alpha<x\le y,\quad \beta\ge x,\qquad
\alpha\ge\frac\beta x+\frac27(\beta-x),              \tag{1}
\]

and `u<=V(x),v<=V(y)`, with

\[
V(t)=1+\frac{t}{2(1+t)}-
 \frac{t}{t-1}\log\frac{2t}{1+t}.
\]

Keep these dimensionless quantities and norms fixed. For every
`q>=q0=(1+x)(1+y)`, set

\[
\sigma=\alpha^2-1,\quad P=q+\sigma,
\quad Q=\alpha(\alpha+\beta),
\quad D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\]
\[
E=G_{1+x}(u)+G_{1+y}(v)-h(q),
\quad G_t(w)=wt-f(t),
\]
\[
f(t)=t-t^{-1}-\log t,\qquad h(t)=\log t-1+t^{-1},
\]
\[
w=\frac{q^2v+D^2u-DqE}{P^2},\quad
E_L=\frac{2Du-qE}{P},\quad
T=P/Q,\quad T_B=Q/\alpha^2.
\]

Then the zero-factor outer residual is strictly negative:

\[
\boxed{
R(T):=wT-f(T)+uT_B-f(T_B)-h(P/\alpha^2)-E_L<0.}       \tag{2}
\]

There is no restriction on the sign of D, no lower bound on w, and no
Casimir hypothesis in this scalar theorem. In particular it covers
the genuine reverse-derivative upper face `w=f'(T)`, and the auxiliary
`T=2` face used in the truncated-root comparison.

## 2. Why the strengthened order is an actual necessary condition

For a genuine incoming short bridge `(A,B,C,a)`, use
`alpha=A/a,beta=B/a,x=C/a`. The two exact turn secants define the
genuine branch alpha(beta), beginning at `(beta,alpha)=(x,1)`, and
the audited central comparison proves

\[
\alpha_\beta=\frac\alpha\beta+
 \frac\eta\xi\left\{\frac x\beta+
              \frac{x-\alpha}{\beta-1}\right\},
\qquad \eta/\xi\ge2/7,
\quad x>\alpha.
\]

Here eta and xi are the two strictly positive endpoint secant gaps.
Thus

\[
\frac{d}{d\beta}
 \frac{\alpha+2x/7}{\beta}
=\frac{(\eta/\xi)[x+\beta(x-\alpha)/(\beta-1)]-2x/7}
 {\beta^2}
\ge\frac{2(x-\alpha)}{7\beta(\beta-1)}>0.
\]

Integrating from beta=x yields (1), strictly when beta>x. This is a
quantitative consequence of the same actual two-secant branch; mere
weak order `alpha*x>=beta` is insufficient for other endpoint values.
The norm upper bounds come from the actual neighbouring-centre minimum
conditions. Reflection selects x<=y.

The transport formulas in Section 1 are exactly the common-lift formulas
at actual data. Their scale extensions below are scalar comparisons;
they are not asserted to preserve a trajectory or costate endpoints.

## 3. The endpoint numerator is decreasing

Let

\[
Z=D-Q,\quad H=G_{1+x}(u)+G_{1+y}(v)+1,
\quad M=(u-1)(\alpha+\beta)^2+\alpha\beta+1.
\]

Since `T*TB=P/alpha²`, the logarithms at the outer endpoint combine.
Direct substitution gives the exact numerator

\[
\begin{aligned}
N(q):=PQ R(T)
={}&(v-1)q^2+Zq\log q\\
 &+q(M+1-ZH)+Z+uZ^2-M.                              \tag{3}
\end{aligned}
\]

For q>=q0,

\[
N''(q)=2(v-1)+Z/q<0.                                \tag{4}
\]

Indeed `Z<1+x`. If Z<=0 the sign is immediate. Otherwise, putting
`s=1/(1+y)<1/2`,

\[
Z/q<s<2s(1-s)\le2(1-v),
\]

because `v<=V(y)<U(s)=1-s+s²`.
The strict upper bound is also immediate from
`V(y)=avg_[1,y](1-y*t/(y+t)^2)`: its integrand decreases strictly
from `U(1/(1+y))` to `3/4` on this nontrivial interval.

At q=q0, put

\[
E_b=(u-1)(1+x)+(v-1)(1+y)+1+
       (1+x)^{-1}+(1+y)^{-1}-q_0^{-1}.
\]

Then

\[
N'(q_0)=2(v-1)q_0+M+1+Z(1-E_b-q_0^{-1}).             \tag{5}
\]

Its u and v coefficients are respectively
`(alpha+beta)²-Z(1+x)>0` and `(1+y)[2(1+x)-Z]>0`.
Raise u and v to `U(1/(1+x)),U(1/(1+y))`. The resulting value is
strictly negative, as witnessed by the following short positive formula.
Write

`alpha=1+h,x=1+h+j,beta=x+k,y=x+ell`, with h,k,ell>=0,j>0,
and `S=h+j+2`, `X=h+j+1`. Then the negative of (5), multiplied by
`S²(1+y)`, is

\[
k^2X(\ell+S)+k(\ell P_1+SP_2)+X(\ell P_3+SP_4),    \tag{6}
\]

where

\[
\begin{aligned}
P_1={}&h^3+6h^2j+7h^2+9hj^2+22hj+10h
       +4j^3+15j^2+16j+4,\\
P_2={}&h^3+6h^2j+5h^2+9hj^2+16hj+4h
       +4j^3+11j^2+6j,\\
P_3={}&h^3+6h^2j+5h^2+9hj^2+16hj+4h
       +4j^3+12j^2+8j,\\
P_4={}&h^3+6h^2j+3h^2+9hj^2+10hj+4j^3+8j^2.
\end{aligned}
\]

All terms are nonnegative and `X*S*P4>0`. Consequently
`N'(q0)<0`; together with (4), N decreases strictly for q>=q0.

## 4. The initial value is negative

The initial value is affine in the norms:

\[
N(q_0)=v q_0^2-Zq_0 E_b+uZ^2+(q_0-1)(M-q_0).         \tag{7}
\]

Both norm coefficients are positive. The v coefficient is
`q0(1+y)(1+x-Z)>0`. Writing S=1+x, the u coefficient is

\[
(Z-S)(Z-(q_0-1)S)
+(q_0-1)[(\alpha+\beta)^2-S^2]>0.                  \tag{8}
\]

We may therefore use the elementary rational norm upper bound

\[
V(t)\le\overline V(t)=
\frac{55t^2+64t+25}{4(t+1)(17t+7)}.                  \tag{9}
\]

To verify it, put r=(t-1)/(t+1) in (0,1). The right side is
`3/4+r²/(12+5r)`. The equivalent logarithm bound is

\[
\log(1+r)\ge\frac r{1+r}
 \left(1+\frac r2-\frac{2r^2}{12+5r}\right).
\]

The derivative of the difference is

\[
\frac{r^3(16-5r)}{2(1+r)^2(12+5r)^2}>0,
\]

and the difference vanishes at zero.

Here is the complete finite integer certificate for the remaining
initial-value sign. Let

\[
n(t)=55t^2+64t+25,\qquad d(t)=4(t+1)(17t+7).
\]

Regard (7) as an affine polynomial `F(u,v)`, and write
`F0=F(0,0)`, `Fu=F(1,0)-F0`, `Fv=F(0,1)-F0`. Define

\[
p=-F_0d(x)d(y)-F_un(x)d(y)-F_vn(y)d(x).               \tag{10}
\]

It is quadratic in beta. The strengthened order (1) is parameterized by

\[
\alpha=1+h,\quad x=1+h+j,\quad y=x+\ell,
\quad\beta=x+\frac{7xh z}{(7+2x)(1+z)},              \tag{11}
\]

with `h,z,ell>=0,j>0`. Put `B=(7+2x)(1+z)`. The exact identity is

\[
\boxed{B^2p=73344\,h j^2z^2(h-1)^2+P_+(h,j,z,\ell).} \tag{12}
\]

The full static coefficient table of P+ is
[mixed_global_short_bridge_upper_endpoint_positive.csv](../explorations/mixed_global_short_bridge_upper_endpoint_positive.csv). Each row
`(h,j,z,ell,coefficient)` means that positive integer coefficient times
the indicated monomial. There are exactly 803 rows, all coefficients
are positive integers, and all unlisted coefficients are zero. The table
contains, in particular,

\[
1492992\,j^3+1492992\,j^3z^2.
\]

Equations (7), (10)--(12), together with that complete table, are an
explicit finite integer identity. The only negative coefficient of
the expanded left side is `-146688*h²*j²*z²`; the displayed square
removes it. Its two neighbouring coefficients become respectively
`92544*h*j²*z²` and `1141920*h³*j²*z²`, both positive. No optimization
or floating computation is a premise of the sign argument.

Thus p>0, and (7) is strictly negative. If equality holds in the order
bound in (1), take the leading coefficient in z in (12); the positive
`1492992*j³*z²` term gives the same strict conclusion. The case h=0
has beta=x and is already covered by z=0.

Combining `N(q0)<0` with Section 3 proves (2) for every q>=q0.
The fixed replay script [mixed_global_short_bridge_upper_endpoint_certificate.py](../explorations/mixed_global_short_bridge_upper_endpoint_certificate.py)
verifies all displayed algebraic identities, the 803 static positive
entries, and the exact square decomposition; all 13 checks pass under
Python 3.12 / SymPy 1.14.

## 5. Scope

The genuine same-lift upper-root endpoint is now strictly negative
throughout this two-short-bridge minimum domain. This includes either
sign of D, the derivative-boundary face, and T=2. It uses the quantified
two-secant order, not merely AC>=aB. It does not by itself exclude a
positive outer-root maximum in the interior. The central truncated value and both continuation branches are joined in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md).
That theorem places the minimum next to a nonshort run; M2 remains open.
