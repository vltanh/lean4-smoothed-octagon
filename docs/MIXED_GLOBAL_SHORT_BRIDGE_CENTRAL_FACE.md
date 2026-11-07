# The central convex-chord face for either bridge-diagonal sign

Research proof checkpoint, 2026-11-07. This proves the entire central convex-chord
comparison face under the genuine strengthened two-secant order, for either
sign of the bridge diagonal. It is not the remaining M2 exclusion. The
coefficient identity is explicit in the accompanying CSV table. The proof
uses two displayed nonnegative multiples of the central factor constraint,
a complete positive integer remainder, and elementary inequalities. No numerical sign assertion,
Lean, Lake, typecheck, CI or word-length enumeration is used.

## 1. Scalar statement and its actual interface

Let

\[
1\le\alpha<x\le y,\qquad x\le\beta\le\alpha x,
\]

and set

\[
q=(1+x)(1+y),\quad P=q+\alpha^2-1,
\quad Q=\alpha(\alpha+\beta),
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\qquad
T=P/Q\ge2,\quad T_B=Q/\alpha^2,
\quad \lambda=q/P,\quad d=D/P.
\]

Assume the strengthened order

\[
\alpha\ge\frac\beta x+\frac27(\beta-x).
\tag{S}
\]

There is no restriction on the sign of D. Write

\[
V(s)=1+\frac{s}{2(1+s)}-
 \frac{s}{s-1}\log\frac{2s}{1+s},\qquad
U(r)=1-r+r^2,
\]

and suppose `u<=V(x), v<=V(y)`. Define

\[
E=(u-1)(1+x)+(v-1)(1+y)+1+
 \frac1{1+x}+\frac1{1+y}-\frac1q,
\]
\[
w=\lambda^2v+d^2u-d\lambda E,
\qquad E_L=2du-\lambda E.
\]

If

\[
\frac34\le w\le U(1/T),
\]

then the outer-root maximum satisfies

\[
\boxed{L(w)+uT_B-f(T_B)-h(P/\alpha^2)-E_L<0,}       \tag{1}
\]

where

\[
f(t)=t-t^{-1}-\log t,\quad h(t)=\log t-1+t^{-1},
\quad L(w)=\max_{t\ge2}\{wt-f(t)\}.
\]

The endpoint `w=3/4` is interpreted by `L(3/4)=log 2`. At `T=2`
the stated norm interval consists of that one point.

For the actual short-bridge problem, `alpha=A/a`, `beta=B/a`,
`x=C/a`, `y=b/a`. Reflection chooses `x<=y`; the two exact turn secants
give the two norm bounds and (S). For clarity, if the incoming bridge is
continued from `(beta,alpha)=(x,1)`, the audited secant comparison gives

\[
\alpha_\beta=\frac\alpha\beta+\frac\eta\xi
 \left\{\frac x\beta+\frac{x-\alpha}{\beta-1}\right\},
\qquad\eta/\xi\ge2/7.
\]

Therefore `d[(alpha+2x/7)/beta]/d beta>0`, and integration gives (S).
This is an actual necessary order, not an assumption about arbitrary
endpoint data. The equality
`q=(1+x)(1+y)` is the auxiliary central zero-duration face. No assertion
is made that points on this scalar face are positive-duration geometric
trajectories. These are the exact same-lift transport formulas at actual
data; on the zero-factor face they define scalar comparison values.

This result includes weak incident-root inequalities and the closed
strengthened-order boundary. The truncated region `w<3/4` is a separate
value comparison. No condition on D is needed here.

## 2. An elementary rational upper bound

The convex function L lies below its chord on `[3/4,U(1/T)]`:

\[
L(w)\le\log2+m(T)(w-3/4),
\quad
m(T)=\frac{4T^2[\log(T/2)-1+2/T]}{(T-2)^2}.
\]

The expression in (1) is therefore at most

\[
\left[\frac{4T^2(w-3/4)}{(T-2)^2}-1\right]\log(T/2)
+\hbox{terms rational in the scalar variables}.       \tag{2}
\]

The log coefficient is nonpositive by `w<=U(1/T)`. Put
`zeta=(T-2)/(T+2)` and use

\[
\log(T/2)\ge2\zeta+\frac23\zeta^3.
\]

This follows by differentiating with respect to zeta: the derivative
of the difference is `2*zeta^4/(1-zeta^2)>=0`, and the difference is
zero at zeta=0. The resulting upper bound is

\[
\mathcal R=
m_0(w-3/4)+(u-1)T_B+1+T_B^{-1}-(TT_B)^{-1}
-E_L-2\zeta-\frac23\zeta^3,                         \tag{3}
\]
\[
m_0=2(1+\zeta)+\frac23\zeta(1+\zeta)^2,
\qquad 2\le m_0\le T.
\]

Indeed `m0>=2`, and

\[
T-m_0=\frac{2\zeta(1+\zeta)(2+\zeta^2)}{3(1-\zeta)}\ge0.
\]

All formulas extend continuously at T=2.

## 3. Raising both norms is a scalar upper bound

The expression (3) is affine in u,v. Both coefficients are strictly
positive. Here are the signs, so no root-domain condition is silently
imposed after a norm is raised.

Put `S=1+x`, `ell=lambda*S`. The v coefficient is

\[
\lambda(1+y)\left[1-m_0
 \frac{D-q/(1+y)}P\right]>0,
\]

because

\[
D-Q=\alpha\beta+1+2x-2\beta x<1+x=q/(1+y),
\qquad m_0\le P/Q.
\]

The u coefficient is

\[
T_B+\ell-2d+m_0d(d-\ell).                          \tag{4}
\]

For d<=0 it is positive term by term: `TB+ell>0`, `-2d>=0`,
and `m0*d*(d-ell)>=0`. For d>0, the geometric inequalities give
`D<S^2`, `ell>2d`, and

\[
d<d_{\max}=Q/P+S/P=1/T+\ell/q.
\]

Replacing `m0` by T decreases (4). For
`F(t)=TB+ell-2t+T*t*(t-ell)`,

\[
F(d)-F(d_{\max})
=T(d-d_{\max})(d+d_{\max}-\ell-2/T)>0,
\]

since the last factor is less than
`(1/q-1/2)*ell-1/T<0`. Finally

\[
F(d_{\max})=
\frac{(q-1)[(\alpha+\beta)^2-(1+x)^2]}{QP}\ge0.
\]

Thus both norms may be raised in (3), independently of what happens
to the auxiliary w interval. A second elementary logarithm lower bound
gives

\[
V(s)\le V_+(s)=
\frac{131s^4+229s^3+163s^2+47s+6}
 {6(s+1)(3s+1)^3}.                                  \tag{5}
\]

For completeness, put `r=(s-1)/(s+1)` in `(0,1)`. Then

\[
V(s)=\frac54+\frac r4-\frac{1+r}{2r}\log(1+r),
\]

and use `log(1+r)>=2a+2a^3/3`, `a=r/(2+r)`. Equation (5) is the exact
rational simplification. Consequently it is enough to prove (3)
negative after `u=V_+(x),v=V_+(y)`.

## 4. Explicit finite integer identity

This section specifies the polynomial independently of its checker.
Write

\[
H=P+2Q,\quad C=5P^2+8PQ+12Q^2,
\]
\[
e=q(u-1)(1+x)+q(v-1)(1+y)+q+(1+x)+(1+y)-1=qE,
\quad W=q^2v+D^2u-De.
\]

Define the polynomial, affine in u,v,

\[
\begin{aligned}
\mathcal N(u,v)={}&QC(4W-3P^2)
+3PH^3(u-1)(\alpha+\beta)^2+3QPH^3\\
&+3\alpha^2PH^3-3\alpha^2QH^3
-3QH^3(2Du-e)\\
&-QP\{6(P-2Q)H^2+2(P-2Q)^3\}.
\end{aligned}                                      \tag{6}
\]

Direct multiplication of (3) gives
`N(u,v)=3*Q*P*H^3*R(u,v)`.
Let `N0=N(0,0)`, `Nu=N(1,0)-N0`, `Nv=N(0,1)-N0`, and

\[
n(s)=131s^4+229s^3+163s^2+47s+6,
\quad d(s)=6(s+1)(3s+1)^3.
\]

The cleared negative upper bound is the polynomial

\[
p=-N_u n(x)d(y)-N_v n(y)d(x)-N_0d(x)d(y).             \tag{7}
\]

It remains to prove p>0. Parameterize the strengthened order by

\[
\alpha=1+h,\quad x=1+h+j,\quad y=x+\ell,
\quad\beta=x+\frac{7hxz}{(7+2x)(1+z)},
\tag{8}
\]

where `h,z,ell>=0` and `j>0`. Write

\[
B=(7+2x)(1+z),\qquad K=7hxz.
\]

This covers the strict upper boundary in (S); the closed boundary is
handled below. The case h=0 forces beta=x and is covered by z=0.
The degree of p in beta is five. After (8), define the polynomial
`p_hat=B^5*p` and the central-factor generator

\[
G=B\{j(j+2)+(h+j+2)\ell-2h(h+1)\}
       -2(h+1)K=B(P-2Q)\ge0.
\tag{9}
\]

The exact integer identity is

\[
\boxed{\widehat p=
 j^2z^3(1625975783424+1310584209408z)G
 +P_+(h,j,z,\ell).}
\tag{10}
\]

Every coefficient of P+ is a positive integer. Its complete static table
is [mixed_global_short_bridge_central_face_positive.csv](../explorations/mixed_global_short_bridge_central_face_positive.csv), containing exactly 13,348
rows. A row `(h,j,z,ell,coefficient)` specifies that integer times the
monomial whose four exponents are listed. Every unlisted coefficient is
zero. The exponent-column names indicate exponents, not additional
variables. This table, together with (6)--(10), is the entire certificate;
no optimizer or floating sign is a premise.

For transparency, the only three negative coefficients of p_hat before
subtracting the displayed G multiple are

\[
\begin{array}{c|r}
\text{monomial}&\text{coefficient}\\
hj^2z^4&-75621740838912\\
hj^2z^5&-41938694701056\\
h^2j^2z^5&-59431496712192.
\end{array}
\]

The two displayed G multipliers remove those coefficients and leave
only the positive remainder. In particular it contains

\[
29720334827520\,j^3+6129819058176\,j^3z^5.
\tag{11}
\]

Consequently (10) gives p_hat>0 for every j>0 and G>=0. There is no D
generator and no condition on its sign. All factors in the original
cleared denominator `3*Q*P*(P+2Q)^3*d(x)*d(y)` are positive.

If equality holds in (S), take the leading coefficient in z in (10),
or divide by z^5 and let z tend to infinity. The first summand stays
nonnegative because `G/z>=0` in that limit, and the second term of (11)
gives a strictly positive limiting numerator. The clearing factor tends
to the positive value `(7+2x)^5`, so the original rational inequality
remains strict at that boundary.

This proves (1) for either sign of D. The fixed replay script
[mixed_global_short_bridge_central_face_certificate.py](../explorations/mixed_global_short_bridge_central_face_certificate.py) verifies the exact norm and
clearing identities, all 13,348 literal positive entries, and the whole
integer identity (10); its ten exact checks pass. It uses only rational
and integer arithmetic. The short two-multiplier identity replaces the
previous positive-D certificate and its 103 multipliers, while the
stronger necessary order removes the previous D restriction.

## 5. Scope of the remaining comparison

The central zero-factor face is now negative whenever the true outer
norm lies in `[3/4,U(1/T)]`, for either bridge-diagonal sign. The value
in the region `w<3/4` is `R(2)`, and must be checked separately: extending
the convex chord below 3/4 would be an invalid upper bound. The [truncated central value](MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_FACE.md)
is proved separately. Both are joined with the scale and endpoint
comparisons in [MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md).
This lemma alone is not an M2 exclusion or an unrestricted theorem.
