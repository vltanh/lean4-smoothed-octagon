# Scalar shape monotonicity for the nonshort boundary residual

Date: 2026-11-07 UTC. Hand proof, reviewed independently.
The underlying boundary comparison is in
[MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md).

This is a hand identity and sign proof. It is a necessary-domain reduction;
the endpoint signs required for a complete nonshort hand exclusion remain
open. Its independent review is recorded in
[MIXED_NONSHORT_SHAPE_REDUCTION_AUDIT](MIXED_NONSHORT_SHAPE_REDUCTION_AUDIT.md).

Use the boundary `b*=K/T-a` and its upper incident norm `u=U(aT/K)`.
Normalize all margins by `T=a+c`, and write

\[
t=a/T,\quad x=(d-a)/T,\quad k=K/T^2,\quad
W=1+x,\quad Y=x(x+2),\quad d_0=t+x,
\]
\[
B=k+2tx+x^2,\quad Z=qB/W,\quad q>1.
\]

Here `0<t<1/2`, `x>0`, and the smaller-turn shape condition is `k>=1`.
The actual incoming secant is

\[
v=1+\frac{(1-t)^2}{1+x}
 -(1-t)\frac{\log(1+x)}x<1-t+t^2.
\]

The upper-envelope diagonal and outgoing norm, in these units, are

\[
H_0:=16h_U/T^2=\frac{k}{t}(v-1+t^2)+t(2-t),
\]
\[
w_U=\frac{k^2-kt+t^2+H_0Y+vY^2}{B^2}.
\]

Consequently the forward stationary residual at the upper incident norm is

\[
\begin{aligned}
R:=R_d(U_*)/T={}&(1-t)+Z-d_0^2/W-d_0^2/Z+d_0^3/B-d_0\log q\\
 &-Wv-Zw_U+d_0(H_0+2vY)/B.
\end{aligned}
\]

The already proved sign of `R_u` says that the necessary boundary root
ceiling is exactly `R<0` (weak closure `R<=0`). Multiply by a positive
factor and put

\[
N=tBqW R.
\]

**Lemma.** At fixed `t,x,q,v`, `N` is affine and strictly increasing in `k`.

**Proof.** Substitution of the displayed formulas cancels the quadratic
terms in `k`. The coefficient `A` of `k` is

\[
\begin{aligned}
A/q={}&x[(1-v)(1+tW)-t(1-t^2)]\\
 &+(q-1)[t^2(1+2x-x^2)+2tx^2+(1-v)Y]
 -t d_0W\log q.
\end{aligned}
\]

Its coefficient of `v` is

\[
A_v=-qx[qx+2q+tW-x-1]<0,
\]

because the bracket equals `(q-1)(x+2)+1+tW`.
Its coefficient of `log q` is `-q t d_0 W<0`. Use the incident ceiling
`v<1-t+t^2` and the elementary strict inequality `log q<q-1`. Direct
collection then gives

\[
A>qt x(1-t)[(q-1)(2x+1)+tx]>0.
\]

All signs have been justified term by term. This proves the lemma.

For a proposed low-scale exclusion, `a^2<=1/4` is equivalent to
`k>=17t^2`, because `a^2=4t^2/(k-t^2)`. Thus any such necessary point
has `k>=max(1,17t^2)`, and its negative residual implies a negative
residual numerator at the lower endpoint `k=max(1,17t^2)`. The remaining
root/first-event contradiction may therefore be proved at those two
explicit shape endpoints. This does not assert that the endpoint is an
actual trajectory or retains every original geometric constraint.
