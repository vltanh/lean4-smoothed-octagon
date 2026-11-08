# The normalized short-root residual increases with the incoming norm

Date: 2026-11-08 UTC. Complete scalar hand lemma; the standalone
[identity and domain audit](MIXED_SMALLER_SHORT_ROOT_INCOMING_AUDIT.md)
checks the four displayed corner expressions. This is a reduction,
not by itself an exclusion of an actual short bridge.

The residual in the
[normalized-root scale theorem](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md)
has a useful monotonicity on the entire ordered short-shape domain.
No lower bound on x other than x>1, no sign of the short diagonal,
and no norm floor or Casimir cap is needed.

Fix

\[
1\le\alpha\le x\le\beta,\qquad x>1,
\quad S=1+x,\quad r_A=\frac\alpha{\alpha+\beta},
\]
\[
0<q\le\frac17,\qquad 0<p\le r_A.
\tag{1}
\]

Then the envelope residual satisfies

\[
\boxed{\frac{\partial}{\partial u}R^*_{p/q}(q)>0.}
\tag{2}
\]

The derivative is independent of u. Thus an upper estimate for the
original incoming norm may be substituted into this scalar residual,
at unchanged shape, p and q. This assertion does not transport any
other norm ceiling or floor after that substitution.

## 1. A bilinear derivative

Write

\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad d=D/\alpha^2,\quad
\varepsilon=1-\alpha^{-2},\quad n=S/\alpha^2,
\]
\[
E_0=S(u-1)+S^{-1},
\]
\[
\begin{split}
A_1&=2\varepsilon+n+dE_0,\\
A_2&=\varepsilon^2+\varepsilon n+n^2+d^2u
 +d\varepsilon E_0-d(2S-1)/\alpha^2,\\
A_3&=2du+\varepsilon E_0-(2S-1)/\alpha^2.
\end{split}
\]

The exact normalized residual is

\[
R^*=E_0+\frac{u-1}{r_A}+r_A+1-pA_1+\log(p/r_A)
       +q(pA_2+p^{-1}-1-A_3).
\]

Its derivative is the bilinear polynomial

\[
\boxed{
R^*_u=S+r_A^{-1}-pdS
 +q\{p(d^2+d\varepsilon S)-2d-\varepsilon S\}.}
\tag{3}
\]

At fixed shape, a bilinear function on the rectangle
0<=p<=r_A, 0<=q<=1/7 is a convex combination of its four corner
values. It therefore suffices to check those four values. The p=0
corner is used only for the polynomial derivative (3); the original
logarithmic residual need not be defined there.

## 2. The two p=0 corners

At p=q=0, the value is S+1/r_A>0. At p=0,q=1/7, multiplication
by 7alpha^2 gives

\[
7\alpha^2R^*_u
 =6\alpha^2S+(5\alpha^2-1)
          +3(\alpha\beta-x)+4\beta x>0.
\tag{4}
\]

Every displayed term is nonnegative, and the first is positive.

## 3. The two p=r_A corners

For compact positive identities put

\[
z=\alpha-1\ge0,\quad h=x-\alpha\ge0,
\quad k=\beta-x\ge0.
\]

At least one of z,h is positive because x>1.
At p=r_A,q=0, the derivative equals

\[
R^*_u=\frac{P_0(z,h,k)}{\alpha(\alpha+\beta)},
\tag{5}
\]

where the complete numerator is

\[
\begin{split}
P_0={}&k^2+k\{2h^2+(3z+7)h+(z+1)(z+6)\}\\
 &+2h^3+(5z+6)h^2+(4z^2+11z+4)h
       +z(z^2+6z+6).
\end{split}
\tag{6}
\]

At p=r_A,q=1/7 it equals

\[
R^*_u=\frac{P_1(z,h,k)}{7\alpha^3(\alpha+\beta)},
\tag{7}
\]

where

\[
\begin{split}
P_1={}&k^2\{4h^2+4(z+1)h+7(z+1)^2\}\\
 &+k\{8h^3+2(6z^2+20z+11)h^2\\
 &\hspace{20mm}+(18z^3+88z^2+113z+41)h\\
 &\hspace{20mm}+(z+1)(6z^3+50z^2+79z+34)\}\\
 &+4h^4+6(2z^2+6z+3)h^3
       +(z+1)(30z^2+79z+34)h^2\\
 &+(24z^4+120z^3+186z^2+109z+20)h\\
 &+z(z+1)(6z^3+43z^2+72z+34).
\end{split}
\tag{8}
\]

Identities (5)--(8) follow by substituting p=r_A and the two q values
in (3), then x=1+z+h and beta=1+z+h+k. They display every term of
the two numerators. All terms are nonnegative, and the terms linear
in h or containing z give a strict positive value when z+h>0.
Both denominators are positive.

All four corner values are therefore strictly positive. The convex
combination argument proves (2) throughout (1), including the closed
derivative endpoints p=r_A and q=1/7. This is an incoming-norm scalar
comparison, not a new statement about the actual root's existence or
the physical completion cost.
