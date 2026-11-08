# Positive-diagonal scale comparison for a general short bridge

Research checkpoint, 2026-11-07. This proves one scalar monotonicity
needed for M2. The upper comparison faces are still separate obligations;
this note does not close the general short-bridge exclusion or M2.

The general comparison is now completed in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md)
and its independent audit. The scope of this constituent lemma is retained.

## 1. Actual window and notation

Work in an actual finite normal closed period. Let a reverse centre of
globally smallest active margin `a` lie between two short forward runs.
Write the adjacent bridges as `(A,B,C,a)` and `(a,b,c,Dright)`.
The proved centre minima and bridge order give

`a<=A<C<=B`, `a<=Dright<b<=c`.

Exchange left and right if necessary so `C<=b`. Normalize by a:

\[
\alpha=A/a,\quad \beta=B/a,\quad x=C/a,\quad y=b/a,
\qquad 1\le\alpha<x\le\beta,\quad x\le y.
\]

The two exact left turn secants also give the stronger order
`beta<=alpha*x`. To see this, parameterize their two averaging intervals
by `p(t)=[A+t(C-A)]/B` and `q(t)=[a+t(B-a)]/C`, `0<=t<=1`.
If `AC<aB`, or if `AC=aB` and `B>C`, then `p<=q`, `pq<=1`, and
the symmetry and strict monotonicity of `z/(1+z)^2` imply
`g(p)>g(q)` on an interval, where `g(z)=1-z/(1+z)^2`.
This contradicts the equal averages. The equal-turn case has `A=a`.

Put

\[
U(r)=1-r+r^2,\quad
\rho=\frac{a^2}{a^2+4},\quad \sigma=\alpha^2-1,
\quad \lambda=\frac1{1+\rho\sigma},
\]
\[
S=1+x,\quad Q=\alpha(\alpha+\beta),\quad
\mathcal D=(\alpha+\beta)^2+(1+x)^2-(\beta+x)^2,
\quad d=\lambda\rho\mathcal D.
\]

This note treats `Dcal>0`. The actual common turn norms `u=8nuL`,
`v=8nuR` obey

\[
u<V(x),\text{ or }u=V(x)\text{ on the equal-centre face},\quad
v\le V(y),\quad
u<U\left(\frac\alpha{\alpha+\beta}\right),\quad
v<U\left(\frac1{1+y}\right).
\tag{1}
\]

The strict far reverse derivative supplies the third bound; the last
bound follows either from the turn secant or the strict central reverse
derivative. `V` is the function in the [equal-centre proof](MIXED_GLOBAL_SHORT_BRIDGE_EQUAL_CENTRES.md). Positive middle
reverse duration is `rho<1/[S(1+y)]`.

Central stationarity and exact same-lift transport give

\[
E=1+\frac1S+\frac1{1+y}-\rho+\log[\rho S(1+y)]
 -(1-u)S-(1-v)(1+y),
\]
\[
F_0=E-\rho\mathcal D u,\qquad F=\lambda F_0,
\quad w=\lambda^2v-dF,\quad E_L=du-F.                 \tag{2}
\]

The genuine left outer root maximum is

\[
R(\rho)=L(w)+G_{1+\beta/\alpha}(u)
          -h(P/\alpha^2)-E_L,
\quad P=1/\rho+\sigma,
\quad T=P/Q,                                          \tag{3}
\]

with the same primitives as the [equal-centre note](MIXED_GLOBAL_SHORT_BRIDGE_EQUAL_CENTRES.md). On its genuine root
domain, `3/4<w<f'(T)`, the maximizing parameter is
`tau=tau*(w)` with `2<tau<T`, and `w=U(1/tau)`.

## 2. The central residual remains strictly negative

Let `D0(x)=2+4x-2x^2`. Since `beta<=alpha*x` and `alpha<x`,

\[
\mathcal D\ge\alpha D_0(x)+(1+2x)(\alpha-1)^2.
\]

If `D0>=0`, this implies `Dcal>=D0`. If `D0<0`, the same comparison
follows from the present hypothesis `Dcal>0`. Thus always `Dcal>=D0`.
The coefficients of u,v in `E-rho D0 u` are positive:
`S-rho D0>0` and `1+y>0`. Raise the norms to `V(x),V(y)` and apply
the strict equal-centre central residual bound. It gives

\[
\boxed{F_0<0,\qquad F<0,\qquad w>\lambda^2v.}        \tag{4}
\]

These statements persist throughout the scalar interval
`0<rho<1/[S(1+y)]`; they do not assert that the comparison points
are geometric trajectories.

## 3. Exact derivative and a rational upper comparison for the norms

Differentiate (2)--(3) with all ratios and the actual norms fixed. With

\[
F_0'=1/\rho-1-\mathcal D u=P-\alpha^2-\mathcal D u,
\]

one obtains

\[
\boxed{R'=\lambda\{(1+\lambda-d\tau)F_0'
                -(\sigma+\tau\mathcal D)F-2\tau\sigma w\}.}
\tag{5}
\]

The identity `2Q-Dcal-sigma=2x(beta-1)>0` and `P>=tau Q`, `tau>=2`
give `1+lambda-d tau>0`. Since `F=(lambda^2v-w)/d`, the expression
in braces in (5) is strictly decreasing in u and v when all geometric
parameters and tau are fixed. Thus use the upper bounds

\[
u_*:=U\left(\frac\alpha{\alpha+\beta}\right),\qquad
v\le\min\left\{v_*,\frac w{\lambda^2}\right\},
\quad v_*:=U\left(\frac S{P-\sigma}\right).           \tag{6}
\]

Indeed the middle factor gives `S/(P-sigma)<1/(1+y)<=1/2`, and U is
decreasing there, proving the v-star bound. Equation (4) gives the other
bound. There is no assertion that norm substitution preserves stationarity
or a geometric path; it only lowers the displayed affine derivative.

Set

\[
Z=\alpha^2+\mathcal D u_*,
\quad N=\tau^2\{P^2w-(P-\sigma)^2v_*\},
\]
\[
R_c=\tau^2(2P-\sigma-\mathcal D\tau)(P-Z)
       -2\sigma\tau(\tau^2-\tau+1)P.                 \tag{7}
\]

If `N<=0`, use `v=w/lambda^2`; multiplying the braces in (5) by
`P tau^2` gives the lower bound `Rc>=Rc+tau N`.
If `N>=0`, use `v=v*`; the resulting lower bound is
`Rc+(tau+sigma/Dcal)N>=Rc+tau N`.
It remains to prove the single rational inequality

\[
\boxed{R_c+\tau N>0.}                               \tag{8}
\]

## 4. Compact positive-polynomial proof

Define

\[
C_0=2Q-\mathcal D+S,\quad L_0=C_0+Q-Z,\quad H_0=2Q-Z,
\]
\[
A_0=Q(Q-\mathcal D+S),
\quad B_0=Q^2-(2Z-\sigma)Q+\mathcal D Z-S^2-S\sigma-\sigma^2,
\]
\[
J_0=4A_0+2B_0-\sigma H_0.
\]

Here `C0>0` by the identity preceding (6), and

`Q-Dcal+S=beta(2x-alpha)-x>0`, so `A0>0`.

Write `t=tau-2>=0` and `z=P-tau Q>=0`. Direct algebra gives

\[
\frac{R_c+\tau N}{\tau}
=(\tau+1)z^2
 +[C_0t^2+(2L_0+2C_0+\sigma)t+4L_0]z
\]
\[
\hspace{18mm}
 +\tau\left[A_0t^2+
       \left(2A_0+\frac{J_0+\sigma H_0}{2}\right)t+J_0\right].
\tag{9}
\]

It suffices that `L0,H0,J0>0`. The complete positive coefficient
identities below prove this. Put

`alpha=1+h`, `x=alpha+j`, `beta=x+k`, where `h,k>=0` and `j>0`.

The tables give the coefficient of `j^i k^l` in, respectively,
`(alpha+beta)^2 L0`, `(alpha+beta)^2 H0`, and
`(alpha+beta)^2 J0`. Every omitted coefficient is zero. Each displayed
polynomial in h has nonnegative coefficients. The first two tables have
strict positive terms proportional to j, and the third has a strict
positive term proportional to j squared. Consequently all three
polynomials are strictly positive on the actual short-bridge domain.

### Coefficients for L0

| i | l | Coefficient |
|---:|---:|---|
| 4 | 0 | $4$ |
| 3 | 1 | $12$ |
| 3 | 0 | $21 h + 18$ |
| 2 | 2 | $12$ |
| 2 | 1 | $45 h + 39$ |
| 2 | 0 | $43 h^{2} + 73 h + 29$ |
| 1 | 3 | $4$ |
| 1 | 2 | $27 h + 24$ |
| 1 | 1 | $58 h^{2} + 100 h + 40$ |
| 1 | 0 | $\left(h + 1\right) \left(39 h^{2} + 58 h + 16\right)$ |
| 0 | 3 | $3 h + 3$ |
| 0 | 2 | $15 h^{2} + 27 h + 11$ |
| 0 | 1 | $\left(h + 1\right) \left(5 h + 2\right) \left(5 h + 6\right)$ |
| 0 | 0 | $h \left(h + 1\right)^{2} \left(13 h + 16\right)$ |

### Coefficients for H0

| i | l | Coefficient |
|---:|---:|---|
| 4 | 0 | $2$ |
| 3 | 1 | $6$ |
| 3 | 0 | $10 h + 8$ |
| 2 | 2 | $6$ |
| 2 | 1 | $22 h + 18$ |
| 2 | 0 | $22 h^{2} + 36 h + 13$ |
| 1 | 3 | $2$ |
| 1 | 2 | $14 h + 12$ |
| 1 | 1 | $32 h^{2} + 54 h + 20$ |
| 1 | 0 | $\left(h + 1\right) \left(23 h^{2} + 34 h + 8\right)$ |
| 0 | 3 | $2 h + 2$ |
| 0 | 2 | $10 h^{2} + 18 h + 7$ |
| 0 | 1 | $\left(h + 1\right) \left(17 h^{2} + 28 h + 8\right)$ |
| 0 | 0 | $3 h \left(h + 1\right)^{2} \left(3 h + 4\right)$ |

### Coefficients for J0

| i | l | Coefficient |
|---:|---:|---|
| 6 | 0 | $8$ |
| 5 | 1 | $32$ |
| 5 | 0 | $56 h + 40$ |
| 4 | 2 | $48$ |
| 4 | 1 | $184 h + 136$ |
| 4 | 0 | $\left(4 h + 4\right) \left(44 h + 21\right)$ |
| 3 | 3 | $32$ |
| 3 | 2 | $216 h + 168$ |
| 3 | 1 | $454 h^{2} + 696 h + 236$ |
| 3 | 0 | $304 h^{3} + 688 h^{2} + 464 h + 84$ |
| 2 | 4 | $8$ |
| 2 | 3 | $104 h + 88$ |
| 2 | 2 | $386 h^{2} + 624 h + 226$ |
| 2 | 1 | $572 h^{3} + 1352 h^{2} + 968 h + 196$ |
| 2 | 0 | $292 h^{4} + 890 h^{3} + 923 h^{2} + 358 h + 32$ |
| 1 | 4 | $16 h + 16$ |
| 1 | 3 | $114 h^{2} + 200 h + 80$ |
| 1 | 2 | $304 h^{3} + 760 h^{2} + 584 h + 132$ |
| 1 | 1 | $348 h^{4} + 1110 h^{3} + 1224 h^{2} + 528 h + 64$ |
| 1 | 0 | $h \left(h + 1\right) \left(139 h^{3} + 384 h^{2} + 336 h + 96\right)$ |
| 0 | 4 | $6 \left(h + 1\right)^{2}$ |
| 0 | 3 | $\left(4 h + 4\right) \left(9 h^{2} + 15 h + 5\right)$ |
| 0 | 2 | $80 h^{4} + 268 h^{3} + 317 h^{2} + 154 h + 24$ |
| 0 | 1 | $h \left(h + 1\right) \left(73 h^{3} + 210 h^{2} + 196 h + 64\right)$ |
| 0 | 0 | $h^{2} \left(h + 1\right)^{2} \left(21 h^{2} + 42 h + 16\right)$ |


Equations (5)--(9) prove `R'(rho)>0` throughout the genuine outer-root
domain when `Dcal>0`.

## 5. Remaining comparison faces

This monotonicity has not by itself excluded the actual root. Increasing
rho can meet the central zero-factor face, the outer derivative face,
or the lower norm face `w=3/4` (with a possible simultaneous `T=2`).
The last face is new relative to equal centres, since lambda is no longer
one. Their signs must be proved before claiming a general short-bridge
minimum principle. Nonpositive Dcal is also a separate case. The actual
same-lift and positive-root requirements have not been dropped.

## Independent audit and supplementary checks

The [joint independent internal hand audit](MIXED_GLOBAL_SHORT_BRIDGE_AUDIT.md)
reviews the same-lift, comparison-domain and coefficient-table interfaces.
The corresponding exact checker is
[`mixed_global_short_bridge_scale_certificate.py`](../explorations/mixed_global_short_bridge_scale_certificate.py).
These are hand and algebraic results, not Lean kernel validation.
