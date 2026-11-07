# A decreasing scale numerator for the truncated outer root

Research checkpoint, 2026-11-07. This proves a scalar monotonicity and
reduces the lower-norm face to two endpoint VALUE inequalities. Those
value inequalities are separate obligations; no M2 closure is asserted.

Use the actual two-short-bridge data and normalization of the general
central comparison. In this note `q=1/rho` is an inverse scale, not an
arc factor. Put

\[
S=1+x,\quad T_0=1+y,\quad q_0=ST_0,\quad
\sigma=\alpha^2-1,\quad P=q+\sigma,
\quad Q=\alpha(\alpha+\beta),
\]
\[
\mathcal D=(\alpha+\beta)^2+S^2-(\beta+x)^2\ge0,
\quad T_B=1+\beta/\alpha,\quad T=P/Q.
\]

The actual order is `1<=alpha<x<=beta<=alpha*x`, `x<=y`. The actual
turn norms obey `u<=V(x)`, `v<=V(y)`, as well as
`u<=U(alpha/(alpha+beta))`, `v<=U(1/(1+y))`. Hold all these ratios
and norms fixed in the scalar comparison. The relevant scale interval is

\[
q\ge q_*:=\max(q_0,2Q-\sigma).
\tag{1}
\]

It ensures the central reverse factor is nonnegative and the outer
comparison interval has T>=2. It does not assert that the comparison
points represent a full physical trajectory.

## 1. Exact numerator

Let `f(t)=t-1/t-log t`, `h(t)=log t-1+1/t`, and `G_t(z)=zt-f(t)`.
The same-lift central and outer data are

\[
E=G_S(u)+G_{T_0}(v)-h(q),
\quad
w=\frac{q^2v+\mathcal D^2u-\mathcal DqE}{P^2},
\quad E_L=\frac{2\mathcal D u-qE}{P}.
\]

The exact truncated line at tau=2 gives

\[
R_2=2w-f(2)+G_{T_B}(u)-h(P/\alpha^2)-E_L,
\quad N_2(q)=P^2R_2(q).
\tag{2}
\]

At w=3/4, this is the genuine Legendre root maximum. For w<3/4,
the maximum on `[2,T]` is also R2, because `f'(tau)>=3/4` there.
Thus this is the correct truncated extension; the convex chord must not
be extrapolated below its interval.

Put `H=G_S(u)+G_T0(v)+1` and `C=G_TB(u)-f(2)+1+2log alpha`.
An exact formula useful for differentiation is

\[
N_2=2q^2v+2\mathcal D^2u-2\mathcal D uP
 +q(P-2\mathcal D)(H-\log q-1/q)
 +P^2(C-\log P)-\alpha^2P.
\tag{3}
\]

## 2. Strict concavity in inverse scale

Write `r_A=alpha/(alpha+beta)` and `s=1/T0`. Since `beta<=alpha*x`,
we have `S>=TB`. Also

\[
2Q-\mathcal D-\sigma=2x(\beta-1)>0,
\quad \mathcal D+\sigma/2<2Q\le P.
\tag{4}
\]

Differentiate (3) twice. Combine the logarithmic terms using
`qP>=2 alpha^2 S T0 TB`, and use the actual norm upper bounds.
The resulting elementary estimate is

\[
N_2''\le -7+8r_A+4s^2+\frac{2\mathcal D-\sigma}{q}<0.
\tag{5}
\]

For clarity, before the final simplification the nonlogarithmic bound is

`4v+2[(u-1)(S+TB)+(v-1)T0+1/S+1/T0+1/TB]-5+(2D-sigma)/q`.

Replace `S` by `TB` only in the negative `(u-1)S` term and in `1/S`;
then use u<=U(r_A), v<=U(s). This gives the first inequality in (5).
The last follows from `r_A,s<=1/2` and `(2D-sigma)/q<2`, the latter
being exactly (4). No norm interval, ellipticity, or root continuation
is required for this concavity.

## 3. Two exact initial derivative signs

Let

\[
A_q=2q+\sigma-2\mathcal D>0,
\]
\[
H_0=(u-1)S+(v-1)T_0+1/S+1/T_0+1,
\quad C_0=(u-1)T_B+1/T_B-1/2,
\]
\[
W(q;u,v)=A_qH_0+2PC_0+4qv-2\mathcal D u-2P
                                      +2\mathcal D-1-\alpha^2.
\]

Exact differentiation of (3) gives

\[
N_2'=W-A_q\log(q/q_0)-2P\log(P/(2Q)).
\tag{6}
\]

Its u and v coefficients are respectively
`A_q S+2P TB-2D>0` and `A_q T0+4q>0`. Therefore replace u,v by the
strict rational upper bounds

\[
V_+(z)=\frac{131z^4+229z^3+163z^2+47z+6}
                         {6(z+1)(3z+1)^3}.
\tag{7}
\]

This follows by replacing the logarithm in V with the first two positive
atanh terms; `V(z)<V_+(z)` for z>1. For z>=1 also use
`log z>=2(z-1)/(z+1)`. At the two faces the resulting strict upper bounds are

\[
B_c=\left[W(q;V_+(x),V_+(y))
                  -\frac{4P(P-2Q)}{P+2Q}\right]_{q=q_0},
\tag{8}
\]
\[
B_o=\left[W(q;V_+(x),V_+(y))
        -\frac{2A_q(q-q_0)}{q+q_0}\right]_{q=2Q-\sigma}.
\tag{9}
\]

Each is used only when its face realizes the maximum in (1), so the
logarithm argument in that bound is at least one. We prove `Bc<=0`
and `Bo<=0` by complete exact polynomial certificates below. The strict
norm substitution then gives `N2'(q*)<0`.

## 4. Complete coefficient certificates

Clear the positive denominators

\[
d_c=6\alpha(\alpha+\beta)ST_0(3x+1)^3(3y+1)^3
                              (q_0+\sigma+2Q),
\]
\[
d_o=6ST_0(3x+1)^3(3y+1)^3(2Q-\sigma+q_0),
\]

and set `p_c=-d_c Bc`, `p_o=-d_o Bo`. They are polynomials, of degree
at most three in beta. Use the order parametrization

\[
\alpha=1+h,\quad x=1+h+j,\quad y=x+\ell,
\quad \beta=x+\frac{hxz}{1+z},
\quad h,j,z,\ell\ge0.
\]

It covers the open AC-order domain; the closed order face follows by
continuity as z tends to infinity. Define the polynomial normalizations
`pc_hat=(1+z)^3 pc`, `po_hat=(1+z)^3 po` after this substitution, and

\[
G=(1+z)[j(j+2)+(h+j+2)\ell-2h(h+1)]
                                  -2(h+1)hxz,
\]
\[
D_t=(1+z)[(1+h)^2+2(1+h)x+1+2x-2x^2]-2jhxz.
\]

These equal `(1+z)(q0+sigma-2Q)` and `(1+z)D`, respectively.

### Central face

Here G>=0. The exact identity is

\[
\widehat p_c=393216\,jz^2G+P_c^+.
\tag{10}
\]

The complete literal table for `Pc+` is
[mixed_global_short_bridge_truncated_scale_q0_positive.csv](../explorations/mixed_global_short_bridge_truncated_scale_q0_positive.csv).
Its 3,242 nonzero coefficients are positive integers.

### Outer zero-factor face

Here -G>=0 and Dt>=0. Put

`(g0,g1,g2,g3,g4)=(-G,Dt,G^2,-G*Dt,Dt^2)`.

The exact identity is

\[
183\widehat p_o=\sum_m c_m h^{m_1}j^{m_2}z^{m_3}\ell^{m_4}g_{i_m}
                                                        +P_o^+.
\tag{11}
\]

The 39 positive integer multipliers are fully listed in
[mixed_global_short_bridge_truncated_scale_t2_multipliers.csv](../explorations/mixed_global_short_bridge_truncated_scale_t2_multipliers.csv).
The complete 2,172 positive integer coefficients of `Po+` are in
[mixed_global_short_bridge_truncated_scale_t2_positive.csv](../explorations/mixed_global_short_bridge_truncated_scale_t2_positive.csv).
Every factor in (10)--(11) is nonnegative on its stated face. Omitted
coefficients are zero. The exact checker reconstructs both identities
from these literal tables and from (8)--(9), using rational arithmetic;
it does not call a numerical optimizer or infer any sign by sampling.

## 5. Precise conclusion and remaining work

Equations (5), (8)--(11) prove

\[
\boxed{N_2'(q)<0\quad\text{for every }q\ge q_*.}
\tag{12}
\]

Therefore `N2(q)<=N2(q*)`. To prove `R2<0` throughout this scalar
domain, it suffices to prove its two VALUE inequalities:

1. `R2<0` on `q=q0`, `T>=2`, including w<3/4;
2. `R2=R(T)<0` on `T=2`, `q>=q0`.

The central convex-chord certificate on `3/4<=w<=f'(T)` does not by
itself prove the first of these when w<3/4. Neither value inequality
is assumed in this note. The result is a rigorous reduction of the
lower-norm face, not a closure of that face or of M2.

The two values are now independently proved in the
[central truncated face](MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_FACE.md) and
[whole upper endpoint](MIXED_GLOBAL_SHORT_BRIDGE_UPPER_ENDPOINT.md).
Their use with this derivative gives the global negative R2 value in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md).
