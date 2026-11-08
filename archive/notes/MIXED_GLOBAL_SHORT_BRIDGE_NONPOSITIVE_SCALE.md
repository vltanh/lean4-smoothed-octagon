# Scale increase on the nonpositive-diagonal root-feasible component

Research checkpoint, 2026-11-07. Hand comparison for the actual
two-short-bridge equations. This is a conditional scale monotonicity
and boundary reduction, not a completed minimum theorem or M2 closure.

## 1. Fixed geometry and the root-feasible region

Use the same normalization as the general short-bridge central and
scale notes. Fix

\[
1\le\alpha<x\le\beta\le\alpha x,\qquad x\le y,
\quad \sigma=\alpha^2-1,\quad Q=\alpha(\alpha+\beta)>2\alpha^2,
\]
\[
\mathcal D=(\alpha+\beta)^2+(1+x)^2-(\beta+x)^2\le0,
\qquad L=-\mathcal D\ge0.
\]

The fixed actual turn norms satisfy `u>3/4`, `v<1`, the two secant
upper bounds, and `u<=U(alpha/(alpha+beta))`, where
`U(r)=1-r+r^2`. The proved central comparison gives
`F0<0` throughout `0<rho<=1/[(1+x)(1+y)]` for these fixed data.
Put

\[
\lambda=(1+\rho\sigma)^{-1},\quad d=-\lambda\rho L,
\quad F=\lambda F_0<0,\quad
T=\frac1{\lambda\rho Q},\quad T_B=1+\beta/\alpha,
\]
\[
w=\lambda^2v-dF=\lambda^2v+\lambda\rho LF,
\qquad E_L=du-F=-\lambda\rho Lu-F.
\tag{1}
\]

In particular `w<lambda^2` when `L>0`; for `L=0` the same strict
inequality follows from `v<1`.

Write

\[
f(t)=t-t^{-1}-\log t,\quad h(t)=\log t-1+t^{-1},
\quad R(t)=wt-f(t)+uT_B-f(T_B)-h(1/\rho_A)-E_L,
\]
\[
\rho_A=\alpha^2\lambda\rho,\qquad
M=\max_{2\le t\le T}R(t).
\]

Consider any scalar point satisfying

\[
T>2,\qquad M>0,\qquad R(T)<0.
\tag{2}
\]

The original actual outer reverse arc has `M>0`, by its positive
duration and incident transversality. The separately proved upper
endpoint theorem supplies `R(T)<0` for the actual strengthened secant
order, throughout the scale interval. The comparison points themselves
need not be trajectories.

Since `w<1`, the maximizer under (2) is unique. It is `tau=2` when
`w<=3/4`, and is the unique `tau=tau_*(w)>2` with `f'(tau)=w` when
`w>3/4`. In the latter case `tau<T`, since otherwise `M=R(T)<0`.
Thus `2<=tau<T` in either case. The maximum is continuously
differentiable across `w=3/4`: its derivative in w is tau on either
side and tends to 2. Formula (5) below therefore also applies there.

## 2. The outer reverse estimate follows from root feasibility

Since `R` decreases on `[tau,T]`, (2) supplies a root
`t_* in (tau,T)`, in particular `2<t_*<T`. Set

\[
r=1/T_B=\alpha/(\alpha+\beta)<\tfrac12,
\quad t=1/t_*<\tfrac12.
\]

The interval constraint gives `rho_A<rt`. Also `u<=U(r)` and
`w<=f'(t_*)=U(t)`: for `w>3/4` this follows from `tau<t_*`, and for
`w<=3/4` it follows from `f'(t_*)>3/4`. Expanding the root
equation gives the actual reverse-centre scalar identity

\[
E_L=1+r+t-\rho_A+\log\frac{\rho_A}{rt}
                  -\frac{1-u}{r}-\frac{1-w}{t}.
\]

Consequently

\[
E_L\le-1+2r+2t-\rho_A+\log\frac{\rho_A}{rt}
<4rt-\rho_A+\log\frac{\rho_A}{rt}\le3\rho_A.
\tag{3}
\]

The strict inequality uses `(1-2r)(1-2t)>0`. For the last one,
`4z-rho_A+log(rho_A/z)` decreases for
`rho_A<=z<=rt<1/4`, and has value `3rho_A` at `z=rho_A`.
The same weak inequality remains valid at a zero-factor limiting root
`t_*=T`. In the open region (2), it also gives `rho_A<1/4` and hence

\[
1-\rho-3\alpha^2\rho>0,\qquad
F> -\lambda\rho(Lu+3\alpha^2).
\tag{4}
\]

Thus (3) is automatic on the root-feasible region (2), rather than a
new condition that must separately be preserved during continuation.

## 3. Strict scale derivative for either sign of the remaining coefficient

The exact envelope derivative from the same-lift scale formulas is

\[
\frac{M_\rho}{\lambda}
=(1+\lambda+\lambda\rho L\tau)
          (\rho^{-1}-1+Lu)
 -(\sigma-\tau L)F-2\tau\sigma w.
\tag{5}
\]

First observe the uniform positive lower bound

\[
\begin{aligned}
\mathcal B&=(1+\lambda)\frac{1-\rho}{\rho}-2\tau\sigma w\\
&\ge(1+\lambda)\frac{1-\rho}{\rho}
                       -\frac{2\sigma\lambda}{\rho Q}
>\frac{1-\rho(1+\lambda)}{\rho}>0.
\end{aligned}
\tag{6}
\]

Here `tau<T=1/(lambda*rho*Q)`, `w<lambda^2`,
`Q>2alpha^2=2(sigma+1)`, `0<lambda<=1`, and the central factor
domain gives `rho<1/4`. If `sigma=0`, the first comparison with the
subtracted term is an equality; the next comparison is still strict.

If `sigma-tau L>=0`, the term `-(sigma-tau L)F` is nonnegative.
All other terms in (5) beyond `B` are nonnegative, so `M_rho>0`.

If `sigma-tau L<0`, insert the lower bound on `F` from (4).
The right side of (5) is then strictly greater than

\[
\mathcal B+(1+\lambda)Lu
 +\lambda\tau L(1-\rho-3\alpha^2\rho)
 +\lambda\sigma\rho(Lu+3\alpha^2)>0.
\tag{7}
\]

This proves `M_rho>0` throughout (2), for every `D<=0`, including the
entire truncated region `w<=3/4`. Neither a Casimir cap nor a
determinant-sector division is used in
this scalar sign. The actual data still use the same normal primary
multiplier before making these scalar comparisons.

## 4. Continuation and the remaining boundaries

Start from actual data with `M>0` and increase rho while retaining
the fixed ratios and norms. Use the separately proved whole upper
endpoint sign `R(T)<0`. On every connected root-feasible segment,
`M` increases, so the path cannot exit through `M=0`. The bound (3)
is reconstructed from a root at every such point; it is not an
independently imposed boundary. The transition through `w=3/4` is
included in the same continuously differentiable maximum.

The bound `w<lambda^2<=1` prevents an upper-norm exit. The only
remaining possible end faces are the central zero factor and `T=2`.
At the latter the maximum equals `R(T)<0`, contradicting its preceding
strict increase from a positive value. Thus a hypothetical actual
positive root maximum must propagate to the central zero-factor face,
with `T>2`. The value of that central maximum is supplied by the separate
[ordinary](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE.md) and
[truncated](MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_FACE.md) face proofs.
The full combination is in [MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md).
This conditional derivative lemma alone does not exclude M2.

The companion [mixed_global_short_bridge_nonpositive_scale_certificate.py](../explorations/mixed_global_short_bridge_nonpositive_scale_certificate.py)
checks only the displayed exact scalar identities; the root existence,
inequality directions and conditional continuation are the hand proof.
No Lean, Lake, typechecking, CI, or numerical sign calculation is used.
