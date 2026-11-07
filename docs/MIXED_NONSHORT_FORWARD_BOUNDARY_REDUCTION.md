# A four-variable endpoint reduction for the nonshort forward successor

Date: 2026-11-07. Hand argument with exact algebra checks. The two endpoint
domain exclusions are pending; this note alone does not close M2. No Lean,
Lake, typechecking or CI.

## 1. Follow the same scalar root to the central boundary

Use the actual smaller-nonshort data of
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md):
`a,b,c,d,r,u,v,h`, with `a<c<=b`, `d>a`, `r>=a`, and

\[
K=a^2+4,\quad T=a+c,\quad S=a+b,\quad
Q=d^2+4,\quad W=c+d,\quad Z=d+r,\quad Y=W^2-T^2.
\]

Hold `a,c,d,r` and the exact turn norm `v=Sec(a,c,d)` fixed, and vary
`b` from its actual value to

\[
b_* = K/T-a.
\]

For each intermediate `b`, solve the linear forward-root equation

\[
R_d=C_d-Wv-Zw+16d h_d/Q=0
\]

for the central incident norm `u(b)`, reconstructing `h_d(b),w(b)` with
the same formulas. Sections 4--5 of the continuation note prove that
`R_u<0` throughout this closed interval. They also give, for
`j=u-U(a/S)`,

\[
j_b=A(b)j-\frac{a(b-a)}{(a+b)^3},\qquad w_b<0\quad\text{while }j<0,
\]

where `A(b)` is continuous. The actual strict incident upper bound gives
`j<0` initially. Variation of constants, or the strict inward derivative
at `j=0`, preserves this inequality up to `b_*`. Consequently

\[
u_*<U(a/(a+b_*)),\qquad w_*<w_{\rm actual}.
\tag{1}
\]

This is a comparison of scalar root solutions. It does not preserve a
trajectory, the lower incident norm, the actual Casimir cap, or the
outgoing switching inequalities. Every transferred restriction used
below is proved explicitly.

## 2. Eliminate the diagonal and expose the monotone next norm

Since `a,c,d,r,v,C_d` are fixed along this comparison, stationarity gives
the affine diagonal

\[
H(w)=\frac{Q}{16d}(Wv+Zw-C_d).
\tag{2}
\]

At actual data this is `h_d`, and at the boundary it is `h_{d,*}`.
Define the two scalar functions

\[
\Gamma(w)=\frac{Q^2vw}{64}-H(w)^2,
\qquad
\mathcal T(w)=\frac{Q^2v-16H(w)Z^2+wZ^4}{(r^2+4)^2}.
\tag{3}
\]

The first is the squared scalar Casimir. The second is the transported
norm at the next switch. Put `K_r=r^2+4`. Direct differentiation gives

\[
\boxed{\mathcal T'(w)=-B,\qquad
B=\frac{Z^3(4-dr)}{dK_r^2}>0.}
\tag{4}
\]

The strict sign follows from the unchanged actual strict-star geometry.
Indeed the retained compact inactive-margin bound is stronger:
`4-dr >= (2/15)Z >0`. Thus the boundary comparison increases the
transported next norm, even though it need not preserve the Casimir.

In the forward-next-switch alternative, the actual next norm is at least
`3/4`. Write

\[
t_* = \mathcal T(w_*),\qquad \tau=t_*-\frac34\ge0,
\qquad w_{\rm cap}=w_*+\frac{\tau}{B}.
\tag{5}
\]

Then `T(w_cap)=3/4`, and (1), (4), and the actual successor condition give

\[
\boxed{w_*\le w_{\rm actual}\le w_{\rm cap}.}
\tag{6}
\]

Only this interval comparison is needed. No lower norm or outgoing
derivative has been asserted at the artificial boundary.

## 3. Concavity gives two necessary endpoint alternatives

The squared Casimir is a strictly concave quadratic:

\[
\Gamma''(w)=-2C,\qquad C=\frac{Q^2Z^2}{256d^2}>0.
\]

More explicitly, for `0<=theta<=1` and `L<=U`,

\[
\Gamma((1-\theta)L+\theta U)
=(1-\theta)\Gamma(L)+\theta\Gamma(U)
  +C\theta(1-\theta)(U-L)^2.
\tag{7}
\]

If `L=U`, the endpoint conclusion below is immediate. Otherwise use
`theta=(w_actual-w_*)/(w_cap-w_*)` in (7). The actual competitive cap
`Gamma(w_actual)<23/125` and (6) imply at least one of

\[
\boxed{\Gamma(w_*)\le\frac{23}{125}
\quad\text{or}\quad
\Gamma(w_{\rm cap})\le\frac{23}{125}.}
\tag{8}
\]

This is the precise replacement for an unjustified transfer of the
Casimir cap to `b_*`. Neither endpoint is assumed to be an actual
trajectory. Excluding both enlarged endpoint domains excludes the
actual forward-next-switch alternative.

## 4. A regular residual for the upper endpoint

The interval caller need not divide by `B`. Set

\[
E_* = \Gamma(w_*)-\frac{23}{125},\qquad
G_*'=\frac{Q^2v}{64}-\frac{h_{d,*}QZ}{8d}.
\]

The exact quadratic expansion yields

\[
\boxed{
E_{\rm cap}:=B^2E_*+BG_*'\tau-C\tau^2
=B^2\left(\Gamma(w_{\rm cap})-\frac{23}{125}\right).}
\tag{9}
\]

Thus the two necessary alternatives are `E_*<=0` and `E_cap<=0`, with
the common requirement `tau>=0`. All denominators in their implemented
expressions are positive on the reconstructed comparison charts. Since
`B>0` at actual data, clearing its square changes no sign. The formula
also extends regularly to enlarged scalar boundary points; no assertion
of physical realizability is made there.

## 5. Finite domain and remaining acceptance gates

At `b_*` the central reverse factor is one: `delta_0=0`. The unchanged
actual coordinates retain their global-minimum, scale, compact-state,
turn-secant, turn-derivative, and incoming missing-control conditions.
The boundary upper incident inequality follows from (1). Define

\[
\delta_1=(d-a)/(a+c),\qquad
\delta_2=(c+d)(d+r)/(d^2+4)-1.
\]

Both are positive at actual data. Their maximum and one free relative
weight give two closed maximal charts, with four effective coordinates
`a,c,epsilon,weight`. The existing
[small-parameter hand theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
applies with `l_0=0`, so it excludes their entire common corner
`epsilon<=1/32`. The complementary domains have `epsilon in [1/32,15]`,
`c in [2/15,2]`, and one relative weight in `[0,1]`. The two-chart
boundary theorem, when independently accepted, excludes `a<=1/2` for
both next-switch alternatives; only then may these covers start at
`a=1/2`. The closed overlap at that endpoint is intentional.

The boundary domain must not inherit `b_*<=8`, `u_*>=3/4`, `h_{d,*}>=0`,
the original outgoing derivative/missing-control bounds, or an additional
Casimir bound. Each endpoint alternative uses only its own cap residual
in (8)--(9). The source, contractor, two-root coverage, and final empty
frontier require separate independent review before this reduction is
used to close the forward branch.

The companion
[exact identity checker](../explorations/mixed_nonshort_forward_boundary_certificate.py)
verifies (2)--(4), the endpoint normalization, (7), and (9). It does not
replace the sign arguments, actual period interface, or the two complete
quantified covers. The reduction remains valid across the twisted seam
because it starts from the existing actual same-covector next-switch
alternative; it introduces no competitor or endpoint-rank assumption.
