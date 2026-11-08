# Scale monotonicity of the smaller-short upper envelope

Date: 2026-11-07 UTC. Hand reduction, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 15.
This note concerns the necessary outer-root envelope from
[MIXED_SMALLER_SHORT_OUTER_ENVELOPE](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
It gives a strict scale monotonicity after normalizing the root
parameter. It does not transport the competitive Casimir cap or the
physical completion score to the changed scale.

The fixed short shape obeys
\[
1\le\alpha<x\le\beta,\qquad
r=(1+x)^{-1},\quad r_A=\alpha/(\alpha+\beta)<1/2,
\]
and its fixed incoming norm obeys
\[
\frac34\le u\le\min\{U(r),U(r_A)\},\qquad U(s)=1-s+s^2.
\]
The actual equal secants supply these conditions. The algebra below
uses only the displayed order and norm bounds.

## 1. Normalize the root by the outer scale

Put
\[
S=1+x,\quad \varepsilon=1-\alpha^{-2},\quad
\delta=D/\alpha^2,\quad n=S/\alpha^2,\quad
E_0=S(u-1)+S^{-1},
\]
where
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x.
\]
Use the outer scale \(q=\rho_A\), and hold
\[
p=\tau q\qquad(0<p\le r_A)
\]
fixed. Here \(p\) is a normalized root parameter, not an active margin.
The change of scale has
\[
\rho=\frac{q}{\alpha^2-(\alpha^2-1)q},\quad
\lambda=1-\varepsilon q,\quad d=q\delta,\quad
\tau=p/q.
\]
At the upper-envelope endpoint,
\[
v_*=U(\rho/r),\quad E_*=E_0+\rho(2S-1).
\]
Define the three scale-independent coefficients
\[
\begin{aligned}
A_1={}&2\varepsilon+n+\delta E_0,\\
A_2={}&\varepsilon^2+\varepsilon n+n^2+\delta^2u
       +\delta\varepsilon E_0-\delta(2S-1)/\alpha^2,\\
A_3={}&2\delta u+\varepsilon E_0-(2S-1)/\alpha^2.
\end{aligned}
\tag{1}
\]
Substitution in the exact transport gives
\[
w_*=1-qA_1+q^2A_2,\qquad E_{L,*}=-E_0+qA_3.
\tag{2}
\]

The explicit root residual therefore becomes affine in \(q\):
\[
\boxed{
R_{p/q}^*(q)=C(p)+q\,L(p),}
\tag{3}
\]
\[
C(p)=E_0+(u-1)/r_A+r_A+1-pA_1+\log(p/r_A),
\]
\[
L(p)=pA_2+p^{-1}-1-A_3.
\tag{4}
\]
Indeed, insert (2) into
\[
R_\tau^*=(w_*-1)\tau+\tau^{-1}
 +(u-1)/r_A+r_A+1-q-E_{L,*}+\log(\tau q/r_A)
\]
and set \(\tau=p/q\). This proves (3) without differentiating an
implicitly selected maximizing root.

## 2. The affine slope is strictly positive

Introduce two scale-independent quantities
\[
Z=S^2[U(r)-u]\ge0,\qquad
B_0=1+\frac{p(S-D)}{\alpha^2}.
\]
Then direct collection of the coefficients in (1)--(4) gives
\[
\boxed{
\begin{aligned}
pL(p)={}&uB_0^2
 +pB_0\left[\frac{x-1}{S}
            +\frac{Z(1+\alpha^{-2})}{S}\right]\\
 &+\bigl[U(p)-u\bigr]-\frac{Zp^2}{\alpha^2}.
\end{aligned}}
\tag{5}
\]
One can verify the identity by writing
\(D/\alpha^2=S/\alpha^2+(1-B_0)/p\) in (4).
The coefficient of \(pB_0\) then reduces to the displayed bracket,
and the remaining quadratic coefficient is \(1-Z/\alpha^2\).

Every term needed for its sign has a short independent bound.
First, because \(p\le r_A\),
\[
\begin{aligned}
\frac{B_0}{p}
&\ge\frac1{r_A}+\frac{S-D}{\alpha^2}
 =\frac{\beta(2x-\alpha)-x}{\alpha^2}\\
&\ge\frac{x-1}{\alpha}>0.
\end{aligned}
\tag{6}
\]
For the second inequality, use \(\beta\ge x\) and
\[
x(2x-\alpha)-x-\alpha(x-1)
=(x-\alpha)(2x-1)>0.
\]
In particular the actual strict order makes (6) strict, though weak
bounds are sufficient below.

Second, \(u\ge3/4\) implies
\[
0\le Z\le S^2[U(r)-3/4]=\frac{(x-1)^2}{4}.
\tag{7}
\]
Consequently
\[
uB_0^2-\frac{Zp^2}{\alpha^2}
\ge\frac{p^2}{\alpha^2}\bigl[u(x-1)^2-Z\bigr]
\ge\frac{p^2(x-1)^2}{2\alpha^2}>0.
\tag{8}
\]
The bracket multiplying \(pB_0\) in (5) is positive.
Finally \(0<p\le r_A<1/2\), and \(U\) decreases on this interval,
so
\[
U(p)\ge U(r_A)\ge u.
\tag{9}
\]
Equations (5)--(9) prove the quantitative strict bound
\[
\boxed{L(p)>\frac{p(x-1)^2}{2\alpha^2}>0.}
\tag{10}
\]
In particular, the upper-envelope root residual strictly increases
with outer scale \(q\) at fixed shape, incoming norm, and normalized
parameter \(p=\tau q\). Neither sign of \(D\) was assumed.

## 3. Three explicit scale endpoints for the residual alone

The retained central-duration, outer-scale and root-parameter bounds
are
\[
q\le q_c:=\frac{\alpha^2}{S^2+\alpha^2-1},\qquad
q\le\frac17,\qquad q\le\frac p2.
\]
The first is exactly \(\rho\le r^2\), and the last is \(\tau\ge2\).
Define
\[
q_{\max}(p)=\min\{q_c,1/7,p/2\}.
\tag{11}
\]
At fixed actual \(p\), (3) and (10) give
\[
R_{p/q}^*(q)\le
R_{p/q_{\max}}^*(q_{\max}).
\tag{12}
\]
Thus the positive necessary envelope residual can be raised to one
of the explicit faces
\[
\rho=r^2,\qquad \rho_A=1/7,\qquad \tau=2.
\tag{13}
\]
The scale and root bounds may be closed at an artificial endpoint.
Additional short-star conditions may be dropped in this scalar
comparison; no resulting endpoint is claimed to be a physical bridge.

## 4. When the original outgoing norm floor can also be retained

A useful additional statement holds on the explicit shape branch
\[
D\le S.
\tag{14}
\]
At fixed geometry, throughout the original upper-envelope comparison
one has \(t\ge t_0=\rho S\), and hence \(t-\rho D\ge0\).
The exact derivatives of the transported norm are
\[
w_v=\lambda^2\,\frac{t-\rho D}{t}\ge0,
\]
\[
\frac{d}{dt}w(t,U(t))
=\lambda^2\,\frac{(2t-1)(t-\rho D)}t\le0.
\tag{15}
\]
Therefore raising \(v\), then decreasing \(t\), does not decrease \(w\).
An actual \(w>3/4\) supplies
\[
w_*>3/4
\tag{16}
\]
at the original scale. No such preservation is asserted when \(D>S\).

During the further scale comparison, (2) makes \(w_*(q)\) an explicit
quadratic. Let \(\widehat q\) be the largest point of the closed set
\[
\{\,0\le q\le q_{\max}:w_*(q)\ge3/4\,\}.
\]
This set is nonempty, contains the original scale by (16), and is
compact. Hence \(\widehat q\) exists and is at least the original
scale. By (10), the residual at \(\widehat q\), with the same \(p\),
is at least the original positive residual.

Either \(\widehat q=q_{\max}\), giving one of (13) while retaining
the norm floor, or
\[
w_*(\widehat q)=3/4.
\tag{17}
\]
In the latter case, at that fixed scale,
\[
\frac{d}{d\tau}R_\tau^*
=\frac34-U(1/\tau)
=-\frac{(\tau-2)^2}{4\tau^2}\le0.
\]
Thus replacing \(\tau=p/\widehat q\) by \(2\) only increases the
residual, while preserving (17). The resulting explicit boundary has
both
\[
w_*=3/4,\qquad \tau=2.
\tag{18}
\]
The upper-envelope endpoint already has \(t=t_0\) and \(v=U(t_0)\).
This gives a further reduced residual test on the branch (14).

## 5. Scope and relation to the corrected cap

The positive-slope proof uses one displayed quadratic identity (5),
the two norm ceilings, and the short order. It has no sampled sign
premise or coefficient table.

Only the necessary residual and, on (14), its outgoing norm floor
have been transported to the changed scale. In particular, this note
does **not** carry either the original upper Casimir cap, the
geometry-only lower bound from
[MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP](MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP.md),
or the physical completion-cost inequality along the scale change.
Those depend on the physical scale and need their own comparison
before being used at (13) or (18).

The new endpoint residual signs, their coupling to the retained cost
test, and the branch \(D>S\) remain open. This scale reduction does
not itself close the smaller-short case.
