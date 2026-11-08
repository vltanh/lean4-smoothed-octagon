# A backward root reduction on the large short-ratio domain

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 4. This note does not yet exclude the remaining scalar domain.

Retain the actual smaller-short hypotheses and the notation of
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
In particular, the two short secants are equal, the geometry is fixed,
and the root parameter tau is that of the actual outer descending root.
This note concerns the possible large-ratio range x>=12/5. It does not
transport the competitive upper Casimir cap to the new scalar endpoint.

## 1. A useful strict bound for the diagonal parameter

Write

\[
Q=\alpha(\alpha+\beta),\qquad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x.
\]

For the exact equal-secant short shape,

\[
\boxed{x\ge12/5\quad\Longrightarrow\quad D<Q.}
\tag{1}
\]

Here is a direct proof. Suppose instead D>=Q. This is equivalent to

\[
\beta(2x-\alpha)\le1+2x.
\]

Since beta>=x and alpha<=x, it follows that x^2<=1+2x. The same
inequality gives

\[
\alpha\ge2x-2-\frac1x\ge\frac{143}{60},\qquad
\beta\le\frac{1+2x}{2x-\alpha}
       \le2+\frac1x\le\frac{29}{12}.
\tag{2}
\]

The first rational function is increasing for x>0. Consequently
beta-alpha<=1/30 and beta+alpha>=143/30.

The positive integral representation of either secant is

\[
\operatorname{Sec}(A,B,P)-\frac34
 =\frac1{4(P-A)}\int_A^P\frac{(s-B)^2}{(s+B)^2}\,ds.
\tag{3}
\]

The second short secant, with s in [alpha,x] contained in
[alpha,beta], therefore satisfies

\[
u-\frac34
\le\frac{(\beta-\alpha)^2}{4(\beta+\alpha)^2}
\le\frac1{4\cdot143^2}.
\tag{4}
\]

The first secant is the average over [1,beta] with B=x. On the
subinterval [1,3/2], using x>=12/5 gives

\[
\frac{x-s}{x+s}\ge\frac{3}{13}.
\]

Together with beta-1<=17/12, its integral gives the contradictory
bound

\[
u-\frac34
\ge\frac1{4(\beta-1)}\cdot\frac12\cdot\frac9{169}
\ge\frac{27}{5746}>\frac1{4\cdot143^2}.
\tag{5}
\]

Thus (1) holds. No cap, scale change, or artificial secant is involved.

For the fixed actual parameter 2<tau<T, where

\[
T=(\lambda\rho Q)^{-1},\qquad d=\lambda\rho D,
\]

(1) implies

\[
\boxed{1-\tau d>0.}
\tag{6}
\]

Indeed, if D<=0 this is immediate; if D>0 then tau*d<D/Q<1.

## 2. Decrease the opposite reciprocal turn

Set t0=rho/r and B(t)=1+tau(lambda*t-d). The existing positive-factor
lemma gives B>0 on the whole fixed interval [t0,r]. Thus the affine
root equation R_tau(t,v(t))=0 defines a unique smooth function there.
For nu(t)=U(t)-v(t), its exact derivatives are

\[
v'=-\frac{(1-\tau d)\nu}{tB},\qquad
w'=-\frac{\lambda^2\nu}{tB},\qquad
\nu'=2t-1+\frac{(1-\tau d)\nu}{tB}.
\tag{7}
\]

Starting at the actual t, decrease t to t0. The condition nu>=0
persists throughout this direction. For example, set
A(t)=(1-tau*d)/(tB) and use an integrating factor for
nu'-A(t)nu=2t-1<0: its integral from an earlier time to the initial
time shows that nu at the earlier time is positive whenever the
initial value is nonnegative.

Now (6)--(7) imply that both v and w are nondecreasing as t is
decreased. Hence the actual floors persist, and the endpoint obeys

\[
\boxed{R_\tau(t_0,v_0)=0,\qquad
\frac34\le v_0\le U(t_0),\qquad w_0\ge\frac34.}
\tag{8}
\]

The root is smooth on the compact interval and its denominator B
never vanishes, so no additional stopping face occurs for (8).
The outer descending ceiling w<U(1/tau) and the upper Casimir cap
are not asserted at this endpoint; they need not survive this
backward scalar comparison.

## 3. Two exact endpoint tests

Let the existing upper envelope at t0 be

\[
V_*=U(t_0),\qquad
E_*=\frac{u-1}{r}+r+\rho(2/r-1),
\]

with associated w_*, E_{L,*}, and R_*=R_tau(t0,V_*). Put

\[
a_0=\lambda\rho(S-D),\qquad S=1+x=1/r,
\qquad B_0=1+\tau a_0>0.
\]

The affine v coefficients at t0 are

\[
(R_\tau)_v=\frac{\lambda B_0}{t_0},\qquad
w_v=\lambda^2\left(1-\frac DS\right),\qquad
\frac{w_v}{(R_\tau)_v}=\frac{a_0}{B_0}.
\]

Solving the root equation exactly gives

\[
v_0=V_*-\frac{t_0R_*}{\lambda B_0},\qquad
w_0=w_*-\frac{a_0R_*}{B_0}.
\tag{9}
\]

Thus (8) has the following three necessary scalar consequences:

\[
\boxed{
R_*\ge0,\qquad
B_0(w_*-3/4)-a_0R_*\ge0,\qquad
R_*\le\frac{\lambda B_0}{t_0}(V_*-3/4).
}
\tag{10}
\]

These formulas retain the actual fixed geometry and actual root
parameter. They do not require D<=S. For D<=S, the middle condition
also gives w_*>=3/4, whereas for D>S the full expression in (10),
not that simpler envelope floor, must be retained.
