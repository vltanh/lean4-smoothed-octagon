# A hand envelope for the outer root of a smaller short bridge

Date: 2026-11-07. This is a proved scalar comparison, with a readable
calculus proof below. It does not use an interval cover, a coefficient
table, or a computer-verified sign. It is not yet an exclusion of the
smaller-short case: the competitive upper Casimir and two-turn defect
still have to be coupled to the new envelope.

The actual six-variable interface is
[MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md),
Sections 1, 3 and 4. Its same-covector central equations and actual
outer descending root are the only interfaces used here. The exact
physical two-turn cost remains the one in
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md).

## 1. Data and statement

Use the actual short-bridge ratios and normalization

\[
1\le\alpha<x\le\beta,\qquad
r=\frac1{1+x}<\frac12,\qquad 0<\rho\le r^2,
\]
\[
\sigma=\alpha^2-1,\quad Q=\alpha(\alpha+\beta),\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\]
\[
\lambda=\frac1{1+\rho\sigma},\quad d=\lambda\rho D,
\quad T=\frac1{\lambda\rho Q},\quad
T_B=\frac{\alpha+\beta}{\alpha},\quad
\rho_A=\alpha^2\lambda\rho.
\]

The incoming turn norm u is fixed. Let the opposite actual turn have

\[
t=\frac1{1+y},\qquad t_0=\frac\rho r\le t\le r,
\qquad v\le U(t),\qquad U(t)=1-t+t^2.
\]

The central pairing and transported outer data are

\[
E(t,v)=\frac{u-1}{r}+\frac{v-1}{t}
       +1+r+t-\rho+\log\frac{\rho}{rt},
\]
\[
w=\lambda^2v+d^2u-d\lambda E,
\qquad E_L=2du-\lambda E.
\]

For a root parameter \(2\le\tau\le T\), put

\[
f(s)=s-s^{-1}-\log s,\qquad
h(s)=\log s-1+s^{-1},
\]
\[
R_\tau(t,v)=\tau w-f(\tau)+uT_B-f(T_B)
                 -h(1/\rho_A)-E_L.
\]

**Envelope theorem.** For every such root parameter,

\[
\boxed{R_\tau(t,v)\le R_\tau(t,U(t))
                     \le R_\tau(t_0,U(t_0)).}
\tag{1}
\]

The comparison holds for both signs of D. Both inequalities are strict
when the corresponding variable actually changes. In particular, a
strictly positive actual outer-root maximum implies

\[
\max_{2\le\tau\le T}R^*_\tau>0,
\tag{2}
\]

where the comparison data are now explicit:

\[
v_*=U(\rho/r),\qquad
E_*=(u-1)/r+r+2\rho/r-\rho,
\]
\[
w_*=\lambda^2v_*+d^2u-d\lambda E_*,
\qquad E_{L,*}=2du-\lambda E_*.
\tag{3}
\]

The positivity premise in (2) comes from the actual outer reverse
switch, as recorded in Section 4 of the six-variable reduction. Its
root parameter tau_A satisfies 2<tau_A<T, R(tau_A)=0, and R'(tau_A)<0.
The strict reverse transversality is established in
[NORMAL_SWITCH_RIGIDITY](NORMAL_SWITCH_RIGIDITY.md). Hence R is strictly
positive immediately to the left of tau_A, within [2,T]. This justifies
using a positive maximum before any artificial comparison is made.

Thus the opposite turn and its independent norm can be removed from
this necessary outer-root condition without the earlier two-short-side
polynomial tables. No assertion is made that the comparison point is an
actual trajectory.

## 2. One elementary positive factor

For every \(t\ge t_0\) and \(0\le\tau\le T\), define

\[
B_\tau(t)=1+\tau(\lambda t-d).
\]

It is strictly positive. If \(\lambda t-d\ge0\), this is immediate.
Otherwise its minimum on \([0,T]\) is at T, and

\[
B_T(t)=1+\frac{t/\rho-D}{Q}
       =\frac{Q+t/\rho-D}{Q}.
\]

Since \(t/\rho\ge1/r=1+x\),

\[
Q+t/\rho-D\ge Q+1+x-D
=\beta(2x-\alpha)-x
\ge x(\beta-1)>0.
\tag{4}
\]

Only \(\alpha\le x\), \(\beta\ge x>1\), and positive Q were used.
This proves the sign uniformly, without a case distinction in D.

## 3. Raise the opposite norm, then decrease its reciprocal turn

At fixed t, central stationarity gives \(E_v=1/t\). Therefore

\[
\frac{\partial R_\tau}{\partial v}
=\tau\lambda^2+\frac{\lambda(1-\tau d)}t
=\frac\lambda t B_\tau(t)>0.
\tag{5}
\]

Raising v to its legitimate incident upper bound U(t) proves the first
inequality in (1). This comparison is affine in v, so no intermediate
root feasibility or ellipticity assumption is needed.

Along this upper-norm curve,

\[
E(t,U(t))=(u-1)/r+r+2t-\rho+\log\frac{\rho}{rt}.
\]

Use \(U'(t)=2t-1\) and
\(\frac{d}{dt}E(t,U(t))=2-1/t\). Direct differentiation of the
displayed R formula gives

\[
\frac{d}{dt}R_\tau(t,U(t))
=\tau\lambda^2(2t-1)+\lambda(1-\tau d)(2-1/t)
=\frac{\lambda(2t-1)}t B_\tau(t)<0.
\tag{6}
\]

Here every comparison value has \(0<t\le r<1/2\), and (4) supplies
the other strict sign. Decreasing t to t0 proves the second inequality
in (1). At t0 the logarithm vanishes, giving (3).

The parameter interval [2,T] is unchanged during both comparisons:
all of x, alpha, beta, rho and u are fixed. Thus (1) applies directly at
an actual parameter where R is positive and proves (2). It does not
require continuation of a moving root or differentiation of a maximum.

## 4. A short explicit form of the new necessary condition

Expanding only the elementary f and h terms gives

\[
\boxed{R^*_\tau=(w_*-1)\tau+\tau^{-1}
 +(u-1)T_B+T_B^{-1}+1-\rho_A-E_{L,*}
 +\log(\tau/T).}
\tag{7}
\]

Its derivative in tau is

\[
\partial_\tau R^*_\tau=w_*-1+\tau^{-1}-\tau^{-2},
\qquad
\partial_\tau^2R^*_\tau=\frac{2-\tau}{\tau^3}\le0.
\tag{8}
\]

Consequently the new envelope maximum on [2,T] has three elementary
possibilities: tau=2, tau=T, or the unique interior solution of
\(w_*=1-1/\tau+1/\tau^2\). This is valid even if the comparison w*
has left the original actual norm interval. In particular, an old
convex-chord bound whose proof assumes \(3/4\le w\le U(1/T)\) cannot
be applied to w* without re-establishing those assumptions.

## 5. Exact effect on the Casimir: a limitation and a useful identity

Assume also the actual incident norm bounds
\(3/4\le u\le U(r)\) and \(3/4\le v\le U(t)\). Define

\[
\Gamma(t,v)=\frac{4uv-E(t,v)^2}{16(1-\rho)^2}.
\]

The standard elementary reverse-centre estimate E<=3rho holds throughout
the two comparisons: use the two incident ceilings, rho<=rt, and
\(\log z\le z-1\), or differentiate
\(-1+2r+2t-4\rho+\log[\rho/(rt)]\) in rho and evaluate at rho=rt.
Hence

\[
2ut-E\ge t(2u-3r)>0.
\]

The exact derivatives are

\[
\Gamma_v=\frac{2u-E/t}{8(1-\rho)^2}>0,
\]
\[
\frac{d}{dt}\Gamma(t,U(t))
=\frac{(2t-1)(2u-E/t)}{8(1-\rho)^2}<0.
\tag{9}
\]

Thus the same comparisons **increase** the squared Casimir:
\(\Gamma_*\ge\Gamma_{\rm actual}\). They transport its lower
bound, not its competitive upper bound. Nor does (1) assert any
monotonicity of the physical two-turn spectral defect.

There is nevertheless a compact endpoint identity. Put

\[
z=U(r)-u\ge0,\quad t_0=\rho/r,\quad
Z=\frac{z}{r(1-\rho)}.
\]

Then the comparison Casimir is

\[
\boxed{\Gamma_*=\frac3{16}
 -\frac{Z\,[Z+2(1-2t_0)]}{16}.}
\tag{10}
\]

For a direct check, write
\(E_*=E_0-z/r\), with \(E_0=-1+2r+2t_0-rt_0\).
Expansion of two quadratics gives

\[
4U(r)U(t_0)-E_0^2=3(1-rt_0)^2,
\]
\[
2E_0/r-4U(t_0)=-2(1-2t_0)(1-rt_0)/r.
\]

Substituting these identities in 4uv*-E*^2 proves (10). These are
displayed identities in two variables, rather than an unexplained
coefficient-sign certificate.

## 6. Quantitative loss identities and a conditional corrected cap

The loss in the two comparisons can be tracked exactly. Write

\[
\nu=U(t)-v\ge0,\qquad E_b(s)=E(s,U(s)),\qquad
b_0=1-\rho,
\]

and retain the fixed parameter tau throughout. Equations (5)--(6) give

\[
\begin{aligned}
R^*_\tau-R_\tau(t,v)
={}&\frac{\lambda\nu}{t}B_\tau(t)\\
&+\lambda\int_{t_0}^{t}
       \frac{1-2s}{s}B_\tau(s)\,ds.
\end{aligned}
\tag{11}
\]

Every integrand and prefactor is nonnegative. The analogous exact
Casimir difference is

\[
\begin{aligned}
\Gamma_*-\Gamma(t,v)
={}&\frac{\nu(4u-2E_b(t)/t)+\nu^2/t^2}{16b_0^2}\\
&+\int_{t_0}^{t}
\frac{(1-2s)(2u-E_b(s)/s)}{8b_0^2}\,ds.
\end{aligned}
\tag{12}
\]

For the first term, substitute E=E_b(t)-nu/t and expand one square.
The integral is (9). Thus these formulas do not rely on a computed
optimizer or a presumed endpoint minimizer.

More generally the ratio of Casimir increase to root-residual increase
is the same at the two stages. At fixed t while v is raised, it is

\[
\frac{\Gamma_v}{(R_\tau)_v}
=\frac{2ut-E(t,v)}{8b_0^2\lambda B_\tau(t)}.
\tag{13}
\]

Along the upper-norm curve, at t<1/2 it is

\[
\frac{d\Gamma(t,U(t))/dt}{dR_\tau(t,U(t))/dt}
=\frac{2ut-E_b(t)}{8b_0^2\lambda B_\tau(t)}.
\tag{14}
\]

All denominators are strictly positive by (4). Suppose a positive
constant C is proved to bound (13) on the entire norm-raising segment
and (14) on the entire reciprocal-turn segment. Integrating gives

\[
\Gamma_*-C R^*_\tau
\le\Gamma_{\rm actual}-C R_{\tau,\rm actual}.
\tag{15}
\]

Choosing an actual tau where R_tau>0 therefore transports the
competitive upper cap in the corrected form

\[
\Gamma_*-C R^*_\tau<\Gamma_{\rm actual}<\Gamma_{\rm cap}.
\tag{16}
\]

This is a conditional comparison principle, not an assertion that a
useful uniform C has already been established. Its hypotheses must be
verified on both complete comparison segments, not only at the actual
point. Equations (11)--(14) identify exactly what such a proof must
control, while avoiding the invalid uncorrected transfer of the cap.

## 7. Remaining task

The actual six-variable obstruction still requires a hand inequality
linking its upper Casimir bound and exact two-turn physical cost to
(1)--(10), or an alternative actual-period obstruction. The proof above
is a uniform and sign-complete reduction of one constraint. It is not a
replacement for the completed 107,977-node exclusion on its own.
