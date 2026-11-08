# Exact bridge order and a uniform variation problem for short forward runs

Date: 2026-11-07 UTC. Hand structural identities and an explicitly
unresolved uniform sign. No Lean, Lake, typechecking, or CI.

## Scope

Use the complete all-short mixed domain `(--+)^m` and notation of
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
Its centre margins are `a_j`, its bridge turn margins are `b_j,c_j`,
and `K_j=a_j^2+4`. Every switch is transverse by
[NORMAL_SWITCH_RIGIDITY](NORMAL_SWITCH_RIGIDITY.md). The same actual
negative elliptic normal multiplier is used throughout.

This note proves an order relation between neighbouring centre and
turn margins, gives an exact endpoint-preserving global scale family,
and spells out the all-short dual Hessian after eliminating all margin
variables. None of the displayed residual signs is assumed. The
unresolved sign is the remaining uniform comparison obligation, not a
completed M1 exclusion.

The later [MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md)
proves the pure-angular sign in the residual below and a uniform
constrained-index lower bound `(m-8)/3`. It excludes all `m>=11`;
`m=5,8` and the full radial/angular residual sign remain open. The
two-centre branch was already excluded by cost.

## 1. A common secant and the order of the bridge

For one bridge write `(a,b,c,d)=(a_j,b_j,c_j,a_(j+1))` and
`nu=z_j^TSz_j`. Positivity of the three factors and the strict centre
minima give

\[
a,d<\min(b,c).
\]

Let

\[
g(r)=1-\frac r{(1+r)^2},\qquad
\mathcal D(a,b,c)=\frac1{8(c-a)}\int_a^c g(t/b)\,dt.
\tag{1}
\]

The two turn stationarity identities are exactly

\[
\mathcal D(a,b,c)=\nu=\mathcal D(d,c,b).
\tag{2}
\]

The strict weak-switch inequalities, now strict by transversality,
also give

\[
g(c/b)<8\nu<g(a/b),\qquad 8\nu<g(d/c).
\tag{3}
\]

**Bridge order lemma.** The signs agree:

\[
\boxed{\operatorname{sign}(d-a)=\operatorname{sign}(c-b).}
\tag{4}
\]

First compare equal outer centres. If `c>b>a`, parameterize the two
averages by

\[
t=a+s(c-a),\qquad t'=a+s(b-a),\qquad 0\le s\le1.
\]

Then `r=t/b>r'=t'/c` and `rr'<=1`, with strict product inequality
for `s<1`. The function `r/(1+r)^2` is unchanged by `r -> 1/r`
and increases strictly on `(0,1)`. Consequently

\[
\frac r{(1+r)^2}>\frac{r'}{(1+r')^2}\qquad(s<1),
\]

which proves

\[
\mathcal D(a,b,c)<\mathcal D(a,c,b)\qquad(c>b>a).
\tag{5}
\]

Now suppose `d>=a`. On `[a,d]`, both `t/c` and `d/c` are
less than one. Since `g` decreases there, (3) gives
`g(t/c)>=g(d/c)>8nu`. Adding this interval to the average
`mathcal D(d,c,b)=nu` yields

\[
\mathcal D(a,c,b)\ge\nu,
\]

with strict inequality if `d>a`. If `c<b`, the reversed version
of (5) says `mathcal D(a,b,c)>mathcal D(a,c,b)`, contradicting
(2). If `c=b`, equality of the two averages at `a` forces `d=a`.
Thus `d>a` implies `c>b`. Apply the same argument to the reversed
bridge `(d,c,b,a)`, which has the same identities (2)--(3), to obtain
the opposite strict implication and the equality case. This proves (4).

At a globally smallest centre `a`, (4) makes the far turn margin at
each adjacent bridge no smaller than its near turn margin. For example,
on an outgoing bridge `c>=b`. The function `g` increases for arguments
at least one, and the left inequality in (3) gives
`g(t/b)<=g(c/b)<8nu` on `[b,c]`. Removing that interval from the
average therefore gives

\[
\nu\le\mathcal D(a,b,b),
\tag{6}
\]

strictly if `c>b`. The incoming bridge has the analogous bound after
reversal. If its near margin is `p` and the outgoing near margin is `n`,
then

\[
d_{j-1}\le D(p/a),\qquad d_j\le D(n/a),
\]
\[
D(x)=\frac18\left[
1+\frac{x}{2(x+1)}
-\frac{x}{x-1}\log\frac{2x}{x+1}\right],\qquad x>1.
\tag{7}
\]

Equality on a bridge requires equality of its two centre margins and
of its two turn margins. This is a genuine minimum-sensitive
restriction; it does not assert a sign for a centre cross pairing.

## 2. An exact global scale family preserves the full endpoint

Write the collapsed diagonal as

\[
D_j^{\rm Jac}=(a_j+b_j)^2+(c_j+a_{j+1})^2-(b_j+c_j)^2.
\]

For `lambda` in a neighbourhood of one, set

\[
K_j(\lambda)=\lambda K_j,\qquad
a_j(\lambda)=\sqrt{\lambda K_j-4},\qquad c_j(\lambda)=c_j,
\]
\[
b_j(\lambda)=
\frac{\lambda D_j^{\rm Jac}-a_j(\lambda)^2
-a_{j+1}(\lambda)^2-2c_j a_{j+1}(\lambda)}
{2(a_j(\lambda)-c_j)}.
\tag{8}
\]

The denominator is nonzero at the original period because `a_j<c_j`.
At `lambda=1`, (8) recovers the original `b_j`. Direct substitution
gives `D_j^Jac(lambda)=lambda D_j^Jac`. Hence the entire collapsed
Jacobi matrix is multiplied by `lambda`, and its second-order transfer
recurrence is unchanged. The full monodromy remains the same central
matrix, not merely a matrix with the same trace. The state-closed
active-margin reconstruction therefore gives both exact twisted
endpoints. Every positivity and strict-star inequality persists on a
sufficiently small common neighbourhood of one. This is an explicit
local family; no endpoint-rank or implicit-function assertion is used.

Let `J=C/sqrt(12)`. Eliminate the derivatives of the two turn margins
using (2) and `D_j^Jac{}'=D_j^Jac`. The exact derivative along (8) is

\[
\boxed{J'(1)=\sum_j\mathcal F(a_j,b_j,c_j,a_{j+1}),}
\tag{9}
\]

where, with `K_a=a^2+4`, `K_d=d^2+4`,

\[
\begin{aligned}
\mathcal F(a,b,c,d)={}&
\nu\left[2bc-ab-cd+8+\frac{4b}a+\frac{4c}d\right]\\
&-\frac{K_a}{16}\left[2f(1+b/a)+h(1+4/a^2)\right]\\
&-\frac{K_d}{16}\left[2f(1+c/d)+h(1+4/d^2)\right],
\end{aligned}
\tag{10}
\]

and `f(t)=t-t^-1-log t`, `h(t)=log t-1+t^-1`.
For verification, the same expression before simplification is

\[
\nu\left[(a+b)K_a/a+(c+d)K_d/d-D_j^{\rm Jac}\right]
-\frac{K_aG_a(a,b)}{16a}-\frac{K_dG_a(d,c)}{16d}.
\]

The logarithms involving the centre factors collect over the whole
period as `-sum_j (K_j/8) log q_(a_j)`. The other terms still need
a valid aggregate inequality. A local summand need not have a definite
sign if one forgets its neighbouring centre-factor constraints.

Normal stationary PMP makes (9) zero. Thus a uniform strict negative
bound for its sum, using (2)--(7), all factor inequalities and the
actual period constraints, would exclude the whole all-short class.
No such aggregate sign is asserted here.

## 3. The all-short joint Hessian in radial and angular variables

Use the exact augmented Hessian of
[MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md), with
`S>0` and `gamma=sqrt(det S)>0`. Define the compatible quarter-turn
operator `I_S=gamma S^-1 J_0`; thus `S I_S=gamma J_0` and
`I_S^2=-I`. Any switch-vector variation has the form

\[
w_j=\alpha_jz_j+\eta_j I_Sz_j.
\tag{11}
\]

The coefficient sequences `alpha,eta` are periodic, even when the
vector sequence itself is antiperiodic. Write the active-margin
variations as ratios

\[
r_j=\delta a_j/a_j,\qquad s_j=\delta b_j/b_j,
\qquad t_j=\delta c_j/c_j.
\]

Let `beta` be the strict switching coefficient
`epsilon(2d_edge-j_edge)>0`, and define three positive conductances
on each bridge:

\[
u_j=\beta_{ab}a_jb_j,\quad
v_j=\beta_{bc}b_jc_j,\quad
w_j^*=\beta_{cd}c_ja_{j+1},\qquad
M_j=8a_j^2/K_j^2.
\]

The complete fixed-vector margin block is

\[
Q_0=\sum_j\left[
u_j(r_j-s_j)^2+v_j(s_j-t_j)^2
+w_j^*(t_j-r_{j+1})^2+M_jr_j^2\right].
\tag{12}
\]

It is positive definite. This permits elimination of every margin
variable, not only the turns, but does not determine the sign of the
remaining Schur complement.

Put `nu_j=z_j^TSz_j` and `e_j=z_(j-1)^TSz_j`. The pure vector
block is exactly

\[
\begin{aligned}
Q_Y={}&2\sum_jK_je_j
\left[(\alpha_j-\alpha_{j-1})^2
+(\eta_j-\eta_{j-1})^2\right]\\
&-4\gamma\sum_j
(\alpha_{j-1}\eta_j-\eta_{j-1}\alpha_j).
\end{aligned}
\tag{13}
\]

Here `z_(j-1)^T S I_S z_j=gamma/K_j`, by the negative Wronskian.
Define

\[
L_j=2\nu_j b_j(c_j-a_j),\qquad
R_j=2\nu_j c_j(b_j-a_{j+1}),
\]
\[
A_j^-=2a_j[(c_{j-1}+a_j)\nu_{j-1}-a_je_j],\quad
A_j^+=2a_j[(a_j+b_j)\nu_j-a_je_j],\quad
T_j=2a_j^2\gamma/K_j.
\]

The remaining cross block is

\[
4\sum_j r_j\left[A_j^-\alpha_{j-1}+A_j^+\alpha_j
-T_j(\eta_j-\eta_{j-1})\right]
-4\sum_j\alpha_j(L_js_j+R_jt_j).
\tag{14}
\]

Equations (12)--(14) follow by differentiating the actual Jacobi
diagonal and the centre off-diagonal entries. They retain the
curvature contribution; (13) is not discarded.

## 4. Explicit elimination leaves one exact dual residual

For each bridge abbreviate `u=u_j`, `v=v_j`, `w=w_j^*` and set

\[
\Delta_j=uv+uw+vw>0,\qquad g_j=uvw/\Delta_j,
\]
\[
F_j^L=\frac{u[(v+w)L_j+vR_j]}{\Delta_j},\qquad
F_j^R=\frac{w[vL_j+(u+v)R_j]}{\Delta_j},
\]
\[
B_j=\frac{(v+w)L_j^2+2vL_jR_j+(u+v)R_j^2}{\Delta_j}>0.
\tag{15}
\]

The two-turn block is
`[[u+v,-v],[-v,v+w]]`. Completing its square in (12)--(14)
replaces the bridge by

\[
g_j(r_j-r_{j+1})^2
-4\alpha_j(F_j^Lr_j+F_j^Rr_{j+1})-4B_j\alpha_j^2.
\]

Define the positive definite periodic operator `L_eff` by

\[
r^TL_{\rm eff}r
=\sum_j g_j(r_j-r_{j+1})^2+\sum_jM_jr_j^2,
\]

and the linear vector

\[
\Xi_j=(A_j^--F_{j-1}^R)\alpha_{j-1}
 +(A_j^+-F_j^L)\alpha_j
-T_j(\eta_j-\eta_{j-1}).
\]

Eliminating the centre ratios as well gives the exact residual

\[
\boxed{\mathcal R(\alpha,\eta)
=Q_Y-4\sum_jB_j\alpha_j^2
-4\Xi^T L_{\rm eff}^{-1}\Xi.}
\tag{16}
\]

All the inverses in this calculation are positive definite and have
displayed coefficients. The common rotation `alpha=0`, `eta=constant`
is in the kernel. The sign of (16) on its complement remains unproved.
In particular, `e_j` can have either sign in (13); positivity of
`Q_0`, `B_j` and `L_eff` alone does not establish nonpositivity of
the full residual.

If (16) were negative definite modulo that rotation, its negative
index would be `2m-1`. The exact augmented-index transfer, including
the three frame-constraint saddle pairs, would then give at least
`2(n-1)` negative closed-period cost directions. For the all-short
branch `n=(2m-1)/3`, this would exclude every `m>=5`. Equation
(16) isolates that uniform matrix-sign obligation; it is not a proof
of its conclusion.
