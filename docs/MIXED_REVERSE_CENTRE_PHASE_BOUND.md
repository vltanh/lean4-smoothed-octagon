# A reverse-centre phase inequality and a uniform all-short index bound

**Later closure:** [MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md)
and its independent audit exclude every all-short `m>=5` uniformly
by the competitive reverse-angle gap and actual twisted winding. With
the two-centre cost theorem, sufficient M1 is now closed. Historical
remaining-case statements below describe the scope of this earlier
argument; F and M2 still remain open.

Date: 2026-11-07 UTC. Hand inequalities, with supplementary exact
identities. No Lean, Lake, typechecking, or CI.

## Statement and scope

Use the actual finite normal closed-period domain after the reverse-run
classification. At a reverse centre let its active margin be `a`, its
two neighbouring active margins be `p,n`, and put `K=a^2+4`. Write
`nu_-,nu_+` for the two incident switch-vector norms in the common
positive definite form `S`, `e` for their cross pairing, and
`gamma=sqrt(det S)>0`. The exact centre identities are those in
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).

Let `beta_-,beta_+>0` be the two reverse switching coefficients and set

\[
\omega_-=\beta_-ap,\qquad \omega_+=\beta_+an,
\quad M=8a^2/K^2,\quad T=2a^2\gamma/K.
\]

Then the following strict inequality holds uniformly:

\[
\boxed{2T^2>Ke\,[M+2(\omega_-+\omega_+)].}
\tag{1}
\]

There is no cost cap, equal-margin assumption, endpoint-rank assumption,
or lower duration bound in (1). It uses the proved strict centre minimum,
the exact normal stationarity identity, and the actual switching signs.

On the complete geometric all-short family `(--+)^m`, (1) makes the pure angular
block of the fully reduced joint Hessian strictly negative modulo common
rotation. The exact augmented-index transfer consequently gives

\[
\boxed{\operatorname{ind}_-(Q_{\rm closed})\ge(m-8)/3.}
\tag{2}
\]

Thus **every all-short minimizing period with `m>=11` is excluded
uniformly**, for arbitrary unequal factors. The allowed multiplicities
satisfy `m=2 mod 3`. The fixed `m=2` branch was already excluded by
cost, so the sufficient M1 obligation is now confined to `m=5,8`.
This is a consequence of one uniform index inequality, not an increasing
catalogue of period comparisons. This note does not exclude those two
remaining branches, F, or M2, and does not assert a full negative sign
for the dual Hessian.

## 1. Dimensionless centre equations

Put

\[
r=\frac a{a+p},\qquad t=\frac a{a+n},\qquad
\rho=\frac{a^2}{K},\qquad
u=8\nu_-,\quad v=8\nu_+,\quad E=16e.
\tag{3}
\]

The strict centre minimum and positive reverse factor give

\[
0<r,t<\tfrac12,\qquad 0<\rho<rt<\tfrac14.
\tag{4}
\]

Both incident edges touch turns. Their exact secants and reverse
switch inequalities imply

\[
\tfrac34<u<U:=1-r+r^2<1,\qquad
\tfrac34<v<V:=1-t+t^2<1.
\tag{5}
\]

The upper inequalities are strict because every actual closed switch
is transverse. The algebra below would also work with non-strict
upper bounds. The exact normal centre stationarity equation becomes

\[
\boxed{E=1+r+t-\rho+\log\frac\rho{rt}
 -\frac{1-u}{r}-\frac{1-v}{t}.}
\tag{6}
\]

The Gram determinant is

\[
\gamma^2=\frac{K^2}{256}(4uv-E^2).
\tag{7}
\]

For (6), divide the common centre gradient by `a`, substitute
`p/a=1/r-1`, `n/a=1/t-1`, and use
`(a+p)(a+n)/K=rho/(rt)`. In the normal stationarity equation,
`C_i=2[(a+p)nu_-+(a+n)nu_+-2ae]`. These substitutions give
exactly the factors in (6).

## 2. The scalar determinant inequality

The case `E<=0` makes (1) immediate, because its left side is positive
and its right side is nonpositive. Assume `E>0`. Define

\[
\mathcal L=\rho(4uv-E^2)-(1-\rho)^2E.
\tag{8}
\]

Raise `u,v` to their upper bounds `U,V`, keeping `r,t,rho` fixed.
Along this rectangle `E` increases, and its upper-corner value is

\[
B=-1+2r+2t-\rho+\log\frac\rho{rt}.
\tag{9}
\]

Throughout the rectangle,

\[
0<E\le B<3\rho.
\tag{10}
\]

Indeed, put `x=2r`, `y=2t`, `w=4rho`, so `0<w<xy<1`.
Then

\[
B-3\rho=x+y-1-w+\log(w/(xy)).
\]

The right side increases in `w<1`. At `w=xy` it is
`-(1-x)(1-y)<0`, proving (10).

Differentiating (8), with (6) substituted, gives

\[
-\mathcal L_u-\frac{1-r}{r}E
=\frac{(1-\rho)^2-4\rho r v
       +E(2\rho-1+r)}r.
\tag{11}
\]

The coefficient `2rho-1+r` is negative. Using (4), (5), and (10),
the numerator in (11) is strictly greater than

\[
1-5\rho+7\rho^2-\rho r
\ge1-\tfrac{11}2\rho+7\rho^2\ge\tfrac1{16}.
\tag{12}
\]

For the last bound, the quadratic decreases on `[0,1/4]` and equals
`1/16` at `1/4`. The analogous estimate holds for the `v` derivative.
Thus increasing either `u` or `v` strictly decreases `mathcal L`.

Let `L_*(rho)` denote (8) at `u=U,v=V,E=B`. Its exact derivatives
are

\[
L_*'=4UV-B^2-\frac{(1-\rho)^3}{\rho},
\]
\[
L_*''=\frac{1-\rho}{\rho^2}
 \bigl[(1-\rho)(1+2\rho)-2\rho B\bigr]>0.
\tag{13}
\]

The last sign follows from `0<B<3rho`: the bracket is greater than
`1+rho-8rho^2>=3/4`. This applies throughout the interval from the
given `rho` to `rt`, because `B` increases there and stays positive.
At its upper endpoint, direct factorization gives

\[
L_*'(rt)=\frac{(1-rt)^2(4rt-1)}{rt}<0,
\]
\[
L_*(rt)=(1-2r)(1-2t)(1-rt)^2>0.
\tag{14}
\]

Since `L_*'` is increasing and still negative at `rt`, `L_*`
decreases on this interval. In particular `L_*(rho)>0`.

Put `Delta_u=U-u`, `Delta_v=V-v`. Integrate (11)--(12) while
raising first `u` and then `v`. The running value of `E` is no
smaller than its original positive value. Together with (14), this
proves the stronger strict estimate

\[
\boxed{\mathcal L>
E\left[\frac{1-r}{r}\Delta_u+
       \frac{1-t}{t}\Delta_v\right].}
\tag{15}
\]

## 3. Translate the scalar inequality into the phase coefficients

The actual reverse switching coefficients are exactly

\[
\beta_-=\Delta_u/4,\qquad \beta_+=\Delta_v/4.
\]

Consequently

\[
\omega_-+\omega_+
=\frac{a^2}{4}\left[
\frac{1-r}{r}\Delta_u+\frac{1-t}{t}\Delta_v\right].
\tag{16}
\]

Use `K=4/(1-rho)`, (7), and (8). Exact simplification yields

\[
a^2\gamma^2-Ke=\frac{K^3}{256}\mathcal L,
\]
\[
2T^2-Ke\,[M+2(\omega_-+\omega_+)]
=\frac{a^2K}{32}
\left\{\mathcal L-E\left[
\frac{1-r}{r}\Delta_u+\frac{1-t}{t}\Delta_v\right]\right\}.
\tag{17}
\]

Equation (15) proves (1). The weaker consequence
`a^2 gamma^2>Ke` follows too. No division by `e` was used in the
case `e<=0`.

## 4. The entire angular block is negative for all-short periods

Use the exact all-short residual in
[MIXED_GLOBAL_SHORT_RUN_VARIATION, Sections 3--4](MIXED_GLOBAL_SHORT_RUN_VARIATION.md#3-the-all-short-joint-hessian-in-radial-and-angular-variables).
Its margin block is positive definite. Eliminating it leaves the
joint Hessian with the same negative index. On the pure angular
subspace `alpha=0`, the exact residual is

\[
\mathcal R(0,\eta)
=2\sum_j K_je_j(\eta_j-\eta_{j-1})^2
-4\xi^TL_{\rm eff}^{-1}\xi,
\quad \xi_j=T_j(\eta_j-\eta_{j-1}).
\tag{18}
\]

The centre matrix has the positive quadratic form

\[
r^TL_{\rm eff}r
=\sum_j g_j(r_j-r_{j+1})^2+\sum_j M_jr_j^2,
\]

where the bridge conductance is
`g_j=(1/u_j+1/v_j+1/w_j)^{-1}` in terms of the three positive
edge conductances. Thus `g_j` is less than either of its centre-
adjoining conductances. Put

\[
D_j=M_j+2g_{j-1}+2g_j>0.
\]

The elementary estimate `(x-y)^2<=2x^2+2y^2` gives the matrix order

\[
0<L_{\rm eff}\le\operatorname{diag}(D_j),\qquad
L_{\rm eff}^{-1}\ge\operatorname{diag}(D_j^{-1}).
\tag{19}
\]

At centre `j`, (1) and the conductance bounds give

\[
2K_je_j-4T_j^2/D_j<0.
\tag{20}
\]

If `e_j<=0` this is immediate; if it is positive, (1) gives the
strict inequality after replacing its two incident conductances by
the smaller `g_(j-1),g_j`. Substitution in (18)--(19) proves

\[
\mathcal R(0,\eta)
\le\sum_j(2K_je_j-4T_j^2/D_j)
                (\eta_j-\eta_{j-1})^2<0
\]

whenever the periodic scalar sequence `eta` is not constant. The
coefficient sequence is periodic even when the switch vectors are
antiperiodic. The constant sequence is exactly common rotation.
Hence the reduced joint Hessian has at least `m-1` negative directions.

## 5. Full constrained index and exact nearby competitors

For all-short periods, the collapsed node count is `P=m` and the
actual geometric winding is `n=(2m-1)/3`. The exact transfer in
[MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md)
therefore gives

\[
\begin{aligned}
\operatorname{ind}_-(Q_{\rm closed})
&=\operatorname{ind}_-(L_{\rm aug})-2(m-n-1)-3\\
&\ge m-1-2(m-n-1)-3
=\frac{m-8}{3}.
\end{aligned}
\]

The three subtracted constraint pairs are essential. The bound does
not confuse the ordinary Jacobi inertia with the constrained cost
index. When `m>=11`, the right side is positive. The same rank bridge
proves that the state-closed full frame map has rank three. The
implicit-function theorem thus integrates a negative tangent to actual
nearby trajectories satisfying both twisted endpoints. Positivity,
strict star, and the retained geometric realization persist locally.
The cost strictly decreases, contradicting minimality.

The single uniform theorem excludes all allowed `m>=11` together.
It leaves exactly the two admissible multiplicities `m=5,8`, since
`m=2` was separately excluded by its exact cost bound. A stronger
uniform radial/angular estimate could still dispose of these branches
together. No such estimate is asserted here.

## Validation boundary

The supplementary checker
[mixed_reverse_centre_phase_certificate.py](../explorations/mixed_reverse_centre_phase_certificate.py)
verifies the displayed derivative, factorization, and normalization
identities. The strict inequalities, positive matrix order, geometric
lift, full endpoint rank, and inertia transfer are the hand arguments
above and in the cited audited notes. No sampled trajectory, floating-
point sign, increasing-length search, or omitted curvature term is
used as a proof premise.
