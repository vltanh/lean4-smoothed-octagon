# A uniform local switch count on compact regular minimizing lifts

Date: 2026-11-07. Hand proof; no Lean compilation, Lake, typechecking, or CI.

## Result and precise scope

This note proves a locally uniform switch bound near **every nonsingular
free-time Pontryagin phase**, provided the trajectories under consideration
satisfy the following additional optimality property:

> **(E4)** On an interval where one fixed control coordinate vanishes almost
> everywhere, the control agrees almost everywhere with at most four positive
> constant vertex pieces.

Actual global Reinhardt minimizers have (E4), by
[EDGE_SWITCH_BOUND.md](EDGE_SWITCH_BOUND.md), Section 7. It does not hold for
arbitrary full-system Pontryagin extremals. The distinction is necessary:
abnormal full-system lifts can accompany arbitrary measurable controls on
one edge.

Consequently, a family satisfying (E4), having uniformly bounded elapsed
time, and whose lifted phases lie in a compact set disjoint from the full
singular locus has **one common finite bound on the number of positive
vertex pieces**. Applying
[GLOBAL_MINIMIZER_COMPACTNESS.md](GLOBAL_MINIMIZER_COMPACTNESS.md) proves
that such an integer exists for all complete global minimizers.

This is an existential uniform bound, not a stated numerical integer. The
compactness note does not give a numerical distance from the singular locus.
The estimates below explain what additional data would make the bound
effective. Neither `N <= 5` nor the octagon cost comparison follows here.

The main point is uniformity under changes of the initial phase and under
arbitrary measurable controls. A Taylor expansion at a zero of a switching
function on one fixed trajectory would not supply that uniformity. Instead,
we remove the homogeneous reduced-adjoint equation, place its solution in
one fixed plane, and use finitely many scalar projections with a strictly
signed first or second derivative.

## 1. The reduced equations and the singular set

Use the original matrix conventions, the trace pairing
`<Y,Z> = tr(YZ)`, and a constant multiplier `lambda <= 0`. Set

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
A=\Lambda_1-\frac32\lambda J,\qquad W=\Lambda_R.
\]

The state belongs to the positive elliptic orbit `X = Phi(x,y)` in the
strict-star domain. Thus `X^2 = -I`, `<X,X> = -2`, and all three vertex
denominators `<Z_i,X>` are negative. Put

\[
P=P_u(X)=\frac{Z_u}{\langle Z_u,X\rangle},\qquad
b=-[A,X],
\]

\[
\mathcal L_{X,P}(Y)
 =[P,Y]-\langle Y,P\rangle[P,X].
\tag{1}
\]

The equations in Hales--Vajjha, Section 6.7, are

\[
\begin{aligned}
X'&=[P,X],\\
A'&=[A,X]+\frac32\lambda[J,X],\\
W'&=\mathcal L_{X,P}W+b,\qquad \lambda'=0.
\end{aligned}
\tag{2}
\]

They hold almost everywhere and in integral form. In addition,

\[
\langle W,X\rangle=0,\qquad
\max_i\{\langle A,X\rangle-\langle W,P_i(X)\rangle\}=0.
\tag{3}
\]

The maximizing control is supported on the maximizing vertex indices.
The maximum in (3) is continuous in the phase, so its almost-everywhere
vanishing implies its vanishing at every time. Reduction from the actual
five-dimensional cotangent space is invertible, as checked in
[GLOBAL_PERIODIC_PMP.md](GLOBAL_PERIODIC_PMP.md), Section 1. In particular,
nontriviality means that `(lambda, Lambda_1, W)` cannot all vanish.

In these coordinates the full singular locus is

\[
\mathcal S=\{X=J,\ A=0,\ W=0\}.
\tag{4}
\]

The ambient definition may include the zero multiplier; no admissible
nontrivial lifted phase is the zero multiplier. At a phase with `A=W=0`,
nontriviality itself forces `lambda != 0`.

The three vertex Hamiltonians have a common control-independent term.
For comparisons it is enough to use the linear functions

\[
h_i(X,W)=-\langle W,P_i(X)\rangle.
\tag{5}
\]

If `W` is a nonzero member of `X^perp`, these three values are not all
equal. Here is the exact algebra. Equality would imply
`<W-cX,Z_i>=0` for all three vertex matrices and a common scalar `c`.
The three measurements separate traceless matrices, so `W=cX`.
Perpendicularity and `<X,X>=-2` then give `c=0`. This is also the hand
vertex test in [SINGULAR_LOCUS.md](SINGULAR_LOCUS.md). It implies that at
least one vertex is strictly excluded from the maximizing set at every
nonzero direction in `X^perp`.

## 2. Uniform coefficient bounds, including measurable controls

All norms in this section are Frobenius norms on matrices and their
induced operator norms. On a sufficiently small closed phase neighborhood
inside strict star, choose finite constants such that

\[
\|X\|\le K_X,\quad \|P_u(X)\|\le K_P\quad(u\in U_T),\quad
\|A\|\le K_A,\quad \|W\|\le K_W,\quad |\lambda|\le K_\lambda.
\tag{6}
\]

The common `K_P` exists because the control simplex is compact and all its
denominators are separated from zero on the chosen state neighborhood.
The elementary estimates

\[
\|[Y,Z]\|\le2\|Y\|\|Z\|,\qquad
|\langle Y,Z\rangle|\le\|Y\|\|Z\|
\]

give

\[
\|\mathcal L_{X,P}\|\le L_0:=2K_P+2K_P^2K_X,\qquad
\|b\|\le2K_AK_X.
\tag{7}
\]

They also bound the phase velocities uniformly:

\[
\begin{aligned}
\|X'\|&\le2K_PK_X,\\
\|A'\|&\le2K_AK_X+3K_\lambda\|J\|K_X,\\
\|W'\|&\le L_0K_W+2K_AK_X.
\end{aligned}
\tag{8}
\]

Thus there is a common finite phase-speed bound `V_0`. If an inner phase
ball has distance `r/2` from the boundary of a concentric outer ball,
every trajectory starting in the inner ball stays in the outer ball
for `|t-t_0| <= r/(2V_0)`, on either part of that time interval where
the trajectory is defined. One may replace `V_0` by `max(1,V_0)`.

Although `P` need only be measurable, `A` is continuously differentiable
by (2), and `X` is Lipschitz. Hence `b` is Lipschitz and

\[
b'=-[[A,X],X]-\frac32\lambda[[J,X],X]-[A,[P,X]]
\quad\text{almost everywhere}.
\tag{9}
\]

Define the control-independent vector

\[
C(X,\lambda)=-\frac32\lambda[[J,X],X].
\tag{10}
\]

Equations (7)--(9) give the explicit bound

\[
\|b'-\mathcal L_{X,P}b-C(X,\lambda)\|
 \le D_0\|A\|,
\qquad
D_0=4K_X^2+4K_PK_X+2L_0K_X.
\tag{11}
\]

No derivative of `u`, `P`, or `mathcal L` appears. This is why the argument
below remains uniform for measurable controls and for short arcs of
arbitrary duration.

## 3. Transport to a fixed two-dimensional plane

Fix a reference phase `p_*=(X_*,A_*,W_*,lambda_*)` satisfying the
algebraic conditions (3) and nontriviality. Let

\[
E=X_*^\perp\subset\mathfrak{sl}_2(\mathbb R).
\]

For nearby initial states `X_0`, choose a smooth ambient linear
isomorphism `S_{X_0}` sending `E` onto `X_0^perp` and tending to the
identity as `X_0` tends to `X_*`. One explicit choice is

\[
\Pi_X(Y)=Y+\frac12\langle Y,X\rangle X,\qquad
S_X(Y)=\Pi_X\Pi_{X_*}(Y)-\frac12\langle Y,X_*\rangle X.
\tag{12}
\]

At `X=X_*` this is the identity. Also `S_X(X_*)=X` and
`S_X(E)=Pi_X(E)`, so it is invertible with the required property in a
sufficiently small neighborhood. Using an ambient isomorphism makes all
norm comparisons below ordinary comparisons in the same three-dimensional
space.

Along an arbitrary trajectory starting at `t_0`, let `U` solve

\[
U'=\mathcal L_{X(t),P(t)}U,\qquad U(t_0)=I.
\tag{13}
\]

This is an absolutely continuous, invertible fundamental matrix for a
bounded measurable linear equation. On `|t-t_0| <= h`,

\[
\|U^{\pm1}\|\le e^{L_0h},\qquad
\|U^{\pm1}-I\|\le e^{L_0h}-1.
\tag{14}
\]

If `Y'=mathcal L Y`, the trace identity gives

\[
\frac d{dt}\langle Y,X\rangle
 =\langle[P,Y],X\rangle+\langle Y,[P,X]\rangle
  -\langle Y,P\rangle\langle[P,X],X\rangle=0
\tag{15}
\]

almost everywhere. Thus `U(t)` maps `X(t_0)^perp` onto `X(t)^perp`.
With `S=S_{X(t_0)}`, the curve

\[
\eta(t)=S^{-1}U(t)^{-1}W(t)
\tag{16}
\]

lies in the one fixed plane `E` and satisfies

\[
\eta'=S^{-1}U^{-1}b,\qquad
\eta''=S^{-1}U^{-1}(b'-\mathcal L b)
\quad\text{almost everywhere}.
\tag{17}
\]

In fact `eta` is continuously differentiable and `eta'` is absolutely
continuous: `b` and `U^{-1}` are continuous and absolutely continuous.
This regularity is sufficient for the scalar monotonicity and convexity
arguments below.

For explicit uniform estimates, suppose both `||S-I||` and
`||S^{-1}-I||` are at most `epsilon`. Put

\[
Q=(1+\epsilon)e^{L_0h},\qquad d=Q-1.
\tag{18}
\]

Then

\[
\|S^{-1}U^{-1}\|\le Q,\quad
\|S^{-1}U^{-1}-I\|\le d,\quad
\|US-I\|\le d.
\tag{19}
\]

The number `epsilon` can be made arbitrarily small by shrinking the
initial-state neighborhood, independently of the measurable control.
The number `d` then tends to zero as that neighborhood and `h` shrink.

## 4. A finite set of separating lines

The following elementary planar observation is the control-selection
part of the proof. Fix `X_*`, the plane `E`, and a nonzero vector `v_*`
in `E`. The vector will be specified separately in the two zero cases.

There are finitely many distinct lines

\[
\ker\ell_1,\ldots,\ker\ell_m\subset E,
\qquad \|\ell_j\|=1,
\tag{20}
\]

with these properties:

1. `ell_j(v_*) != 0` for every line.
2. Each closed angular sector cut out by the lines has a vertex index
   that is strictly excluded from the maximizing set for every nonzero
   vector in that sector, at state `X_*`.
3. The same sector exclusions hold uniformly when `X` is sufficiently
   close to `X_*` and the actual reduced covector is `W=T eta`, where
   the ambient linear map `T` is sufficiently close to the identity and
   maps `E` into `X^perp`.

Here is a construction that includes the boundary rays. On the unit
circle of `E`, the open sets

\[
\{\xi:h_i(X_*,\xi)>h_j(X_*,\xi)\},\qquad i\ne j,
\tag{21}
\]

cover the circle by the vertex test in Section 1. Choose a Lebesgue
number for this finite open cover. Take equally spaced lines with mesh
fine enough that every **closed** sector's unit-circle arc has diameter
smaller than that number. Rotate the whole finite line arrangement by
an angle avoiding the finitely many choices for which one line is
parallel to `v_*`. Each closed sector is contained in one set (21).
Its comparison `h_i-h_j` has a positive minimum on its compact
unit-circle arc. Taking the minimum over the finitely many sectors
gives a positive common margin `beta`.

The functions in (5) depend continuously on `X` and linearly on `W`.
Uniform continuity on the finite collection of compact arcs therefore
preserves a margin at least `beta/2` when `X` and `T` are sufficiently
close to their reference values. Positive homogeneity extends the
comparison to every nonzero vector in each sector. The support rule
then forces the selected excluded coordinate to vanish almost
everywhere whenever the direction stays in that sector. Different
sectors may exclude different vertices.

Define the positive derivative margin

\[
\alpha=\min_{1\le j\le m}|\ell_j(v_*)|>0.
\tag{22}
\]

If `||eta'-v_*|| < alpha/2`, every `ell_j(eta)` is strictly monotone
and has at most one zero. If `||eta''-v_*|| < alpha/2` almost everywhere,
every such function has a strictly signed second derivative and at most
two zeros. For the second assertion, its first derivative is strictly
monotone by integration. Three distinct zeros of the function would
give two distinct zeros of its first derivative by Rolle's theorem,
a contradiction. This proof applies to `C^1` functions with absolutely
continuous first derivative.

After deleting all these zeros from a time interval, each remaining
connected component stays in a single open sector. Indeed the
continuous vector cannot cross a separating line without a zero of
one of the selected scalar functions. A zero of the whole vector is
also in that finite deleted set. There are at most `m+1` components in
the first-derivative case and at most `2m+1` in the second-derivative
case. On the closure of each nondegenerate component one fixed control
coordinate is zero almost everywhere; finite endpoints do not affect
that statement. Property (E4) therefore supplies at most four pieces
per component.

## 5. The locally uniform theorem

**Theorem.** Let `p_*` be a nontrivial free-time Pontryagin phase in
strict star and outside `mathcal S`. There exist an open phase
neighborhood `V_*`, a time `h_*>0`, and an integer `B_*` such that the
following statement holds. Every trajectory satisfying (2)--(3), the
maximum principle, and (E4), with phase in `V_*` at time `t_0`, has at
most `B_*` positive vertex pieces on any interval containing `t_0`
whose points satisfy `|t-t_0| <= h_*` and on which that trajectory is
defined. All three choices depend on the reference phase, not on the
particular trajectory or its measurable control.

### Case I: `W_* != 0`

One vertex is strictly excluded at the reference phase by Section 1.
Its strict comparison survives in a phase neighborhood. Use the
uniform speed estimate (8) and an inner neighborhood to choose `h_*`
so that every relevant short trajectory stays there. Its control lies
on the same proper edge almost everywhere. Property (E4) gives
`B_*=4`.

### Case II: `W_*=0`, `A_* != 0`

At the reference phase (3) gives `<A_*,X_*>=0`. The centralizer of
`X_*` in the traceless matrices is `R X_*`. Consequently

\[
b_*=-[A_*,X_*]\ne0.
\tag{23}
\]

Otherwise `A_*` would be a multiple of `X_*`, and the displayed
perpendicularity would force it to vanish. The vector `b_*` belongs
to `E`.

Apply Section 4 with `v_*=b_*`. Choose a small outer phase ball of
radius `r` around `p_*`. On that ball,

\[
\|b-b_*\|
 \le2K_X\|A-A_*\|+2\|A_*\|\|X-X_*\|
 \le2(K_X+\|A_*\|)r.
\]

Equations (17)--(19) imply

\[
\|\eta'-b_*\|
 \le2Q(K_X+\|A_*\|)r+d\|b_*\|.
\tag{24}
\]

Shrink `r` and then `h_*` so that the right side is less than
`alpha/2`, and so that `||X-X_*||` and `||US-I||` meet the sector
comparison tolerances of Section 4. These simultaneous requirements
are possible because `epsilon` tends to zero with `r` and `d` tends
to zero with `r,h_*`. Choose `V_*` inside the concentric ball of radius
`r/2` and also require `h_* <= r/(2 max(1,V_0))`. This last condition
justifies the outer-ball assumptions for every trajectory in the
statement.

Every guard projection is strictly monotone. The count in Section 4
therefore gives the common bound

\[
B_*=4(m+1).
\tag{25}
\]

The nearby trajectories need not have `W(t_0)=0`, and their zeros need
not occur at the same time. Estimate (24), rather than an expansion
assuming a zero at `t_0`, handles that issue.

### Case III: `W_*=A_*=0`, `X_* != J`

Nontriviality forces `lambda_* != 0`. Also

\[
C_*=-\frac32\lambda_*[[J,X_*],X_*]\ne0.
\tag{26}
\]

To see this, if the double commutator vanished, `[J,X_*]` would
centralize `X_*`. It is perpendicular to `X_*`, so it would be zero.
Then `X_*` would be a multiple of `J`. The determinant-one positive
elliptic orbit contains only `J` among these multiples, contrary to
the case hypothesis. The vector `C_*` belongs to `E`.

Apply Section 4 with `v_*=C_*`. On a radius-`r` outer ball, `||A||<=r`.
The elementary double-commutator estimate gives

\[
\begin{aligned}
\|C(X,\lambda)-C_*\|
\le 6\|J\|\bigl(&K_X^2|\lambda-\lambda_*|\\
&+|\lambda_*|(K_X+\|X_*\|)\|X-X_*\|\bigr)
\le K_Cr,
\end{aligned}
\tag{27}
\]

where `K_C=6||J||(K_X^2+|lambda_*|(K_X+||X_*||))`.
Combining (11), (17), and (19) yields

\[
\|\eta''-C_*\|
 \le Q(K_C+D_0)r+d\|C_*\|
 \quad\text{almost everywhere}.
\tag{28}
\]

As in Case II, shrink `r`, the inner neighborhood `V_*`, and `h_*`
so that the right side is less than `alpha/2`, the sector margins
survive, and (8) keeps all trajectories in the outer ball. Each guard
projection has a strictly signed second derivative. The count is now

\[
B_*=4(2m+1).
\tag{29}
\]

Again neither `A` nor `W` must vanish on the nearby trajectory. The
control-independent leading term in (28) dominates all its measurable
control-dependent terms uniformly. The three cases exhaust every
nontrivial phase outside (4), proving the theorem.

## 6. Compact regular families have a uniform finite bound

**Corollary.** Let a class of complete trajectories satisfy the maximum
principle and (E4). Suppose all their phase values lie in one compact
set `K_lift` of nontrivial strict-star phases disjoint from `mathcal S`,
and all their elapsed times satisfy `0<T<=T_max`. There is an integer
`N_*` such that every member agrees almost everywhere with a vertex
control having at most `N_*` positive pieces on its whole period.

**Proof.** Apply the local theorem at every point of `K_lift` and take
a finite subcover by the inner neighborhoods `V_1,...,V_s`. Let

\[
h=\min_j h_j>0,\qquad B=\max_j B_j<\infty.
\]

Partition each period into intervals of length at most `h`. At each
interval's left endpoint the phase is in one selected `V_j`. The local
theorem bounds that whole interval by `B` positive vertex pieces.
Concatenation and merging equal neighboring controls cannot increase
the resulting count. Thus one may take

\[
\boxed{\quad N_*=B\left\lceil\frac{T_{\max}}h\right\rceil.\quad}
\tag{30}
\]

Finite partition endpoints do not matter to the almost-everywhere
control or its integral trajectory. If the chosen cut divides a
vertex arc across the twisted period seam, subsequent cyclic reduction
can only decrease the count. This proves the corollary. `square`

There is no uniform lower bound on individual arc durations in this
argument. Arbitrarily short arcs and coalescing switches are allowed;
the finitely many guard zeros, followed by (E4) on each edge interval,
bound their number.

## 7. Application to actual global minimizers and the remaining gates

[GLOBAL_MINIMIZER_COMPACTNESS.md](GLOBAL_MINIMIZER_COMPACTNESS.md) proves
the needed hypotheses for all actual global minimizers after projective
normalization of their genuine cotangent lifts. It includes abnormal
lifts, proves closedness under weak-star convergence of the equivalent
affine controls, and uses the actual minimizing cost to identify the
limit as a global minimizer. Evaluation of that compact family over
the normalized period gives a compact phase set. Theorem 16.3.1 and
Lemma 8.3.4 exclude the full singular locus from every one of its lifts.
The smooth cotangent-coordinate change used here preserves compactness
and disjointness. The time bound is `T_max=A_oct/3`, and (E4) holds by
the exact edge replacement theorem.

Therefore (30) proves the mathematical statement

\[
\boxed{\text{There exists one finite integer bounding the number of
positive vertex pieces of every complete global minimizer.}}
\tag{31}
\]

The dependence on the published finite bang-bang theorem is not circular.
That theorem is used separately on each limiting global minimizer to
exclude a singular point from every lift. Compactness then gives one
regular compact set, and Sections 2--6 supply a new **uniform** local
count on that set. Pathwise finiteness alone was never used to assert
an upper bound over a family.

An effective finite comparison still needs additional work:

1. Give a certified numerical singular clearance for normalized global
   minimizers, or an explicit regular compact phase domain containing
   them. The compactness proof only asserts existence of the clearance.
2. **Now completed conditionally:**
   [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
   supplies a fixed angular mesh, explicit comparison and derivative
   margins, and an explicit O(1/epsilon) count for a supplied normalized
   clearance. All coefficient constants are fixed. A numerical clearance
   remains necessary before this becomes a particular integer.
3. Prove a uniform global cost comparison on the resulting domain, with
   the actual free initial state and twisted closure. The current
   through-five comparison cannot be invoked unless a separate argument
   reduces the resulting bound to five or otherwise completes that
   global comparison.

Statement (31) supplies a genuine uniform reduction theorem, but not an
explicit list of cases. It does not authorize resuming an increasing
sequence of word-length comparisons. The failed universal local L3
replacement remains false on its original domain; none of the reasoning
here changes that domain or assumes it away.

## Sources and validation boundary

- Hales--Vajjha, [Section 6.7](https://arxiv.org/html/2405.04331v1#Ch6.S7):
  the state and reduced-adjoint equations.
- [Section 8.2](https://arxiv.org/html/2405.04331v1#Ch8.S2): the control
  support test and the full singular locus.
- [Section 8.1](https://arxiv.org/html/2405.04331v1#Ch8.S1), together with
  [EDGE_SWITCH_BOUND.md](EDGE_SWITCH_BOUND.md): the measurable edge
  interval bound (E4) for actual global minimizers.
- [GLOBAL_MINIMIZER_COMPACTNESS.md](GLOBAL_MINIMIZER_COMPACTNESS.md):
  compactness, normalization, and uniform qualitative singular clearance.
- [GLOBAL_PERIODIC_PMP.md](GLOBAL_PERIODIC_PMP.md): actual cotangent
  reduction and the free-initial-state twisted transversality conditions.

The transport identities, uniform estimates, finite angular construction,
and uniform local-count argument are proved above. They use neither sampled
trajectories nor a computer algebra sign certificate. No Lean source,
typechecking, build, or CI execution is a premise or a validation claim.

Independent mathematical review on 2026-11-07 checked the full note,
including the ambient plane isomorphism, both measurable-control derivative
estimates, closed-sector margins, scalar zero counts, (E4) on component
closures, and the finite-cover passage. Three separate reviews found no
substantive gap. This records hand review, not kernel validation or an
explicit numerical value of the final bound.
