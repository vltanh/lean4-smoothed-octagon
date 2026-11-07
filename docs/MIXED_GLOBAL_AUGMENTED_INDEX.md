# The full endpoint rank and augmented-index bridge

Date: 2026-11-07 UTC. Hand proof. No Lean, Lake, typechecking, or CI.

## Statement and exact remaining sign

Consider an actual finite positive normal minimizing period after the
reverse-run classification, with `N>=6`. Let `m` be its number of
double reverse runs, allowing `m=0` for a pure-forward period, and put

\[
P=N-2m,\qquad n=(N-m-1)/3.
\]

The geometric winding and ordinary scalar Jacobi inertia are proved in
[MIXED_GLOBAL_PROJECTIVE_WINDING](MIXED_GLOBAL_PROJECTIVE_WINDING.md).
This note proves the following uniform bridges.

1. The full frame map on the state-closed active-margin family has
   rank three. A negative constrained cost direction therefore gives
   an actual nearby closed competitor.
2. The common collapsed Jacobi matrix gives an exact joint Lagrangian
   in `N` margin variables and two `P`-component kernel vectors.
   Its second derivative includes the full frame-constraint curvature.
3. If `Q_closed` is the actual constrained cost Hessian and `L_aug`
   is this joint Hessian, then

   \[
   \boxed{\operatorname{ind}_-(Q_{\rm closed})
   =\operatorname{ind}_-(L_{\rm aug})-2(P-n-1)-3.}
   \tag{1}
   \]

4. The principal block of `L_aug` on all turn-margin variables is
   positive definite. They can be eliminated without changing its
   negative index.

Consequently the one sufficient **unproved** bound

\[
\operatorname{ind}_-(L_{\rm aug})\ge2P-1
\tag{2}
\]

would imply at least `2(n-1)` negative closed directions. Equation
(1) is a proved inertia identity; (2) is the substantive remaining
index problem. No F/M1/M2 comparison is closed by this note.

For M2 beyond the retained through-five class, `n>=2`. Indeed if
`n=1`, then `P+m=4`. A mixed period has `P>=m>=1`. The possibilities
are `(m,P)=(1,3)`, with `N=5`, or `(2,2)`, in which both forward
runs have length one and the period belongs to the already excluded
two-centre M1 branch. Thus (2) would exclude the entire remaining M2
domain uniformly, rather than one word length at a time.

## 1. Rank three follows from the existing full local rank theorems

The cyclic active margins give an open smooth family resolving the
state endpoint and allowing the initial state to vary. They recover
every nearby state-closed positive trajectory with the same sign
pattern: read its constant active margins and use

\[
q_i=(a_{i-1}+a_i)^{\epsilon_{i-1}}
    (a_i+a_{i+1})^{\epsilon_i}
    (a_i^2+4)^{-(\epsilon_{i-1}+\epsilon_i)/2}.
\tag{3}
\]

The third switching-state margin is
`(4-a_(i-1)a_i)/(a_(i-1)+a_i)`, so there is no extra state degree
of freedom omitted by these coordinates.

Every remaining period with `N>=6` contains a six-complete-arc window
of one of the following types, after cyclic relabeling:

| Whole-period assignment | Available window | Existing full rank input |
|---|---|---|
| Pure forward F | `012012` | [LOCAL_FORWARD_RANK](LOCAL_FORWARD_RANK.md) |
| All forward runs short M1 | `021210` | [LOCAL_MIXED_SIX_RANK](LOCAL_MIXED_SIX_RANK.md) |
| Some forward run longer M2 | `010201` | [LOCAL_SIX_VARIATION, Section 2](LOCAL_SIX_VARIATION.md#2-universal-regularity-of-the-l4-endpoint-map) |

Each input gives rank five for the six positive logarithmic durations,
with initial state fixed, into the **actual** terminal frame and state.
It follows that the subspace of its duration variations with zero
terminal-state derivative maps onto all three frame directions.

Extend these variations by zero outside the selected window. The
state at its far end has zero derivative, so the remaining state
trajectory and the full twisted state endpoint have zero derivative.
The frame variation is transported by multiplication through the
remaining fixed controls; this is an invertible linear transport on
the three-dimensional frame tangent space. All three full-period
frame derivatives are therefore still realized.

There is also an exact local realization of this argument. Rank five
allows five of the six duration coordinates to serve as endpoint
coordinates. Holding the two local terminal-state coordinates fixed
while varying the three frame coordinates produces a smooth local
family. The unchanged tail then preserves the full state closure
exactly. Its active margins are coordinates of the state-closed family
(3). Thus the remaining full frame map in those coordinates has rank
three, without inferring rank from normality or from the absence of
abnormal maximizing lifts.

The selected six arcs fit within one actual period. Cyclic rebasing
and the actual twist treat a window crossing the original seam. All
factors and star margins remain positive under sufficiently small
variations. The rank-three implicit-function theorem can therefore
integrate a negative constrained direction. The retained geometric
realization argument applies to these nearby closed trajectories;
no rank claim supplies the missing negative sign by itself.

## 2. The common collapsed scalar operator

Write

\[
s_i=a_i+a_{i+1},\quad K_i=a_i^2+4,\quad
\delta_i=(\epsilon_{i-1}+\epsilon_i)/2.
\]

First form the symmetric quadratic expression on switch sequences
with the actual central boundary sign:

\[
\mathcal H_a(z)
=-\sum_i\epsilon_i s_i^2 z_i^2
 +2\sum_i\delta_iK_i z_{i-1}z_i.
\tag{4}
\]

At every turn impose the fixed linear relation `z_i=-z_(i-1)`.
The word, not the active margins, specifies these relations. Collapse
them and apply the same sign gauge as in
MIXED_GLOBAL_PROJECTIVE_WINDING. This gives a `P`-dimensional real
symmetric Jacobi matrix `H(a)`, on boundary sign `(-1)^n`, with
positive off-diagonal coefficients `K_i` at its remaining edges.

Let `Y` be the `P`-by-two matrix of collapsed, gauged actual switch
vectors. Then

\[
H(a)Y=0,\qquad \operatorname{rank}Y=2.
\tag{5}
\]

Here is a direct way to check (5) without assigning a recurrence from
the control labels alone. After the run theorem, a class of identified
switches contains zero, one, or two turns. With no turn, the three
vector terms are the usual forward Jacobi relation. For an isolated
`(+,-)` turn at arc `i`, the constrained row before gauging is

\[
K_{i-1}y_{i-2}+(s_i^2-s_{i-1}^2)y_{i-1}
 +K_{i+1}y_{i+1}=0.
\]

In the prefix frame at that arc its three required vectors are

\[
K_{i-1}y_{i-2}=-s_{i-1}(e_1+e_2),\quad
y_{i-1}=-e_2/s_{i-1},\quad
K_{i+1}y_{i+1}=s_{i-1}e_1+(s_i^2/s_{i-1})e_2.
\]

Substitution cancels both components. The opposite isolated turn is
the reversed calculation under the actual reflection/time-reversal
symmetry. A class with two turns is exactly the three-factor
`A_- A_+ A_-` calculation in
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
These are all the possible identified classes; no growing collection
of words is involved.

The same construction on a nearby state-closed margin family gives
the actual two-dimensional transfer recurrence before imposing its
central endpoint. Thus `dim ker H(a)=2` is locally equivalent to the
full central frame constraint. At the actual period the geometric
winding gives

\[
n_+(H)=n-1,\quad n_0(H)=2,\quad n_-(H)=P-n-1.
\tag{6}
\]

The positive definite form `S=-J_0U` is supplied by the actual
negative-elliptic primary costate. Absorb it into the kernel basis by
putting `Z=Y S^(1/2)`. Then `HZ=0` and `rank Z=2`. This change of
basis does not change `H` or its inertia.

## 3. The exact stationary joint Lagrangian

The signed state-closed action is

\[
J(a)=C/\sqrt{12}=\frac18\sum_i\epsilon_i G(a_i,a_{i+1}),
\]

with the function `G` in MIXED_GLOBAL_COSTATE_ELLIPTIC. Hold the
actual matrix `S` fixed when differentiating, or equivalently use
the absorbed basis `Z`, and define

\[
\mathscr L(a,Z)=J(a)+\operatorname{tr}(Z^T H(a)Z).
\tag{7}
\]

The actual normal boundary identity gives

\[
J_{a_i}=-\operatorname{tr}(Z^T H_{a_i}Z).
\tag{8}
\]

For verification before absorbing `S`, differentiation of (4) gives

\[
\operatorname{tr}(SY^T H_{a_i}Y)
=-2\epsilon_{i-1}s_{i-1}d_{i-1}
 -2\epsilon_i s_i d_i+4\delta_i a_i e_i.
\]

At equal incident signs, the Gram stationarity identity is exactly
the negative of this expression. At a turn, `d_(i-1)=d_i`, and the
turn secant formula gives the same identity. These are identities of
the given physical normal covector after the actual boundary-term
cancellation; a new multiplier has not been chosen for (7).

Equations (5) and (8) say that `(a,Z)` is a stationary point of
the unconstrained joint function (7). Denote the joint Hessian by
`L_aug`. For a margin variation `v` and a kernel-vector variation
`W`, its quadratic form is

\[
\boxed{
L_{\rm aug}(v,W)=Q_0(v)
 +4\operatorname{tr}(Z^T H_v W)
 +2\operatorname{tr}(W^T H W),
}
\tag{9}
\]

where

\[
Q_0(v)=J_{vv}+\operatorname{tr}(Z^T H_{vv}Z).
\]

## 4. The margin block and strict positivity on turns

Define the strictly positive switching coefficients

\[
\beta_i=\epsilon_i(2d_i-j_i)>0,
\qquad
j_i=\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{4s_i^2}.
\]

Strictness is the actual closed-period transversality result in
[NORMAL_SWITCH_RIGIDITY](NORMAL_SWITCH_RIGIDITY.md). It is not an
assumption about every local PMP window.

The full margin block is

\[
\boxed{
Q_0(v)=\sum_i\beta_i a_i a_{i+1}
 \left(\frac{v_i}{a_i}-\frac{v_{i+1}}{a_{i+1}}\right)^2
 -8\sum_i\frac{\delta_i v_i^2}{K_i^2}.
}
\tag{10}
\]

For a hand check, `G_ab/8=j_i`, so the off-diagonal entry of
`Q_0` is `epsilon_i(j_i-2d_i)=-beta_i`. Under common scaling,
the quadratic coefficients in (4) satisfy
`sum a_i H_(a_i a_j)=H_(a_j)`. On the other hand the exact Euler
identity for the signed action gives

\[
(J''a)_i-J_{a_i}=-8\delta_i a_i/K_i^2.
\]

Together with (8), these determine the diagonal entries and prove
(10), including its factor eight.

On the subspace supported only at turn indices, the second sum in
(10) vanishes. Every connected component of turn indices touches a
same-sign index. A vector with zero weighted-square sum would have
constant `v_i/a_i` along each edge and zero at those adjacent
same-sign indices, hence would vanish. The turn principal block is
therefore positive definite. It may be eliminated from (9) by a
Schur complement without changing the negative index of `L_aug`.

For all-short M1, (10) is positive definite on **all** margin
variables: every nonzero potential term has `delta_i=-1`, and
the constant weighted-square mode is eliminated by at least one
centre. This stronger observation does not prove that the resulting
dual kernel-vector block is negative semidefinite.

## 5. The full tangent constraint and its rank

Let `H^dagger` be the inverse of `H` on the orthogonal complement
of its two-dimensional kernel, extended by zero on that kernel.
The linearized closed-frame constraint is exactly

\[
\boxed{Z^T H_vZ=0.}
\tag{11}
\]

It has rank three. One can verify the link to the actual endpoint
derivative by the discrete Green identity. At a cut, take independent
kernel rows `z_-1,z_0`, let `B` be the two-by-two matrix with these
rows, let `c_0>0` be the off-diagonal coefficient across the cut,
and let `T` be the two-dimensional recurrence monodromy. At the
period `T=epsilon I`, with `epsilon=(-1)^n`. With the initial
recurrence basis held fixed, summing the linearized recurrence gives

\[
Z^T H_v Z
=-\epsilon c_0 B^T
\begin{pmatrix}0&1\\-1&0\end{pmatrix}T_v B.
\tag{12}
\]

The boundary term is the difference of the two discrete Wronskians;
the initial term vanishes when that recurrence basis is held fixed.
The monodromy has determinant one, so `T_v` is traceless at a
central endpoint. Multiplication by the displayed skew matrix takes
traceless matrices isomorphically to symmetric matrices. Conjugation
by the invertible `B` and the nonzero scalar in (12) preserve rank.
The recurrence monodromy is conjugate to the actual frame product up
to the fixed central sign introduced by the gauge. At a central
endpoint the derivative of the conjugating basis cancels.
Section 1 therefore proves the rank-three assertion in (11).

For an actual closed variation choose the derivative of its kernel
basis orthogonal to the original kernel. Differentiating `HZ=0`
then gives `W=-H^dagger H_vZ`. Substitution in (9) gives the exact
constrained quadratic form

\[
\boxed{
Q_{\rm closed}(v)=Q_0(v)
 -2\operatorname{tr}(Z^T H_v H^\dagger H_v Z),
\quad Z^T H_vZ=0.
}
\tag{13}
\]

A different kernel-basis derivative adds only a kernel vector, whose
contribution vanishes by (11). Formula (13) thus includes the actual
endpoint curvature and is independent of that gauge choice.

## 6. Inertia transfer and the three constraint pairs

Split `W` into its kernel component and orthogonal range component.
The range block of (9) is two copies of `2H` on its nonzero
eigenspaces. By (6), it contributes
`2(P-n-1)` negative directions and `2(n-1)` positive directions.
Eliminating it gives (13) in the margin variables, together with the
coupling to the four-dimensional kernel component of `W`.

That coupling has rank three by (11). Its one unused direction is
the common infinitesimal rotation of the two columns of `Z`.
After an invertible linear change of coordinates, its remaining
three directions form one six-dimensional constraint block

\[
\begin{pmatrix}A&I_3\\I_3&0\end{pmatrix},
\]

contributing three positive and three negative directions,
independently of `A`. The uncoupled margin space is precisely the
kernel of (11), where the quadratic form is (13). Sylvester inertia
therefore gives (1), and also

\[
\begin{aligned}
\operatorname{ind}_+(L_{\rm aug})
 &=2(n-1)+3+\operatorname{ind}_+(Q_{\rm closed}),\\
\operatorname{null}(L_{\rm aug})
 &=1+\operatorname{null}(Q_{\rm closed}).
\end{aligned}
\tag{14}
\]

The extra three negative constraint directions are essential. Omitting
them would turn an ordinary Jacobi count into an incorrect cost index.

## Uniform remaining problem

The exact remaining sufficient sign is (2), or any other estimate
that makes the right-hand side of (1) positive on every remaining
competitive M2 period. The local all-six-margin minimum and a local
one-dimensional Hessian are insufficient substitutes for this global
condition. Nor may the indefinite inverse `H^dagger` in (13) be
discarded.

All calculations above are hand identities on the fixed sign family,
using the already audited actual normal, geometric, endpoint-rank,
and Jacobi inputs. No numerical sample or period-length catalogue
enters the bridge. Independent review of this note remains separate
from external peer review and Lean kernel validation.
