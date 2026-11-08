# Constructing the forward control trajectory

`SmoothedOctagon/ControlTrajectory.lean` constructs a measurable control from the
determinant-normalized boundary of a balanced disk. It proves both integral
equations in the upstream `IsStateTrajectory` definition. The construction is
then specialized to the balanced representation of an actual worst disk in
normal position.

This is source-level Lean development. **Compilation, typechecking, Lake, and
kernel validation have not been run.** Source inspection does not replace those
checks. No additional axiom or proof placeholder is introduced.

## What the theorem starts with

The main geometric theorem `normalized_boundary_isStateTrajectory` takes a
centrally symmetric convex disk, six positive regular boundary parametrizations,
and their common matrix frame. The explicit hypotheses are

\[
\sigma_j(t)=g(t)s_j^*,\qquad
g'(t)=g(t)X(t),\qquad
\det g(t)=1,
\]

with `IsStarState (X t)` at every time and global entrywise Lipschitz regularity
of `X`. The star-state predicate includes trace zero, determinant one, and the
three strict star inequalities. These are the outputs of the constructed clock
in `DeterminantClock.lean`; they are not assumptions that a control trajectory
already exists.

`balanced_determinantClock_isStateTrajectory` supplies the boundary curves as
`σ_j ∘ a`, where `a` is the increasing inverse determinant clock. The helper
`positiveBoundaryParam_of_balanced` obtains the original positive global boundary
parametrizations from the balanced-pair definition. It uses periodicity and
exhaustiveness on one half-open period to prove global exhaustiveness. The
existing `positiveBoundaryParam_reparam` then handles the positive change of
parameter.

`balanced_exists_stateTrajectory` invokes the clock existence theorem itself.
For a balanced circle representation it produces a positive full period `P`,
the clock `a`, and a state trajectory on `[0, P / 6]` with identity initial
frame. Finally, `normalized_worstDisk_exists_stateTrajectory` invokes the
constructed balanced circle representation of an actual worst disk. Its
trajectory and control are therefore obtained from the disk rather than
postulated.

## The explicit control, including exceptional times

Write

\[
\kappa_j(t)=\det\!\left(s_{2j}^*,
 [X(t)+X(t)^{-1}X'(t)]s_{2j}^*\right),\qquad j=0,1,2.
\]

Here `X'` is the entrywise derivative, whose total definition is measurable even
where a classical derivative does not exist. On the Borel set where all three
curvatures are nonnegative and their sum is positive, set

\[
u_j(t)=\frac{\kappa_j(t)}{\kappa_0(t)+\kappa_1(t)+\kappa_2(t)}.
\]

On its complement, set all three coordinates to `1 / 3`. This is the function
`boundaryControl X`, built through `repairedCurvatureControl`.

The repair is essential for the exact upstream definition: the control must
belong to the simplex at **every** time of the interval, whereas the state
equation holds almost everywhere. The code proves the following properties
separately.

- `boundaryControl_mem` proves simplex membership at every time.
- `measurable_stateCurvature` and `measurable_boundaryControl` prove Borel
  measurability. For determinant-one matrices, inversion is the adjugate; the
  proof reduces to measurable scalar arithmetic and measurable derivatives.
- `boundaryControl_eq_raw_ae` proves agreement with the raw normalized
  curvatures almost everywhere in the open interval. Upstream Lemma 3.3.1
  supplies a strictly positive curvature coordinate, so the sum in the raw
  denominator is strictly positive there.
- `boundaryControl_denominator_neg` proves
  `traceForm (controlMatrix (boundaryControl X t)) (X t) < 0` at every star
  state, including repaired times. The inverse used in `controlP` therefore
  never uses a zero denominator along this construction.

## Why curvature survives the new parameter

An arbitrary almost-everywhere statement cannot simply be pulled back through
an unspecified change of variable. The proof instead establishes the curvature
inequality directly for the normalized curves.

At a point where `X` is differentiable, the frame equation gives

\[
\sigma_j'=gXs_j^*,\qquad
\sigma_j''=g(X^2+X')s_j^*.
\]

Since both determinants equal one,

\[
\det(\sigma_j',\sigma_j'')
=\det\!\left(s_j^*,[X+X^{-1}X']s_j^*\right).
\]

This algebraic identity is `normalized_curvature_identity`. The scalar
curvature is nonnegative at any point where the second derivative exists:
the tangent line supports the convex disk, so

\[
f(t)=\det(\gamma'(t_0),\gamma(t)-\gamma(t_0))\geq0,
\qquad f(t_0)=f'(t_0)=0.
\]

Its second derivative cannot be negative. The source proves this as
`positiveBoundary_curvature_nonneg`, using the same support-line argument as
upstream Lemma 2.4.6 but with pointwise second differentiability as the explicit
input. Entrywise Lipschitz regularity of `X` supplies that differentiability
almost everywhere. This proves `stateCurvature_nonneg_of_boundary` without
assuming a global bound on the second derivative of the reparametrized curves.

## From the differential equation to the required integrals

The local regularity required by upstream Theorem 3.4.2 is also derived. Since
`X` is continuous and `g' = gX`, each entry of `g` is continuously differentiable.
On a compact interval the entries of `g` are bounded and Lipschitz. Multiplying
them by the bounded Lipschitz entries of `X` proves that `g'` is Lipschitz on
that interval (`frame_velocity_lipschitz`).

Theorem 3.4.2 is first applied to the raw curvature control, exactly as its
hypotheses require. Almost-everywhere equality with the repaired control then
gives

\[
X'=P(u,X)X-XP(u,X)
\]

almost everywhere. The original frame equation gives the other differential
equation everywhere.

For `X`, the entrywise Lipschitz property implies absolute continuity on every
closed subinterval. The absolutely-continuous fundamental theorem of calculus
then gives

\[
X(t)=X(0)+\int_0^t [P(u(s),X(s)),X(s)]\,ds.
\]

`integralCurve_of_lipschitz_ae` proves this entry by entry, including interval
integrability. The proof removes the endpoint null set explicitly when passing
from the open-interval derivative statement to the integration interval. It
does **not** assume that the derivative-exceptional set is countable. The
classical matrix FTC supplies the integral equation for `g`.

For assembling a new balanced-pair witness, the module also exports
`frame_velocity_lipschitz_periodic`. It differentiates frame periodicity to
obtain velocity periodicity and promotes the compact-interval Lipschitz bound
to a global bound. This is used by the cyclic-clock construction to obtain
global Lipschitz derivatives of the six new boundary curves.

## The precise remaining comparison

Full-period periodicity alone does not identify the frame at `P / 6` with the
rotation `R`. The cyclic successor construction supplies the stronger identity
`σ_j(t + P / 6) = σ_(j+1)(t)` after the determinant clock. That identity is needed
both for the admissible terminal conditions and for the upstream area formula.
The forward theorem here deliberately records the actual state-trajectory
conclusion before this separate cyclic input is supplied.

Even an admissible realization with exact area cost does not by itself prove
that a geometric minimizer minimizes cost over **all** upstream admissible
controls. The missing reverse comparison has the form: for every admissible
control, construct a balanced circle disk whose area is at most that control's
cost. This is proved separately in `ReverseComparison.lean`; it is not an
additional premise silently assumed by this forward construction.

### Low-cost winding route used by the reverse comparison

The following explains the winding issue addressed by `LowCostWinding.lean`,
`CyclicExtension.lean`, and `ReverseGeometry.lean`. Their full assembly is in
`ReverseComparison.lean` and [REVERSE_COMPARISON.md](REVERSE_COMPARISON.md).

An admissible control can make extra turns. For example, the constant state
`X = J` with uniform control and the rotating frame satisfies the same terminal
conditions at `T = π/3 + 2πn`. Its cost is `π + 6πn`. Thus a proof that every
admissible trajectory directly traces a simple boundary with exactly its cost
would be false.

For cost at least `π`, the unit disk is already a competitor with no larger
area. Only the case of cost less than `π` needs reconstruction. Write

\[
X=\begin{pmatrix}a&b\\c&-a\end{pmatrix},\qquad
v=(g_{00},-g_{01}).
\]

The star inequalities and determinant one give `c > 0`, `b < 0`, and
`-a² - bc = 1`. The reflected row satisfies

\[
v'=(av_0-cv_1,-bv_0-av_1).
\]

Its angular numerator is

\[
q=-bv_0^2-2av_0v_1+cv_1^2.
\]

Both `q` and `(c-b)‖v‖²-q` are positive definite quadratic forms, each with
determinant one. The lifted angle therefore has strictly positive derivative
bounded above by `c-b = -traceForm J X`. Its increase over the interval is at
most two thirds of the cost, hence less than `2π/3` in the low-cost case.
The terminal frame `R` forces that increase to be `π/3 + 2πn`, so it must be
exactly `π/3`.

In particular the first entry `g₀₀` stays positive during this arc. The first
column then cannot make an additional turn. Fixed positive determinants of
adjacent contact columns keep their relative angles in `(0, π)`, giving the
same minimal angular increment to every contact. The intended continuation is
to extend the frame by `g(t + nT) = g(t) R^n`, use terminal conjugacy of `X` to
match first derivatives, prove one full winding, and apply the existing
star-curve convexity criterion.

The full construction obtains regularity from arbitrary integral admissibility,
checks the global extension and every seam, derives one-turn simplicity, and
constructs the balanced circle witness with exact area. The high-cost assembly
uses the concrete octagon, whose area is strictly below `π`. The forward
construction here does not assume any of those reverse conclusions.
