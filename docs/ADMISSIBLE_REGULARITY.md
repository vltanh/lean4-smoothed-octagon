# Regularity derived from arbitrary admissible controls

`SmoothedOctagon/AdmissibleRegularity.lean` derives the regularity needed for
reverse geometric reconstruction from the upstream **integral-form** state
trajectory definition. It does not restrict the control to be continuous,
piecewise constant, a vertex control, or a member of a polygon family.

The only main hypothesis is `IsStateTrajectory T u g X`. In particular, `u` is
merely measurable and simplex-valued on `[0,T]`, and `g` and `X` initially come
with entrywise integral equations. The new results prove continuity,
Lipschitz regularity of `X`, continuously differentiable entries of `g`, the
state differential equation almost everywhere, and nonnegative contact
curvature almost everywhere.

**Compilation, typechecking, Lake, and kernel validation have not been run.**
This is source-level Lean development. No additional axiom or proof
placeholder is introduced.

## Exact exported interface

All of the following theorems take an actual `IsStateTrajectory` witness.

| Declaration | Conclusion on the trajectory interval |
| --- | --- |
| `stateTrajectory_continuous` | Both `g` and `X` are continuous on `[0,T]`. |
| `stateTrajectory_state_lipschitz` | Every entry of `X` is Lipschitz on `[0,T]`. |
| `stateTrajectory_frame_hasDerivWithinAt` | `g' = g X` holds within the closed interval at every point, including its endpoints. |
| `stateTrajectory_frame_hasDerivAt` | The same equation holds as an ordinary derivative at every point of `(0,T)`. |
| `stateTrajectory_frame_contDiffOn` | Every entry of `g` is `C¹` on `[0,T]`. |
| `stateTrajectory_state_ae_hasDerivAt` | The actual control equation for `X'` holds almost everywhere on `(0,T)`. |
| `stateTrajectory_stateCurvature_nonneg` | All three matrix state curvatures are nonnegative almost everywhere on `(0,T)`. |
| `stateTrajectory_contactCurvature_nonneg` | All six curves `t ↦ g(t) s_j*` have nonnegative signed curvature almost everywhere on `(0,T)`. |
| `stateTrajectory_regularity` | The preceding conclusions are packaged together for the extension construction. |

The endpoint derivative theorem is stated within `[0,T]`. An arbitrary state
trajectory places no constraints on its original functions outside that
interval. The source does not use an ordinary derivative at an endpoint until
a separate extension has been constructed.

## Uniformly bounding the state velocity

The state right-hand side is

\[
F(u,X)=P(u,X)X-XP(u,X),\qquad
P(u,X)=\frac{Z_u}{\operatorname{tr}(Z_uX)}.
\]

The integral equations first imply continuity of `g` and `X` on `[0,T]`, via
the existing matrix FTC library. The control itself need not be continuous.

The control simplex is compact: it is the intersection of the compact
coordinate box `[0,1]³` and the closed affine equation
`u₀ + u₁ + u₂ = 1`. For a continuous star-state curve `X`, consider the compact
product

\[
[0,T]\times\{u\in[0,1]^3:u_0+u_1+u_2=1\}.
\]

Upstream Lemma 3.3.4 gives

\[
\operatorname{tr}(Z_uX(t))<0
\]

at every point of that product. Therefore reciprocal division is continuous
there. The commutator `F(u,X(t))` is jointly continuous in `(t,u)`, and each of
its four scalar entries has a finite uniform bound on the compact product.
This proves `controlCommutator_bounded`.

The bound applies to **every** simplex value at time `t`, so substituting the
actual measurable control `u(t)` preserves it without requiring any
regularity of that selection.

## From bounded integrals to Lipschitz regularity

For a scalar entry of an integral curve, the defining equation and additivity
of the interval integral give

\[
f(y)-f(x)=\int_x^y v(t)\,dt.
\]

If `|v(t)| ≤ C` on `[0,T]`, the integral norm estimate gives

\[
|f(y)-f(x)|\leq C|y-x|\qquad(x,y\in[0,T]).
\]

The helper `integralCurve_lipschitz_of_bounded` proves this directly for each
matrix entry. It works for unordered endpoints by restricting integrability
to the unordered subinterval. No derivative assumption, and no assumption
that an exceptional set is countable, enters this step.

Applying it to the uniformly bounded state commutator gives entrywise
Lipschitz regularity of `X` on the whole closed interval.

## The classical frame equation and endpoint derivatives

Continuity of `g` and `X` makes the product `gX` continuous. The ordinary first
fundamental theorem of calculus therefore turns the frame integral equation
into

\[
g'=gX.
\]

It holds at every interior point, and as a derivative within the interval at
both endpoints. Each entry has a continuous derivative within `[0,T]`.
The interval has unique derivatives within it because `T > 0`; the
`contDiffOn_one_iff_derivWithin` characterization then yields the asserted
`C¹` regularity on the closed interval.

This is the exact regularity needed for gluing adjacent rotated copies. The
future cyclic extension can compare the right endpoint derivative of one
piece with the left endpoint derivative of the next, using the frame and
state terminal identities.

## Actual a.e. dynamics and geometric curvature

The state equation's integrand need not be continuous. The Lebesgue
fundamental theorem of calculus gives its derivative almost everywhere:

\[
X'=F(u,X).
\]

`integralCurve_ae_hasDerivAt` proves this entry by entry and transfers the
derivative from the indefinite integral to the original state using their
local equality in the open interval.

For a star state and any simplex control, upstream `oct_stateCurvature_eq`
gives

\[
\kappa_j
=-2\,\operatorname{tr}(Z_uX)^{-1}u_j\geq0.
\]

The trace denominator is negative, and every simplex coordinate is
nonnegative. Substituting the actual derivative equation proves the three
state-curvature inequalities almost everywhere.

The three opposite roots give the remaining contacts: the quadratic
expression

\[
q(v)=\det\bigl(v,(X+X^{-1}X')v\bigr)
\]

satisfies `q(-v) = q(v)`. Thus nonnegativity at roots `0,2,4` implies it at all
six roots.

At an interior differentiability point of `X`, the contact curve
`γ_j(t)=g(t)s_j*` satisfies

\[
\gamma_j'=gXs_j^*,\qquad
\gamma_j''=g(X^2+X')s_j^*.
\]

Both state determinants equal one, so the normalized curvature identity
already proved in `ControlTrajectory.lean` yields

\[
\det(\gamma_j',\gamma_j'')
=q(s_j^*)\geq0.
\]

The proof uses an eventual equality of derivative functions in a neighborhood
contained in `(0,T)`. Consequently it never differentiates the unconstrained
original frame outside the interval. This local formulation is suitable for
transporting the curvature inequality to translated copies in a cyclic
extension.

## Remaining reverse-comparison work

These results remove the extra smoothness assumption from the analytic input
on the original trajectory interval. They do not yet construct a global
closed boundary. The next construction must glue the frame and state using
the admissible endpoint identities, prove global regularity across the seams,
and transport the a.e. curvature inequalities through its countably many
translations.

For cost below `π`, the winding estimate then has to establish a simple
one-turn boundary and the balanced geometric competitor. For cost at least
`π`, `ControlBounds.lean` supplies the octagon as the required competitor. Until that complete
reverse comparator is assembled, the forward realization of a geometric
minimizer is not an assertion of `IsReinhardtMinimizer`.
