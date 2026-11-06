# Low cost excludes extra winding for smooth star trajectories

This module addresses a specific part of G3d's reverse-comparison problem. The endpoint
condition `g(T)=R` records a matrix, so it determines a rotation only modulo full turns.
Reconstructing a simple balanced boundary requires controlling those extra turns.

`LowCostWinding.lean` proves such a bound for a **global smooth star arc**. Its hypotheses
are explicit: each entry of `g` is `C¹`, `det g=1`, `X` is continuous, `g′=gX`, and `X`
is a star state. For `T>0`, `g(0)=I`, `g(T)=R`, and cost less than `π`, the reflected
first row has lifted angle exactly `π/3` at the endpoint, and `g₀₀(t)>0` throughout
`[0,T]`.

**Source draft. Lean compilation, typechecking, kernel validation, and CI have not been
run.** The theorem is not yet stated for every `IsReinhardtAdmissible` trajectory. The
passage from an arbitrary integral-admissible segment to the smooth-arc interface, and
the full reconstruction of a balanced disk, remain open ledger items.

## A continuous angle without assuming a simple path

For any nonvanishing `C¹` curve `γ`, regard it as a complex curve `z` and define

\[
L(t)=\int_0^t\frac{z'(s)}{z(s)}\,ds,
\qquad \theta(t)=\operatorname{Im}L(t).
\]

The quotient is continuous. Differentiating `z(t) exp(-L(t))` gives zero, so

\[
z(t)=z(0)\exp(L(t)).
\]

Thus `θ` is an actual continuous angle lift. It is not the principal argument, which
would forget full turns. Neither periodicity nor injectivity is needed for this
construction. The source adapts the corresponding logarithmic-integral proof from
the pinned upstream `PlaneCurve.StarCurve` development, removing those unused hypotheses.

Its derivative is

\[
\theta'(t)=\frac{\det(\gamma(t),\gamma'(t))}{|\gamma(t)|^2}.
\]

## The reflected row and its quadratic form

Write a star state as

\[
X=\begin{pmatrix}a&b\\c&-a\end{pmatrix},
\qquad -a^2-bc=1.
\]

The star inequalities imply `c>0`. Define

\[
Q_X(z_0,z_1)=-b z_0^2-2a z_0z_1+c z_1^2.
\]

Completing the square gives the exact identity

\[
c Q_X(z)=(c z_1-a z_0)^2+z_0^2.
\]

If `z₀` is nonzero, this is strictly positive. If `z₀=0` and `z` is nonzero, then
`Q_X(z)=c z₁²>0`. Hence the form is positive definite. Rotating a vector by a right
angle also shows

\[
(c-b)(z_0^2+z_1^2)-Q_X(z)=Q_X(-z_1,z_0)\ge0.
\]

Now set

\[
\gamma(t)=(g_{00}(t),-g_{01}(t)).
\]

This is the reflected first row; the reflection fixes the orientation sign for the
right matrix equation `g′=gX`. The determinant-one condition prevents this row from
vanishing. Directly differentiating its two coordinates gives

\[
\det(\gamma,\gamma')=Q_X(\gamma).
\]

Consequently its angle satisfies

\[
0<\theta'(t)\le c(t)-b(t)=-\operatorname{tr}(JX(t)).
\]

The positivity is established without assuming any winding count or simple boundary.

## Integrating the cost bound

The Reinhardt cost is

\[
\mathcal C(T,X)=-\frac32\int_0^T\operatorname{tr}(JX(t))\,dt.
\]

Integrating the pointwise angular inequality yields the exported bound

\[
\boxed{\frac32\theta(T)\le\mathcal C(T,X).}
\]

This is `reflectedFirstRow_angle_le_cost`. All integrands are continuous under the
stated smooth-arc hypotheses; the source uses the ordinary fundamental theorem of
calculus and interval-integral monotonicity.

## Identifying the endpoint turn

At `g(0)=I`, the reflected row is `(1,0)`, so its initial lifted angle is zero.
At `g(T)=R`, it is `(1/2,√3/2)`. Exponential reconstruction therefore gives

\[
\theta(T)=\frac\pi3+2\pi n\quad(n\in\mathbb Z).
\]

Its strictly positive angular speed and `T>0` imply `θ(T)>0`, excluding negative
integers `n`. If the cost is below `π`, the integrated bound gives
`θ(T)<2π/3`, excluding every positive integer `n`. Thus `n=0` and

\[
\boxed{\theta(T)=\frac\pi3.}
\]

Strict monotonicity places every intermediate angle in `[0,π/3]`. The real part of
`exp(L(t))` is `exp(Re L(t)) cos θ(t)`, and both factors are positive on this interval.
Hence `g₀₀(t)>0` for every `t∈[0,T]`.

## What this closes and what it does not

The source proves the reflected-row winding and positive-coordinate-chart statements
for the stated smooth star arcs. These are useful ingredients for the low-cost reverse
geometry construction. They do not yet prove that every admissible integral trajectory
has such a global extension, that all six boundary arcs form a simple convex balanced
disk, or that its area is at most the trajectory's cost.

Those remaining constructions must precede an assertion that the geometric minimizer
is a minimizer over the entire control-admissible class. The high-cost competitors also
need an explicit geometric comparison, such as the unit disk, with all required facts
supplied. No such reverse theorem is assumed here.

## Sources

The implementation is [LowCostWinding.lean](../SmoothedOctagon/LowCostWinding.lean).
The logarithmic-integral construction is adapted from pinned
[StarCurve.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurve.lean).
The star state, endpoint matrix, and cost definitions are in pinned
[Defs.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
