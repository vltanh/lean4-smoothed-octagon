# An entirely circular trajectory cannot minimize the control cost

[`SmoothedOctagon/CircleExclusion.lean`](../SmoothedOctagon/CircleExclusion.lean)
proves a bounded exclusion result for the actual integral control problem:

\[
\operatorname{IsReinhardtMinimizer}(T,u,g,X)
\quad\Longrightarrow\quad
\exists t\in(0,T),\ X(t)\ne J.
\]

Here

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}
\]

is the normalized circle state. The theorem excludes a trajectory that stays
at this state for its **entire open interval**. It does not exclude a circular
state on a proper subinterval and does not establish a global classification
of singular arcs.

**Validation: not run.** The Lean file contains proof bodies and has been
reviewed as source. Lean compilation, Lake commands, kernel validation, and
CI have not been run. It introduces no axiom, `sorry`, or `admit`.

## Exact scope and declarations

The main result starts from the upstream `IsReinhardtMinimizer` predicate.
Its admissibility component uses a measurable simplex-valued control and
integral equations on `[0,T]`. There is no added smoothness assumption on the
control and no condition on the original curves outside this interval.

The exclusion is obtained from a stronger statement about all admissible
trajectories:

\[
\bigl[\forall t\in(0,T),\ X(t)=J\bigr]
\quad\Longrightarrow\quad
\operatorname{reinhardtCost}(T,X)\ge\pi.
\]

| Declaration | Conclusion |
|---|---|
| `reinhardtCost_eq_three_mul_of_circle` | Equality to `J` on `(0,T)` gives cost `3*T`, for `0 ≤ T`. |
| `reflectedFirstRow_angularSpeed_eq_one` | A smooth determinant-one frame has reflected-row angular speed `1` at a time where its star state is `J`. |
| `reflectedFirstRow_angle_eq_terminalTime_of_circle` | For the explicit global smooth-frame interface, equality to `J` on `(0,T)` gives lifted angle `T`. |
| `lowCost_admissible_not_circle` | An actual admissible trajectory of cost below `π` cannot have state `J` everywhere on `(0,T)`. |
| `admissible_circle_cost_ge_pi` | Every actual entirely circular admissible trajectory has cost at least `π`. |
| `controlMinimizer_cost_lt_pi` | Every full control minimizer has cost strictly below `π`. |
| `controlMinimizer_not_circle` | The state of a full control minimizer cannot equal `J` throughout `(0,T)`. |
| `controlMinimizer_exists_non_circle_state` | A full control minimizer has an interior time at which its state differs from `J`. |

The two smooth-frame lemmas are analytic helpers. The final admissible and
minimizer results construct their required global regularity from the
integral input through `CyclicExtension`.

## Hand proof

### 1. The cost of a circular state

The cost convention in the pinned upstream source is

\[
C(T,X)=-\frac32\int_0^T\operatorname{tr}(JX(t))\,dt.
\]

If `X(t)=J` for `0<t<T`, then `J²=-I`, so the trace in the integrand is `-2`.
Consequently

\[
C(T,X)=-\frac32(-2T)=3T.
\]

The hypothesis need not mention `t=0` or `t=T`. Changing an integrand at the
two endpoints does not change its integral. The Lean proof uses the exact
pinned mathlib lemma `intervalIntegral.integral_congr_Ioo_of_le`, which
accepts equality on the open interval directly. This cost identity itself
does not require admissibility.

### 2. Unit angular speed

Suppose first that a global smooth frame `G` has determinant `1` and satisfies
`G′=GY`. Write its reflected first row as

\[
z(t)=\bigl(G_{00}(t),-G_{01}(t)\bigr).
\]

The determinant condition implies `z(t)≠0`. At a time where `Y(t)=J`, the
matrix equation gives

\[
z'(t)=\bigl(-z_1(t),z_0(t)\bigr).
\]

Thus

\[
\theta'(t)
=\frac{\det(z(t),z'(t))}{z_0(t)^2+z_1(t)^2}
=1.
\]

In the source proof this calculation is expressed through the already
defined `starRowQuadratic` and the upstream logarithmic derivative
`sc_logDeriv`. Its denominator is nonzero because the reflected row is
nonzero. The angle `sc_angle` is a continuous lift obtained by integrating
the logarithmic derivative, with `sc_angle z 0=0`; it is not a principal
argument. Integrating the unit speed on `(0,T)` therefore gives

\[
\theta(T)=T.
\]

Again, the open-interval integral congruence avoids an endpoint hypothesis.

### 3. An admissible circular trajectory cannot have low cost

Take an actual `IsReinhardtAdmissible T u g X` trajectory, suppose it is
circular on `(0,T)`, and suppose for a contradiction that its cost is below
`π`.

`exists_cyclic_extension_of_isReinhardtAdmissible` constructs global curves
`G,Y` with the smoothness used above. They agree with `g,X` on the closed
interval, preserve the cost, and satisfy

\[
G(0)=I,\qquad G(T)=R,\qquad G'=GY,
\]

with star states everywhere. Hence `Y(t)=J` on `(0,T)`, and Step 2 gives
`θ(T)=T`.

The existing `lowCost_reflectedFirstRow_angle` theorem uses the endpoint
rotation and the strict cost bound to remove possible extra turns. It gives

\[
\theta(T)=\frac\pi3.
\]

It follows that `T=π/3`. Step 1 then gives `C(T,X)=π`, contradicting the
strict cost bound. Taking the contrapositive proves that every admissible
trajectory circular throughout `(0,T)` has cost at least `π`. The argument
does not assume that a contact curve is simple and does not assume a
rotation formula for the original frame outside its prescribed interval.

### 4. Apply minimality

`exists_worstDisk_lowCost_realization` already constructs an actual
admissible competitor with cost below `π`, using a normalized geometric
worst disk and the concrete octagon upper bound. Full control minimality
compares against that competitor, so every full control minimizer also has
cost below `π`.

Step 3 now rules out `X(t)=J` for every `t∈(0,T)`. Classical negation gives
the stated interior time where `X(t)≠J`.

## Relationship to singular arcs

This module makes no assumption about costates or the existence of a
Pontryagin lift. A separate result that forces `X=J` when the reduced costate
vanishes on an interval can use this exclusion when that interval is the
whole `(0,T)`. For a proper subinterval, the present proof gives no
contradiction: neither the full endpoint rotation nor the full trajectory
cost is determined by that subarc alone.

## Sources and pins

- Upstream definitions of `J`, the cost, admissibility, and minimization:
  [`SmoothedPolygons/Defs.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
- Upstream logarithmic angle and its derivative identity:
  [`Basic/Analysis/Convex/StarCurve.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurve.lean).
- The pinned terminal-time proof discusses the circular competitor and the
  strict octagon comparison, but does not provide the whole-interval
  exclusion proved here:
  [`SmoothedPolygons/Ch4/TerminalTime.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch4/TerminalTime.lean).
- Open-interval integral congruence at the resolved mathlib commit:
  [`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean).
- Local prerequisites:
  [`CyclicExtension.lean`](../SmoothedOctagon/CyclicExtension.lean),
  [`LowCostWinding.lean`](../SmoothedOctagon/LowCostWinding.lean), and
  [`ControlBounds.lean`](../SmoothedOctagon/ControlBounds.lean), available
  through the imported `ReverseComparison` module.
