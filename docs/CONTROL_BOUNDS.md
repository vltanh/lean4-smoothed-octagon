# Cost bounds and the remaining reverse comparison

`SmoothedOctagon/ControlBounds.lean` proves bounds that apply directly to the
upstream integral-form trajectory definition. It also identifies precisely
where reverse reconstruction is still required. All named comparison and
lower-bound propositions in this file remain open unless explicitly supplied
as hypotheses.

**Compilation, typechecking, Lake, and kernel validation have not been run.**
The Lean source has proof bodies and the arguments below; this is not a claim
of kernel verification.

## A lower bound for every actual state trajectory

Write a star state as

\[
X=\begin{pmatrix}a&b\\c&-a\end{pmatrix}.
\]

The star inequalities and determinant condition give

\[
-a^2-bc=1,\qquad c-b>0.
\]

The elementary identity

\[
(c-b)^2-4=(b+c)^2+4a^2\geq0
\]

therefore implies `c-b ≥ 2`. Since `traceForm J X = b-c`,

\[
-\frac32\operatorname{tr}(JX)\geq3.
\]

This is `star_costDensity_ge_three`. The argument uses the existing strict
trace sign but does not assume half-plane coordinates or optimality.

For an arbitrary `IsStateTrajectory T u g X`, the integral state equation
implies continuity of `X` on `[0,T]`. Its trace cost density is consequently
integrable. Integrating the pointwise bound gives

\[
\boxed{3T\leq\operatorname{cost}(T,X).}
\]

This is `stateTrajectory_cost_ge_three_mul`. As `T > 0`, the cost is positive.
If the cost is below `π`, then automatically

\[
T<\pi/3.
\]

The proof applies to a measurable control with integral state equations. It
does not require a smooth control, a global extension, or a minimizing
trajectory. The integration step follows the existing terminal-time argument
in upstream `Ch4/TerminalTime.lean`, with its global-minimizer assumption
removed from the lower-cost estimate.

## The actual worst-disk realization is already below the threshold

The concrete octagon's existing area theorem and explicit control formula give

\[
\operatorname{area}(K_{\rm oct})
=\frac{\sqrt{12}\,(8-\sqrt{32}-\log 2)}{\sqrt8-1}<\pi.
\]

`octagon_area_lt_pi` connects that strict inequality to this project's actual
`octagon` set. The geometric volume is converted from `ENNReal.ofReal` only
after nonnegativity of the existing exact cost has been supplied.

Let `K` be an actual worst disk with the balanced circle realization already
constructed. Its balanced-area minimality compares it with the concrete
octagon, giving

\[
\operatorname{cost}(T,X)=\operatorname{area}(K)
\leq\operatorname{area}(K_{\rm oct})<\pi.
\]

The finite-measure hypotheses needed to convert the area comparison to real
numbers follow from compactness of the disks. Combining this with the lower
cost bound gives the terminal-time bound for the constructed realization.
`exists_worstDisk_lowCost_realization` supplies an actual witness with all
these conclusions and the original density identity

\[
\delta(K)=\operatorname{cost}(T,X)/\sqrt{12}.
\]

This conclusion uses geometric minimality. It is available before proving
that the trajectory minimizes over all admissible controls, so it does not
assume the very comparison the reverse construction is intended to justify.

## Why the reverse comparison only needs low costs

`AdmissibleBalancedComparison` is the explicit remaining obligation:

> For every upstream admissible control trajectory, construct a balanced disk
> in circle representation with area at most the trajectory's cost.

The statement permits a different competitor. Extra-winding trajectories need
not themselves trace a simple boundary with area equal to their cost.

If a trajectory has cost at least `π`, the concrete octagon already supplies
the required competitor, because its area is strictly less than `π`.
`highCost_balanced_competitor` proves this case without even needing
admissibility as a hypothesis.

`LowCostBalancedComparison` restricts the reconstruction obligation to
admissible trajectories whose cost is below `π`. The preceding high-cost
competitor proves the exact equivalence

```lean
AdmissibleBalancedComparison ↔ LowCostBalancedComparison
```

The equivalence discharges the high-cost case. It does not construct the
low-cost competitor. The latter requires the interval regularity, cyclic
extension, winding, and convexity arguments tracked separately in the ledger.

## Conditional control minimality and the global lower bound

`controlMinimizer_of_worstDisk_realization` keeps
`AdmissibleBalancedComparison` as an explicit hypothesis. Under that
hypothesis, a competitor control produces a balanced disk `K'`; geometric
minimality gives

\[
\operatorname{cost}(T,X)=\operatorname{area}(K)
\leq\operatorname{area}(K')
\leq\operatorname{cost}(T',X').
\]

This is exactly the unrestricted comparison required by
`IsReinhardtMinimizer`. No theorem asserts that predicate without supplying
the reverse comparison.

The second named open proposition, `LowCostControlLowerBound`, asks for

\[
\operatorname{area}(K_{\rm oct})\leq\operatorname{cost}(T,X)
\]

for every admissible trajectory with cost below `π`. It has no finite
switching-word or polygon-family restriction. A proof of this inequality
already implies the original Reinhardt minimality conjecture through the
constructed actual worst-disk realization. This sufficient direction does
not need the reverse comparison.

With `LowCostBalancedComparison` supplied, the converse follows as well:
geometric global minimality bounds the reconstructed competitor's area,
which in turn bounds the trajectory's cost. Thus the source proves the
conditional equivalence

```lean
LowCostBalancedComparison →
  (ReinhardtConjecture ↔ LowCostControlLowerBound)
```

Neither this global inequality nor affine equality classification is proved
by the cost and terminal-time bounds.

## Sources

The polygon source is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- `SmoothedPolygons/Ch4/TerminalTime.lean`: the strict trace sign and the
  original integral lower-cost argument.
- `SmoothedPolygons/Ch7/SmoothedPolygon.lean`:
  `example7_5_smoothedOctagon`, including its exact cost and strict `π` bound.
- `SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean`:
  `smoothedPolygon_isStateTrajectory`, `smoothedPolygonDisk_volume`, and
  `oct_octagon_value_nonneg`.
- `Basic/Analysis/Calculus/MatrixFTC.lean`: continuity from the integral equations.
- This project's `BalancedReduction.lean`, `BalancedTargets.lean`, and
  `AdmissibleRealization.lean`: constructed geometric minimality and exact
  area-cost witnesses.

The underlying mathlib revision is
`9d581dfff2e41de989072ea63abf3daf69311520`.
