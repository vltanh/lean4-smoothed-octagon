# Cubic margins for normalized strong lifts

The new scalar estimate is transported to the actual upstream switching functions in
[`StrongSwitching.lean`](../SmoothedOctagon/StrongSwitching.lean). This is a source-level Lean
draft with a hand proof below. Compilation and kernel validation have **not been run**.

## Exact scope and statements

Assume `1 / √3 < y₀ < 1`, let `τ = switchTime y₀`, and let `0 ≤ t ≤ τ`. For the explicit
strong lift, whose cost multiplier is `λ_cost = -1`, the estimates are

\[
\chi_{32}(t)\ge\frac{\sqrt3}{2}t^3,
\qquad
\chi_{31}(t)\ge\frac{\sqrt3}{2}(\tau-t)^3.
\]

The theorem `normalizedStrongLift_switching_cubic_lower_bounds` gives the same pair of
estimates for every upstream `IsStrongLift y₀ Λ₁ ΛR (-1)`, using uniqueness of that normalized
lift. The indices in Lean are `switchingFn 2 1` and `switchingFn 2 0`, respectively.

## Hand proof of the transport

Set

\[
y=1+3y_0^2,\qquad W=e^{\sqrt3y_0t},\qquad r=yW.
\]

The upstream lemmas `hmax_y_mem` and `hmax_W_mem` give
`2 < y < 4`, `1 ≤ W`, and `yW ≤ 4`. Hence `W < 2` and `2 ≤ y ≤ r ≤ 4`.
By `chi32_eq`,

\[
\chi_{32}(t)=\frac{2f(y,yW)}{3y^2W y_0^3(2-W)}.
\]

The denominator is strictly positive. The scalar theorem
`hmaxF_uniform_cubic_lower_bound` gives

\[
8f(y,yW)\ge (yW-y)^3=y^3(W-1)^3.
\]

Furthermore,

\[
W(2-W)=1-(W-1)^2\le1,\qquad
W-1\ge\sqrt3y_0t,\qquad 2y^2\le y^3.
\]

All quantities multiplied in these comparisons are nonnegative. Writing
`D = 3y²W y₀³(2-W)`, the complete comparison is

\[
\begin{aligned}
4\left(\frac{\sqrt3}{2}t^3\right)D
&=6\sqrt3\,y^2y_0^3t^3\,W(2-W)\\
&\le6\sqrt3\,y^2y_0^3t^3\\
&\le3\sqrt3\,y^3y_0^3t^3\\
&\le y^3(W-1)^3\\
&\le8f(y,yW).
\end{aligned}
\]

Division by `4D > 0` proves the first estimate. The upstream identity
`chi31_eq_chi32` applies it at time `τ-t` to prove the second. Finally,
`strongLift_unique` identifies every normalized strong lift with the explicit one on the
segment, so the bounds transfer without changing their constants.

## What the estimate does not establish

The result gives a quantitative gap away from the prescribed switches in these strong lifts.
It strengthens an upstream sign result already known for this family. The hypotheses do not
cover arbitrary Pontryagin extremals, arbitrary smoothed polygons, or all centrally symmetric
convex disks. No global density comparison, bound on the number of switches, or classification
of minimizers follows from this estimate alone. A differently scaled costate lift also needs
the corresponding scaling factor in its bound.
