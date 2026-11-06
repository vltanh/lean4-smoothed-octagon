# The continuous contact trace of an actual worst disk

This is G2b in the proof ledger. The input is an actual worst disk `K` in Reinhardt's
normal position. The output is a six-component continuous boundary curve with common
period, simple traversal, full boundary coverage, normalized contact determinants, and
the prescribed initial values. No boundary curve is assumed in the input.

**Source draft; Lean compilation and kernel validation have not been run.**

## Construction

Let `b(θ) = rein_bd K θ` be the radial boundary point at polar angle `θ`. The upstream
no-gap theorem `rein_mem_Θ` provides a least-area circumscribed hexagon whose midpoint
of edge zero is `b(θ)`. Choose such an indexed hexagon and call it `V(θ)`.

The indexed uniqueness theorem `rein_V_unique` implies that this choice is canonical.
Define

\[
\sigma_j(\theta)=\operatorname{midpoint}\bigl(V(\theta)_j,V(\theta)_{j+1}\bigr).
\]

Thus `σ₀ = b`. Every midpoint lies on the boundary by the upstream critical-hexagon
contact theorem. The upstream theorem `rein_continuous_V` proves continuity of the
chosen hexagon using compactness and uniqueness. Taking a midpoint is continuous, so
all six functions `σⱼ` are continuous.

## Normalized contact relations

For every `θ`, the central symmetry of `V(θ)` gives

\[
\sigma_j+\sigma_{j+2}+\sigma_{j+4}=0,
\qquad \sigma_{j+3}=-\sigma_j.
\]

All critical hexagons have the same least area. Since one is normalized, the upstream
`rein_det2_hexMidpoint_std` fixes every adjacent midpoint determinant:

\[
\det(\sigma_j,\sigma_{j+1})=\frac{\sqrt3}{2}.
\]

Together these three identities are precisely `IsMultiPoint`.

## Period and simple traversal

The radial boundary point satisfies `b(θ + 2π) = b(θ)`. Indexed uniqueness therefore
gives `V(θ + 2π) = V(θ)`, so every component has the same full period `2π`.

Suppose `σⱼ(θ) = σⱼ(ψ)`. The upstream uniqueness theorem `rein_unique`, applied at the
same midpoint index on both hexagons, identifies the entire indexed hexagons. Their
zeroth midpoints agree, so `b(θ) = b(ψ)`. By `rein_bd_inj`,

\[
\psi=\theta+2\pi n\quad\text{for some }n\in\mathbb Z.
\]

If `θ` and `ψ` both belong to `[a,a+2π)`, the half-open interval forces `n = 0`.
Consequently every component is injective on every such interval. The half-open
endpoint convention is necessary because the full-period endpoints agree.

## Exhaustive coverage

Fix a boundary point `x` and a component `j`. Choose a critical hexagon whose zeroth
midpoint is `x`, then shift its indices by `-j`; call the shifted hexagon `W`. Its
`j`-th midpoint is `x`.

The zeroth midpoint of `W` is another boundary point. The upstream polar coverage
theorem `rein_exists_bd_Ico` supplies an angle `ψ ∈ [a,a+2π)` whose radial boundary
point is that midpoint. Indexed uniqueness gives `W = V(ψ)`. Thus `σⱼ(ψ) = x`.

This proves that every component covers the entire boundary during every full period.
It proves more than the range identity on all of `ℝ` needed by the later regularity
lemmas.

## Initial values and remaining analytic step

In normal position there is a critical hexagon whose six midpoints are the sixth
roots of unity. Its zeroth midpoint `(1,0)` is the radial boundary point at angle zero.
Indexed uniqueness identifies this hexagon with `V(0)`. Therefore
`σⱼ(0) = sixthRoot j`, the predicate `IsCircleRepresentation`.

The construction proves continuity, not yet differentiability. G2c must deduce a
positive regular `C¹` parametrization of curve zero from uniqueness of the supporting
line. Then upstream Lemma 2.4.2 upgrades all six components. A common global arclength
change of parameter is still needed before applying the Lipschitz-derivative theorem.
The definition of `IsBalancedPair` requires a common full period; it does not require
the six component functions to be time translates by one sixth of that period.

## Source

All upstream declarations above are in
[Ch2/Reinhardt.lean at the pinned revision](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean).
The implementation is [BoundaryTrace.lean](../SmoothedOctagon/BoundaryTrace.lean).
