# Continuous normalized supporting covectors

`SmoothedOctagon/SupportNormal.lean` constructs a continuous supporting covector along
the radial boundary of every actual worst disk. This supplies the missing geometric
input for proving that the radial boundary is continuously differentiable. No smooth
boundary parametrization is assumed in this module.

**Validation: not run.** The implementation has been reviewed against the pinned source,
but Lean compilation, Lake, kernel validation, and CI have not been run.

## Main result

For an actual worst disk `K`, `exists_continuous_radial_support` gives a function
`n : ℝ → (Fin 2 → ℝ)` such that:

- `n` is continuous;
- `planeDot (n θ) (rein_bd K θ) = 1` for every angle `θ`;
- `planeDot (n θ) y ≤ 1` for every `y ∈ K`;
- `planeDot (n θ) y ≤ gauge K y` for every vector `y`.

Here

\[
\operatorname{planeDot}(n,x)=n_0x_0+n_1x_1.
\]

The covector is normalized by its value at the boundary contact. It need not have
Euclidean norm one. The pairing is written in coordinates, so the result does not
depend on an inner-product instance for the function space, whose default norm is
the sup norm.

The more general theorem `exists_continuous_radial_support_of_unique_support` starts
with a centrally symmetric convex disk and the explicit condition that every boundary
point lies on exactly one support line. The worst-disk theorem obtains this condition
from upstream Lemma 2.2.5.

## Construction and proof

### Existence and uniqueness at a contact

The upstream theorem `irr_exists_normal` supplies a covector whose value at the
boundary point is one and whose values on the disk are at most one. Its proof uses
separation and the fact that the origin lies in the interior of the disk; normalization
does not divide by an unchecked quantity.

If two such covectors support at the same boundary point, their level-one lines are
support lines through that point. The no-corners condition makes those lines equal.
The upstream algebraic lemma `irr_eq_of_line_eq` then makes the covectors equal.
Thus uniqueness is proved from uniqueness of support lines, rather than assumed as
a stronger property of a chosen normal field.

### A uniform compact box

Choose `r > 0` with the sup-norm ball of radius `r` about zero contained in `K`, and
put `a = r / 2`. The coordinate test vectors `a e_i` and `-a e_i` lie in the disk.
Every covector satisfying the supporting inequalities therefore obeys

\[
a n_i\le 1,\qquad -a n_i\le 1,
\qquad |n_i|\le a^{-1}.
\]

All supporting covectors lie in the same compact box
`[-a⁻¹, a⁻¹] × [-a⁻¹, a⁻¹]`. This bound depends only on the disk, not on the angle
or the chosen boundary curve.

### Continuity without differentiability

For any continuous boundary curve `τ`, consider a field `n` that satisfies the
normalized support conditions at `τ t`. At a fixed time `t₀`, every cluster point
`w` of this field satisfies the limiting contact equality

\[
\operatorname{planeDot}(w,\tau(t_0))=1
\]

and all the limiting support inequalities

\[
\operatorname{planeDot}(w,y)\le1\quad(y\in K).
\]

The proof makes both limit passages explicit. A failed contact equality gives an
open neighborhood of `(t₀, w)` disjoint from the graph of the support field. A failed
support inequality gives an open neighborhood of `w` that the field never enters.
Either would contradict the cluster-point property.

Pointwise uniqueness forces every cluster point to equal `n t₀`. Compactness then
implies convergence to this value. This proves `continuous_normalizedSupport`; the
radial specialization uses the already proved continuity of `rein_bd`.

### Domination of the gauge

For a nonzero vector `y`, the gauge is strictly positive and
`(gauge K y)⁻¹ • y` is a boundary point. Applying the supporting inequality there and
multiplying by the positive gauge gives

\[
\operatorname{planeDot}(n,y)\le\operatorname{gauge}_K(y).
\]

The zero vector is handled separately. No denominator is left implicit.

## Exported interfaces

| Declaration | Role |
| --- | --- |
| `planeDot` and its linearity lemmas | Coordinate pairing and elementary algebra. |
| `IsNormalizedSupport` | Level-one contact equality and supporting inequalities. |
| `exists_normalizedSupport` | Pointwise construction at any boundary contact. |
| `normalizedSupport_unique` | Pointwise uniqueness from the no-corners condition. |
| `existsUnique_normalizedSupport` | Combined existence and uniqueness. |
| `exists_support_coordinate_bound` | A single bound for all supporting covectors. |
| `continuous_normalizedSupport` | Continuity along any continuous boundary curve. |
| `normalizedSupport_le_gauge` | Domination of the gauge on the whole plane. |
| `radialSupport` and `radialSupport_spec` | The chosen field along `rein_bd`. |
| `radialSupport_continuous` | Continuity under the explicit no-corners condition. |
| `radialSupport_periodic` | The chosen field has period `2π`. |
| `exists_continuous_radial_support_of_unique_support` | General constructed radial field. |
| `exists_continuous_radial_support` | Specialization to an actual worst disk. |

## Sources and proof boundary

The geometry dependency is pinned at
[`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`](https://github.com/vltanh/lean4-smoothed-polygon/tree/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f).
The relevant upstream declarations are in
[`SmoothedPolygons/Ch2/Irreducible.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Irreducible.lean)
(`irr_exists_normal`, `irr_eq_of_line_eq`) and
[`SmoothedPolygons/Ch2/Reinhardt.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean)
(`lemma2_2_5`, `rein_isSupportLine_of`, and the radial gauge lemmas).

The compactness argument follows the same general limit-and-uniqueness pattern as
upstream `bdy_continuous_tangent`, but proves continuity of supporting covectors
without that theorem's smooth-boundary hypothesis. It uses
`IsCompact.tendsto_nhds_of_unique_mapClusterPt` from pinned
[`Mathlib/Topology/Compactness/Compact.lean`](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Compactness/Compact.lean).

This module introduces no axioms, proof holes, or assumed regular parametrization.
The radial derivative, arclength change of parameter, and balanced-curve assembly
are subsequent steps. Global minimality and affine uniqueness remain separate
research obligations.
