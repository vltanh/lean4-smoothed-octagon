# Normalization of an actual worst disk

This is a concrete first step toward global gate G2, the reduction from an arbitrary
worst centrally symmetric convex disk to the normalized balanced-curve problem.
`SmoothedOctagon/Normalization.lean` constructs a normalized representative of an actual
worst disk and proves the contact and density identities needed by the next step.

**Validation: not run.** These are source-level Lean proofs with a hand-reviewed argument.
No Lean compilation, Lake command, kernel check, or CI was run. No new axiom, `sorry`, or
`admit` is introduced in this module. Its results reuse the pinned upstream theorems;
this statement does not assert an axiom audit or kernel verification of that dependency.

## Exact construction

Let `K` satisfy the upstream predicate `IsWorstDisk K`, and choose any
`x ∈ frontier K`. The construction produces an invertible continuous linear map `e`
and a positive real area factor `d` such that

\[
\det(eu,ev)=d\det(u,v),\qquad e(x)=s_0^*=(1,0).
\]

The image `e '' K` is still a worst disk and has the same greatest packing density as
`K`. It has a least-area circumscribed hexagon whose six edge midpoints are

\[
s_j^*=\bigl(\cos(\pi j/3),\sin(\pi j/3)\bigr),\quad j\in\mathbb Z/6\mathbb Z.
\]

These midpoints are boundary contacts. The assertion makes the contact configuration
regular; it does not assert that the circumscribed hexagon's vertices form a regular
hexagon. The map can change area: `d` is positive, with no requirement that `d = 1`.
The input disks are centrally symmetric about the origin, so a linear map suffices
for this affine normalization.

The proof uses the following steps, with no optimality or normal-position assumption
added to the given worst disk.

1. `bdy_exists_hexagon` supplies a least-area circumscribed hexagon `v` with
   `hexMidpoint v 0 = x` and all six edge midpoints on the boundary.
2. `rein_normalize` gives `e`, `d`, and the six midpoint equations.
3. `rein_isLeastAreaHexagon_comp` transports the least-area property to `e '' K`.
4. `bdy_isWorstLatticeDisk_image`, together with
   `ch2_isWorstLatticeDisk_iff_isWorstDisk`, preserves worst-disk status. Both disks
   therefore have greatest packing density `minimaxDensity`, proving the stated
   equality of their densities.

`worstDisk_normalization` chooses the upstream polar boundary point at angle zero.
`exists_normalized_worst_disk` then applies this construction to the existing theorem
that an actual worst disk exists. Thus the normalized class is nonempty.

## Contact determinant and the area objective

Normalizing one least-area circumscribed hexagon fixes the area of every such hexagon.
For each critical hexagon `v`, with edge midpoints `m_j`, the module proves

\[
m_j+m_{j+2}+m_{j+4}=0,\qquad m_{j+3}=-m_j,
\qquad \det(m_j,m_{j+1})=\frac{\sqrt3}{2}.
\]

The sum and central-symmetry identities follow from the centrally symmetric vertex
sequence. The determinant equality is the upstream normal-position lemma
`rein_det2_hexMidpoint_std`. Together they give `IsMultiPoint (hexMidpoint v)`.
The least-area hexagon has area

\[
\operatorname{area}(H_K)=4\det(m_0,m_1)=2\sqrt3.
\]

The module also proves the normalized density identity

\[
\operatorname{greatestPackingDensity}(K)
 =\frac{\operatorname{area}(K)}{2\sqrt3}.
\]

Here `greatestPackingDensity` is the upstream quantity for packings by congruent copies.
The proof first invokes the upstream equality with greatest lattice packing density
for centrally symmetric convex disks (`theorem2_1_3`), then its critical-hexagon area
formula (`rein_glpd_eq`). It does not assume general affine invariance of congruent-copy
packings for arbitrary bodies.

Finally, `normalized_worstDisk_boundary_contacts` proves that **each** boundary point
of a normalized actual worst disk extends to a six-contact multi-point lying on that
same boundary. This pointwise existence result supplies the contact data needed for
subsequent curve construction.

## What remains in G2

A balanced boundary curve requires a coherent choice of these contacts as the first
contact traverses the boundary, with the required continuity, regularity, orientation,
periodicity, injectivity, tangent conditions, and curvature conditions. This module
supplies the normalized disk and pointwise contact configurations. It does not claim
that those configurations already form such a curve, that there is an admissible
control trajectory, or that any octagon lower bound has been established.

In particular, reducing the disk-density objective to normalized area leaves the
mathematical task of bounding that area. Neither the Reinhardt conjecture nor affine
uniqueness is proved here.

## Declaration inventory

| Declaration | Result |
| --- | --- |
| `worstDisk_normalization_at` | Normalizes an actual worst disk at a chosen boundary point and preserves its density. |
| `worstDisk_normalization` | Removes the need to supply the boundary point. |
| `exists_normalized_worst_disk` | Gives an actual worst disk in normal position. |
| `normalized_leastAreaHexagon_isMultiPoint` | Gives the normalized multi-point identities for every critical hexagon. |
| `normalized_leastAreaHexagon_area` | Gives critical-hexagon area `2 * √3`. |
| `normalized_density_eq_area` | Expresses normalized greatest packing density as area divided by `2 * √3`. |
| `normalized_worstDisk_boundary_contacts` | Extends each boundary point to a normalized six-contact configuration. |

## Pinned source references

The implementation uses `vltanh/lean4-smoothed-polygon` at commit
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`, matching the package configuration.

- [Boundary.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean):
  `bdy_exists_hexagon`, `bdy_isWorstLatticeDisk_image`, and the midpoint identities.
- [Reinhardt.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean):
  `rein_normalize`, `rein_PosLin`, `rein_Std`, `rein_isLeastAreaHexagon_comp`,
  `rein_det2_hexMidpoint_std`, `rein_least_volume_eq`, `rein_volume_std`, `rein_glpd_eq`,
  `rein_bd_mem_frontier`, and `rein_exists_worst`.
- [Density.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Density.lean):
  `IsWorstDisk`, `theorem2_1_3`, and `ch2_isWorstLatticeDisk_iff_isWorstDisk`.
