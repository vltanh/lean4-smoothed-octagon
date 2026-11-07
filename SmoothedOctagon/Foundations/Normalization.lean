module

public import SmoothedPolygons.Ch2.Boundary

/-!
# Affine normalization of an actual worst disk

This module supplies a geometric first step toward the balanced-curve reduction. It starts
with an actual `IsWorstDisk`, constructs an orientation-preserving linear image with a
critical hexagon in Reinhardt's normal position, and preserves greatest packing density.
The six standard contacts are edge midpoints, not a claim about the hexagon's vertices.

In normal position, every critical hexagon has contact determinant `√3 / 2` and area
`2 * √3`. Every boundary point belongs to a normalized contact multi-point. Selecting
these multi-points continuously and obtaining a balanced boundary curve remain separate
obligations; no curve regularity or admissible control trajectory is asserted here.

Status: source-level Lean draft; compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set SmoothedPolygons

/-- Normalize an actual worst disk with a prescribed boundary point as its first standard
contact. The map preserves orientation, worst-disk status, and greatest packing density. -/
theorem worstDisk_normalization_at {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d : ℝ),
      rein_PosLin e d ∧ e x = sixthRoot 0 ∧ IsWorstDisk (e '' K) ∧
      rein_Std (e '' K) ∧
      greatestPackingDensity (e '' K) = greatestPackingDensity K := by
  obtain ⟨v, hv, _, hv0⟩ := bdy_exists_hexagon hK hx
  obtain ⟨e, d, he, hme⟩ := rein_normalize hv
  have hK' : IsWorstDisk (e '' K) :=
    ch2_isWorstLatticeDisk_iff_isWorstDisk.mp
      (bdy_isWorstLatticeDisk_image e he.pos he.det
        (ch2_isWorstLatticeDisk_iff_isWorstDisk.mpr hK))
  refine ⟨e, d, he, ?_, hK', ?_, hK'.2.trans hK.2.symm⟩
  · rw [← hv0]
    exact hme 0
  · refine ⟨fun j ↦ e (v j), rein_isLeastAreaHexagon_comp he hv, ?_⟩
    intro j
    rw [rein_hexMidpoint_comp, hme]

/-- Every actual worst disk has a density-preserving representative in Reinhardt's normal
position. No normal-position hypothesis is imposed on the input disk. -/
theorem worstDisk_normalization {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d : ℝ),
      rein_PosLin e d ∧ IsWorstDisk (e '' K) ∧ rein_Std (e '' K) ∧
      greatestPackingDensity (e '' K) = greatestPackingDensity K := by
  obtain ⟨e, d, he, _, hK', hstd, hdensity⟩ :=
    worstDisk_normalization_at hK (rein_bd_mem_frontier hK.1 0)
  exact ⟨e, d, he, hK', hstd, hdensity⟩

/-- Reinhardt's normal position is inhabited by an actual worst disk. -/
theorem exists_normalized_worst_disk :
    ∃ K : Set (Fin 2 → ℝ), IsWorstDisk K ∧ rein_Std K := by
  obtain ⟨K, hK⟩ := rein_exists_worst
  obtain ⟨e, d, he, hK', hstd, hdensity⟩ :=
    worstDisk_normalization (ch2_isWorstLatticeDisk_iff_isWorstDisk.mp hK)
  exact ⟨e '' K, hK', hstd⟩

/-- Normalizing one critical hexagon fixes the contact determinant of every critical
hexagon; its edge midpoints therefore form a multi-point in the upstream normalization. -/
theorem normalized_leastAreaHexagon_isMultiPoint {K : Set (Fin 2 → ℝ)}
    (hstd : rein_Std K) {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) :
    IsMultiPoint (hexMidpoint v) := by
  intro j
  refine ⟨?_, bdy_hexMidpoint_add_three hv.1 j,
    rein_det2_hexMidpoint_std hstd hv j⟩
  rw [← bdy_hexMidpoint_succ hv.1 j,
    show j + 4 = (j + 1) + 3 by ring,
    bdy_hexMidpoint_add_three hv.1, add_neg_cancel]

/-- Every least-area circumscribed hexagon of a disk in normal position has area `2√3`. -/
theorem normalized_leastAreaHexagon_area {K : Set (Fin 2 → ℝ)}
    (hstd : rein_Std K) {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) :
    volume.real (hexagonOf v) = 2 * √3 := by
  obtain ⟨w, hw, hwm⟩ := hstd
  exact (rein_least_volume_eq hv hw).trans (rein_volume_std hw.1 hwm)

/-- In Reinhardt's normal position, greatest packing density is area divided by `2√3`.
The equality concerns packings by congruent copies, using the upstream equality with
lattice packing density for centrally symmetric convex disks. -/
theorem normalized_density_eq_area {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hstd : rein_Std K) :
    greatestPackingDensity K = volume.real K / (2 * √3) := by
  obtain ⟨v, hv, hvm⟩ := hstd
  rw [theorem2_1_3 hK, rein_glpd_eq hK hv, rein_volume_std hv.1 hvm]

/-- Every boundary point of a normalized worst disk extends to a six-point boundary
contact configuration with the required determinant. This is pointwise existence;
continuity of a choice as the boundary point varies is not part of the statement. -/
theorem normalized_worstDisk_boundary_contacts {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) (hstd : rein_Std K) {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ∃ s : ZMod 6 → Fin 2 → ℝ, IsMultiPoint s ∧
      (∀ j, s j ∈ frontier K) ∧ s 0 = x := by
  obtain ⟨v, hv, hvK, hv0⟩ := bdy_exists_hexagon hK hx
  exact ⟨hexMidpoint v, normalized_leastAreaHexagon_isMultiPoint hstd hv, hvK, hv0⟩

end SmoothedOctagon
