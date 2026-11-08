module

public import SmoothedPolygons.Ch2.Density
public import SmoothedPolygons.Ch2.Reinhardt
public import SmoothedPolygons.Ch2.BalancedDensity
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# The global Reinhardt target

This module connects the concrete smoothed octagon to the packing problem already defined in
`SmoothedPolygons`. The dependency is pinned in the package configuration. The candidate, its
admissibility, its exact density, and the existence of a worst disk come from that dependency.

`ReinhardtConjecture` asserts global minimality among all centrally symmetric convex disks,
using the greatest density of packings by congruent copies. `AffineRigidity` records the separate
uniqueness assertion. They are proved in `LowerBound` (`reinhardtConjecture`) and
`Equality/Transport` (`worstDisk_eq_linear_image`). The theorems below give equivalent forms of
the lower bound and prove the candidate's upper bound on the minimax density.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real SmoothedPolygons

/-- The concrete smoothed octagon in the upstream circle representation (`k = 1`). -/
noncomputable def octagon : Set (Fin 2 → ℝ) := smoothedPolygonDisk 1

/-- Reinhardt's candidate density, in the exact normalization used upstream. -/
noncomputable def octagonDensity : ℝ :=
  (8 - √32 - Real.log 2) / (√8 - 1)

/-- The minimality assertion: the smoothed octagon has least greatest packing density among
all centrally symmetric convex disks. This definition asserts no uniqueness. -/
def ReinhardtConjecture : Prop := IsWorstDisk octagon

/-- The separate rigidity assertion: every worst disk is an invertible linear image of the
smoothed octagon. Since `IsCCSDisk` centers disks at the origin, linear images express affine
equivalence after centering. -/
def AffineRigidity : Prop :=
  ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K →
    ∃ A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ), K = A '' octagon

/-- The two mathematical targets together: global minimality and uniqueness up to affine
equivalence. -/
def FullReinhardtConjecture : Prop := ReinhardtConjecture ∧ AffineRigidity

/-- The concrete candidate satisfies all conditions of an upstream balanced pair. -/
theorem octagon_isBalancedPair :
    IsBalancedPair octagon (smoothedPolygonCurve 1) (tf 1) :=
  (smoothedPolygonDisk_isBalancedPair 1 le_rfl).1

/-- In particular, the concrete candidate belongs to the full comparison class. -/
theorem octagon_isCCSDisk : IsCCSDisk octagon :=
  octagon_isBalancedPair.1

/-- The density is inherited from the geometric area theorem and the balanced-disk density
formula; it is not assigned to the candidate by definition. -/
theorem octagon_density : greatestPackingDensity octagon = octagonDensity := by
  rw [greatestPackingDensity_of_isBalancedPair octagon_isBalancedPair,
    MeasureTheory.measureReal_def]
  exact smoothedOctagon_volume.2

/-- Global minimality is exactly the universal density lower bound. The quantified disks are
arbitrary centrally symmetric convex disks, not just members of a polygon family. -/
theorem reinhardtConjecture_iff_density_lower_bound :
    ReinhardtConjecture ↔
      ∀ K : Set (Fin 2 → ℝ), IsCCSDisk K →
        octagonDensity ≤ greatestPackingDensity K := by
  constructor
  · intro h K hK
    change IsWorstDisk octagon at h
    have hbound := (ch2_isWorstDisk_iff.mp h).2 K hK
    rwa [octagon_density] at hbound
  · intro h
    change IsWorstDisk octagon
    apply ch2_isWorstDisk_iff.mpr
    refine ⟨octagon_isCCSDisk, ?_⟩
    intro K hK
    rw [octagon_density]
    exact h K hK

/-- The same conjecture in terms of the minimax value. -/
theorem reinhardtConjecture_iff_minimax :
    ReinhardtConjecture ↔ minimaxDensity = octagonDensity := by
  constructor
  · intro h
    change IsWorstDisk octagon at h
    exact h.2.symm.trans octagon_density
  · intro h
    change IsWorstDisk octagon
    exact ⟨octagon_isCCSDisk, octagon_density.trans h.symm⟩

/-- The candidate gives the upper-bound half of the desired minimax equality. -/
theorem minimaxDensity_le_octagonDensity : minimaxDensity ≤ octagonDensity := by
  unfold minimaxDensity
  refine csInf_le ?_ ⟨octagon, octagon_isCCSDisk, octagon_density⟩
  refine ⟨0, ?_⟩
  rintro d ⟨K, _hK, rfl⟩
  exact ch2_greatestPackingDensity_nonneg K

/-- The worst-disk comparison below is nonvacuous: the upstream existence theorem supplies a
global minimizer, and Fejes Tóth's theorem identifies the lattice and congruent-copy problems. -/
theorem exists_worst_disk : ∃ K : Set (Fin 2 → ℝ), IsWorstDisk K := by
  obtain ⟨K, hK⟩ := rein_exists_worst
  exact ⟨K, ch2_isWorstLatticeDisk_iff_isWorstDisk.mp hK⟩

/-- It suffices to prove the candidate lower bound for any actual worst disk. Both geometric
optimality and the inequality are explicit hypotheses; no classification theorem is assumed. -/
theorem reinhardtConjecture_of_worst_disk
    {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K)
    (hbound : octagonDensity ≤ greatestPackingDensity K) : ReinhardtConjecture := by
  apply reinhardtConjecture_iff_minimax.mpr
  rw [hK.2] at hbound
  exact le_antisymm minimaxDensity_le_octagonDensity hbound

/-- One can focus the lower-bound task on global minimizers without losing equivalence to the
original conjecture. Existence of a worst disk is used in the reverse implication. -/
theorem reinhardtConjecture_iff_worst_disk_lower_bound :
    ReinhardtConjecture ↔
      ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K →
        octagonDensity ≤ greatestPackingDensity K := by
  constructor
  · intro h K hK
    exact reinhardtConjecture_iff_density_lower_bound.mp h K hK.1
  · intro h
    obtain ⟨K, hK⟩ := exists_worst_disk
    exact reinhardtConjecture_of_worst_disk hK (h K hK)

end SmoothedOctagon
