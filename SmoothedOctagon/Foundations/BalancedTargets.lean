module

public import SmoothedOctagon.Foundations.Problem
public import SmoothedOctagon.Foundations.BalancedReduction

/-!
# Exact remaining targets in the balanced problem

The completed source construction of a balanced representative of an actual worst disk
allows both global targets to be transferred without an assumed reduction theorem.
Global minimality becomes an area inequality over all balanced circle competitors;
affine rigidity becomes a classification of all balanced circle minimizers.

The propositions below remain open. The equivalences identify the remaining work, rather
than discharge the area inequality or the equality classification. No finite polygon or
switching-word restriction is imposed. Compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Set SmoothedPolygons

/-- The explicit global area inequality remaining after the balanced reduction. -/
def BalancedAreaLowerBound : Prop :=
  ∀ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ),
    IsBalancedPair K σ tf → IsCircleRepresentation σ → volume octagon ≤ volume K

/-- The equality classification in the balanced problem. It quantifies over every
balanced circle minimizer, with no polygon-family restriction. -/
def BalancedAffineRigidity : Prop :=
  ∀ K : Set (Fin 2 → ℝ), IsBalancedCircleMinimizer K →
    ∃ A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ), K = A '' octagon

/-- The concrete octagon starts at the six standard contact points. -/
theorem octagon_isCircleRepresentation :
    IsCircleRepresentation (smoothedPolygonCurve 1) :=
  (smoothedPolygonDisk_isBalancedPair 1 le_rfl).2

/-- The original geometric conjecture is equivalent to the concrete octagon minimizing
the balanced area problem. The reverse direction uses the constructed global minimizer. -/
theorem reinhardtConjecture_iff_balancedCircleMinimizer :
    ReinhardtConjecture ↔ IsBalancedCircleMinimizer octagon := by
  constructor
  · intro h
    exact isBalancedCircleMinimizer_of_isWorstDisk h
      octagon_isBalancedPair octagon_isCircleRepresentation
  · intro h
    exact balancedCircleMinimizer_isWorstDisk h

/-- An exact reformulation of global minimality as the universal balanced area bound.
The class remains all balanced disks in circle representation. -/
theorem reinhardtConjecture_iff_balancedAreaLowerBound :
    ReinhardtConjecture ↔ BalancedAreaLowerBound := by
  rw [reinhardtConjecture_iff_balancedCircleMinimizer]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨⟨smoothedPolygonCurve 1, tf 1,
      octagon_isBalancedPair, octagon_isCircleRepresentation⟩, h⟩

/-- It also suffices to prove the area bound only for genuine balanced circle minimizers.
Existence and their relation to global packing minimizers are proved in `BalancedReduction`. -/
theorem reinhardtConjecture_iff_balancedMinimizer_area_lower_bound :
    ReinhardtConjecture ↔
      ∀ K : Set (Fin 2 → ℝ), IsBalancedCircleMinimizer K →
        volume octagon ≤ volume K := by
  constructor
  · intro h K hK
    obtain ⟨σ, tf, hbal, hcirc⟩ := hK.1
    exact reinhardtConjecture_iff_balancedAreaLowerBound.mp h K σ tf hbal hcirc
  · intro h
    obtain ⟨K, hK, hmin⟩ := exists_balancedCircle_worst_disk
    obtain ⟨σ, tf, hbal, hcirc⟩ := hmin.1
    have harea : volume.real octagon ≤ volume.real K :=
      ENNReal.toReal_mono hK.1.2.1.measure_lt_top.ne (h K hmin)
    apply reinhardtConjecture_of_worst_disk hK
    rw [← octagon_density,
      greatestPackingDensity_of_isBalancedPair octagon_isBalancedPair,
      greatestPackingDensity_of_isBalancedPair hbal]
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < Real.sqrt 12)).mpr harea

/-- Affine rigidity transfers in both directions. Pulling a balanced classification back
through the constructed normalization gives the classification of every actual worst disk. -/
theorem affineRigidity_iff_balancedAffineRigidity :
    AffineRigidity ↔ BalancedAffineRigidity := by
  constructor
  · intro h K hK
    exact h K (balancedCircleMinimizer_isWorstDisk hK)
  · intro h K hK
    obtain ⟨e, d, he, hK', hmin, hdensity⟩ := worstDisk_balanced_normalization hK
    obtain ⟨A, hA⟩ := h (e '' K) hmin
    refine ⟨A.trans e.symm.toLinearEquiv, ?_⟩
    calc
      K = e.symm '' (e '' K) := (rein_image_symm_image (e := e) K).symm
      _ = e.symm '' (A '' octagon) := by rw [hA]
      _ = (A.trans e.symm.toLinearEquiv) '' octagon := by
        rw [image_image]
        rfl

/-- Both remaining global targets, with their exact unrestricted balanced comparison
classes. Neither conjunct is established by this equivalence. -/
theorem fullReinhardtConjecture_iff_balancedTargets :
    FullReinhardtConjecture ↔ BalancedAreaLowerBound ∧ BalancedAffineRigidity := by
  exact and_congr reinhardtConjecture_iff_balancedAreaLowerBound
    affineRigidity_iff_balancedAffineRigidity

end SmoothedOctagon
